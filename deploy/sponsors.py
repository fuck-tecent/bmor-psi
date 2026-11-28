"""Moderated organization logos. All identities come from the Zhihu OAuth session."""
import hashlib
import hmac
import io
import re
import sqlite3
import time
from collections import OrderedDict
from contextlib import closing
from email import policy
from email.parser import BytesParser
from html import escape
from threading import Lock
from urllib.parse import urlsplit

from PIL import Image, UnidentifiedImageError

DESK = "/auth/zhihu/sponsors"
STYLE = "/sponsor-settings.css"
SCRIPT = "/sponsor-upload.js"
PUBLIC = "/sponsors/logo/"
DISPLAY_ORDER = "display_position IS NULL, display_position, id"
ORIGIN = "https://www.goldbach.tech"
FILE_LIMIT = 4 * 1024 * 1024
LIMIT = FILE_LIMIT + 16 * 1024


def setup(db):
    db.executescript("""
        CREATE TABLE IF NOT EXISTS site_admins(subject TEXT PRIMARY KEY, slot TEXT UNIQUE);
        CREATE TABLE IF NOT EXISTS sponsor_logos(
            id INTEGER PRIMARY KEY, owner TEXT NOT NULL, name TEXT NOT NULL, png BLOB,
            state TEXT NOT NULL DEFAULT 'pending', submitted INTEGER NOT NULL,
            reviewer TEXT, reviewed INTEGER, website TEXT NOT NULL DEFAULT '');
        CREATE INDEX IF NOT EXISTS sponsor_state ON sponsor_logos(state,id);
        CREATE INDEX IF NOT EXISTS sponsor_owner ON sponsor_logos(owner,submitted);
    """)
    with db:
        db.execute("BEGIN IMMEDIATE")
        columns = {row[1] for row in db.execute("PRAGMA table_info(sponsor_logos)")}
        if "website" not in columns:
            db.execute("ALTER TABLE sponsor_logos ADD COLUMN website TEXT NOT NULL DEFAULT ''")
        if "display_position" not in columns:
            db.execute("ALTER TABLE sponsor_logos ADD COLUMN display_position INTEGER")


def bootstrap(db, profile, registered_profile, uid=None):
    match = profile["subject"] == uid if uid else registered_profile and profile["profile_url"] == registered_profile
    if match:
        db.execute("INSERT OR IGNORE INTO site_admins VALUES (?, 'initial')", (profile["subject"],))


def upload_fields(content_type, raw):
    msg = BytesParser(policy=policy.default).parsebytes(
        b"Content-Type: " + content_type.encode("ascii") + b"\r\n\r\n" + raw)
    fields = {}
    if msg.defects or not msg.is_multipart():
        raise ValueError("invalid multipart form")
    for part in msg.iter_parts():
        key = part.get_param("name", header="content-disposition")
        if (key not in ("name", "csrf", "logo", "website") or key in fields or part.is_multipart()
                or part.defects or part.get_content_disposition() != "form-data"):
            raise ValueError("invalid form")
        value = part.get_payload(decode=True)
        fields[key] = value if key == "logo" else value.decode("utf-8")
    if not {"name", "csrf", "logo"} <= fields.keys():
        raise ValueError("incomplete form")
    return fields


def website_url(value):
    value = value.strip()
    if not value:
        return ""
    if len(value) > 2048 or any(c.isspace() or ord(c) < 32 or ord(c) == 127 or c == "\\" for c in value):
        raise ValueError("invalid website")
    parts = urlsplit(value)
    if (parts.scheme not in ("http", "https") or not parts.hostname
            or parts.username is not None or parts.port == 0):
        raise ValueError("invalid website")
    host = parts.hostname.rstrip(".").encode("idna").decode("ascii")
    label = r"[a-z0-9](?:[a-z0-9-]{0,61}[a-z0-9])?"
    tld = host.rsplit(".", 1)[-1]
    if (not re.fullmatch(rf"(?:{label}\.)+{label}", host, re.IGNORECASE)
            or not tld[0].isalpha() or re.fullmatch(r"0x[0-9a-f]*", tld, re.IGNORECASE)):
        raise ValueError("invalid website host")
    return value


def website_link(url, label):
    return f'<a href="{escape(url)}" target="_blank" rel="noopener noreferrer ugc nofollow">{label}</a>'


class InvalidLogo(ValueError):
    pass


def logo_png(raw):
    if not isinstance(raw, bytes) or len(raw) > FILE_LIMIT:
        raise ValueError("image size")
    with Image.open(io.BytesIO(raw), formats=("PNG", "JPEG", "WEBP")) as im:
        if max(im.size) > 4096 or im.width * im.height > 8_000_000:
            raise InvalidLogo("dimensions")
        if getattr(im, "n_frames", 1) != 1:
            raise InvalidLogo("animated")
        im.thumbnail((480, 240))
        clean = im.convert("RGBA")
        clean.info.clear()
        out = io.BytesIO()
        clean.save(out, format="PNG", optimize=True)
        return out.getvalue()


_PUBLIC_LOGO_CACHE = OrderedDict()
_PUBLIC_LOGO_LOCK = Lock()
_PUBLIC_LOGO_LIMIT = 256


def render_public_logo(raw, *, webp=False, hd=False):
    high_res = bool(hd or len(raw) <= 20_480)
    key = (hashlib.sha256(raw).digest(), bool(webp), high_res)
    with _PUBLIC_LOGO_LOCK:
        cached = _PUBLIC_LOGO_CACHE.get(key)
        if cached is not None:
            _PUBLIC_LOGO_CACHE.move_to_end(key)
            return cached
    with Image.open(io.BytesIO(raw)) as im:
        im = im.convert("RGBA")
        if not high_res:
            im.thumbnail((280, 140), Image.Resampling.LANCZOS)
        im.info.clear()
        out = io.BytesIO()
        if webp:
            if high_res:
                im.save(out, format="WEBP", lossless=True, quality=100, method=6)
            else:
                im.save(out, format="WEBP", quality=82, method=6)
            result = (out.getvalue(), "image/webp")
        else:
            im.save(out, format="PNG", optimize=True)
            result = (out.getvalue(), "image/png")
    with _PUBLIC_LOGO_LOCK:
        _PUBLIC_LOGO_CACHE[key] = result
        _PUBLIC_LOGO_CACHE.move_to_end(key)
        while len(_PUBLIC_LOGO_CACHE) > _PUBLIC_LOGO_LIMIT:
            _PUBLIC_LOGO_CACHE.popitem(last=False)
    return result


INITIATOR_URL = "https://www.zhihu.com/people/cg-22-2"
INITIATOR_AVATAR_FALLBACK = "https://avatars.githubusercontent.com/u/103875245?v=4&s=64"
ZHIHU_SCIENCE_URL = "https://www.zhihu.com/org/zhi-hu-ke-xue"
AI_WORKS_URL = "https://www.zhihu.com/project/detail/210995"
ZHIHU_DISCUSS_URL = "https://www.zhihu.com/question/2108591052059665116"


def coinitiator_lockup(path, lang, prefix):
    zh = lang == "zh"
    logo_id = None
    co_url = ZHIHU_SCIENCE_URL
    avatar_url = INITIATOR_AVATAR_FALLBACK
    if path:
        try:
            with closing(sqlite3.connect(path)) as db:
                row = db.execute(
                    f"SELECT id, website FROM sponsor_logos WHERE state='approved' AND name='知乎科学' "
                    f"ORDER BY {DISPLAY_ORDER} LIMIT 1"
                ).fetchone()
                if row:
                    logo_id, website = row
                    if website:
                        co_url = website
                if db.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='links'").fetchone():
                    linked = db.execute(
                        "SELECT avatar_url FROM links WHERE (profile_url=? OR lower(handle)='cgandgameenginelearner') "
                        "AND avatar_url != '' LIMIT 1",
                        (INITIATOR_URL,),
                    ).fetchone()
                    if linked and linked[0]:
                        avatar_url = linked[0]
        except sqlite3.Error:
            pass
    co_name = "知乎科学" if zh else "Zhihu Science"
    initiator_role = "发起人" if zh else "Initiator"
    co_role = "联合发起：" if zh else "Co-initiator:"
    co_content = (
        f'<img class="coinitiator-logo" src="{prefix}sponsors/logo/{logo_id}.png" alt="{co_name}" loading="eager">'
        if logo_id is not None else f'<strong>{co_name}</strong>'
    )
    return (
        f'<div class="colophon-credits">'
        f'<span class="colophon-party"><span class="colophon-role">{initiator_role}</span>'
        f'<a class="colophon-person" href="{INITIATOR_URL}" target="_blank" rel="noopener noreferrer">'
        f'<span class="author-avatar" aria-hidden="true">L<img src="{escape(avatar_url)}" alt="" loading="eager" referrerpolicy="no-referrer"></span>'
        f'<strong>@lifesize</strong></a></span>'
        f'<span class="colophon-sep" aria-hidden="true"></span>'
        f'<span class="colophon-party colophon-party-co"><span class="colophon-role">{co_role}</span>'
        f'<a class="colophon-org" href="{escape(co_url)}" target="_blank" rel="noopener noreferrer ugc nofollow">'
        f'{co_content}</a></span>'
        f'</div>'
    )


def author_colophon(path, lang, prefix, *, goldbach=True):
    return f'<div class="hero-colophon">{coinitiator_lockup(path, lang, prefix)}</div>'


def hero_origin_note(lang, *, goldbach=True):
    if not goldbach:
        return ""
    if lang == "zh":
        return (
            '<div class="hero-origin">'
            '<p>由 @lifesize 发起 · 知乎科学联合推动，知乎答主 lifesize 在知乎 AI4S 讨论社群「知乎 研 Club」中发起本次活动。</p>'
            f'<p>知乎科学持续支持研究者连接、公开讨论与阶段成果传播。'
            f'<a href="{AI_WORKS_URL}" target="_blank" rel="noopener noreferrer">知乎 AI Works 入口 <span aria-hidden="true">↗</span></a></p>'
            '</div>'
        )
    return (
        '<div class="hero-origin">'
        '<p>Initiated by @lifesize and co-promoted with Zhihu Science; Zhihu creator lifesize launched this effort in the Zhihu AI4S community “Zhihu Yan Club”.</p>'
        f'<p>Zhihu Science supports connecting researchers, open discussion, and sharing milestones. '
        f'<a href="{AI_WORKS_URL}" target="_blank" rel="noopener noreferrer">Zhihu AI Works <span aria-hidden="true">↗</span></a></p>'
        '</div>'
    )


def footer_credit(path, lang, prefix):
    return f'<div class="footer-credit-line">{coinitiator_lockup(path, lang, prefix)}</div>'


def wall(path, lang, prefix):
    with closing(sqlite3.connect(path)) as db:
        rows = db.execute(f"SELECT id,name,website FROM sponsor_logos WHERE state='approved' ORDER BY {DISPLAY_ORDER}").fetchall()
    cards = []
    for ident, name, website in rows:
        alt = escape(name) if website else ""
        image = (f'<img loading="lazy" decoding="async" '
                 f'src="{prefix}sponsors/logo/{ident}.png" alt="{alt}">')
        if website:
            image = website_link(website, image)
        cards.append(f'<figure>{image}<figcaption>{escape(name)}</figcaption></figure>')
    zh = lang == "zh"
    grid = f'<div class="sponsor-grid">{"".join(cards)}</div>' if cards else ""
    return (f'<section class="shell sponsor-wall" id="supporting-orgs"><div class="sponsor-heading"><h2>{"支持机构" if zh else "Supporting organizations"}</h2>'
            f'<a class="text-link" href="{ORIGIN}{DESK}?lang={lang}">'
            + ("申请成为支持机构" if zh else "Submit an organization logo") + f' ↗</a></div>{grid}</section>')


def public_logo(path, ident):
    record = public_logo_record(path, ident)
    return record[0] if record else None


def public_logo_record(path, ident):
    with closing(sqlite3.connect(path)) as db:
        row = db.execute("SELECT png, name FROM sponsor_logos WHERE id=? AND state='approved'", (ident,)).fetchone()
    return (row[0], row[1]) if row else None


def settings_page(status, lang, title, content):
    back = "返回研究台" if lang == "zh" else "Research desk"
    html = f"""<!doctype html><html lang="{lang}"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title} · {back}</title><link rel="stylesheet" href="{STYLE}"><script src="{SCRIPT}" defer></script>
<link rel="icon" href="/goldbach-icon.svg"></head><body>
<header><div class="shell masthead"><a href="/?lang={lang}">
<img src="/goldbach-icon.svg" width="40" height="40" alt=""><span>{back}</span></a></div></header>
<main class="shell"><h1>{title}</h1>{content}</main></body></html>"""
    return status, {"Content-Type": "text/html; charset=utf-8"}, html.encode()


def upload_error(lang, busy=False):
    zh = lang == "zh"
    title = ("上传繁忙" if zh else "Upload busy") if busy else ("Logo 文件过大" if zh else "Logo file is too large")
    hint = ("请稍后重试。" if zh else "Try again shortly.") if busy else (
        "请选择不超过 4 MiB 的 PNG、JPEG 或 WebP 图片。" if zh else "Choose a PNG, JPEG or WebP file up to 4 MiB.")
    return upload_notice(503 if busy else 413, lang, f"{title}。{hint}" if zh else f"{title}. {hint}")


def upload_notice(status, lang, text):
    title = "提交未完成" if lang == "zh" else "Submission incomplete"
    back = "返回投稿或登录" if lang == "zh" else "Return to submission or sign in"
    return settings_page(status, lang, title, f'<section class="card"><p role="alert">{text}</p>'
                         f'<a href="{DESK}?lang={lang}">{back}</a></section>')


def handle(method, path, params, headers, db, row, lang, redirect):
    def tr(zh, en):
        return en if lang == "en" else zh
    title = tr("赞助单位 Logo", "Sponsor logos")
    def msg(code, text):
        if path == DESK + "/upload":
            return upload_notice(code, lang, text)
        return settings_page(code, lang, title,
                             f'<section class="card"><p>{text}</p><a href="{DESK}?lang={lang}">{tr("返回设置","Back to settings")}</a></section>')
    uid = row["subject"]
    csrf = f'<input type="hidden" name="csrf" value="{row["csrf"]}">'
    if not uid:
        if method == "GET" and path == DESK:
            dest = "home" if params.get("entry")=="home" else "sponsors"
            return settings_page(200, lang, title, f'<section class="card signin"><p>{tr("使用知乎账号投稿或登录审核。","Sign in with Zhihu to submit or review logos.")}</p>'
                        f'<form action="/auth/zhihu/start" method="post">{csrf}<input type="hidden" name="next" value="{dest}">'
                        f'<button class="primary">{tr("使用知乎登录","Sign in with Zhihu")}</button></form></section>')
        return msg(403, tr("请先登录知乎。","Please sign in with Zhihu."))
    admin = db.execute("SELECT 1 FROM site_admins WHERE subject=?", (uid,)).fetchone()
    if method == "POST":
        if headers.get("Origin") != ORIGIN or not hmac.compare_digest(str(params.get("csrf","")).encode(),row["csrf"].encode()):
            return msg(403, tr("请刷新后重试。","Refresh and try again."))
        if path == DESK+"/logout":
            db.execute("DELETE FROM sessions WHERE sid=?", (row["sid"],))
            return redirect("/?lang="+lang)
        if path == DESK+"/upload":
            name = params.get("name","").strip()
            if not 1 <= len(name) <= 80:
                return msg(400, tr("单位名须为 1–80 字。","Use a name of 1–80 characters."))
            try:
                website = website_url(params.get("website", ""))
            except ValueError:
                return msg(400, tr("请输入以 https:// 或 http:// 开头、带域名的完整官网地址，或留空。",
                                   "Enter a full website URL starting with https:// or http://, or leave it blank."))
            if len(params.get("logo", b"")) > FILE_LIMIT:
                return upload_error(lang)
            try:
                png = logo_png(params.get("logo",b""))
            except Image.DecompressionBombError:
                return upload_notice(400, lang, tr("图片尺寸过大，请缩小后重试。", "The image dimensions are too large. Resize it and retry."))
            except InvalidLogo as error:
                message = (tr("请上传静态图片，动态图片不受支持。", "Choose a static image; animated images are unsupported.")
                           if str(error) == "animated" else
                           tr("图片最多 800 万像素，单边最多 4096 像素，请缩小后重试。", "Resize the image to at most 8 MP and 4096 pixels per side."))
                return upload_notice(400, lang, message)
            except (UnidentifiedImageError, OSError, ValueError, TypeError, SyntaxError):
                return upload_notice(400, lang, tr("图片无法读取，请重新导出为 PNG、JPEG 或 WebP 后重试。", "Export the image again as PNG, JPEG or WebP and retry."))
            now = int(time.time())
            db.execute("BEGIN IMMEDIATE")
            count = db.execute("SELECT count(*) FROM sponsor_logos WHERE owner=? AND (state='pending' OR submitted>?)",(uid,now-86400)).fetchone()[0]
            if count >= 3:
                return msg(429, tr("待审或近一天的投稿已达三份。","Limit of three pending or recent submissions reached."))
            db.execute("INSERT INTO sponsor_logos(owner,name,png,submitted,website) VALUES(?,?,?,?,?)",
                       (uid, name, png, now, website))
        elif path == DESK+"/review":
            if not admin:
                return msg(403, tr("需要管理员权限。","Administrator access required."))
            decision = params.get("decision")
            if decision not in ("approved","rejected","withdrawn"):
                return msg(400, tr("无效操作。","Invalid action."))
            expected = "approved" if decision == "withdrawn" else "pending"
            changed = db.execute("""UPDATE sponsor_logos SET state=?,reviewer=?,reviewed=?,
                png=CASE WHEN ?='approved' THEN png ELSE NULL END WHERE id=? AND state=?""",
                (decision,uid,int(time.time()),decision,params.get("id"),expected)).rowcount
            if not changed:
                return msg(409, tr("状态已变更，请刷新。","State changed. Refresh the page."))
        elif path == DESK + "/order":
            if not admin:
                return msg(403, tr("需要管理员权限。", "Administrator access required."))
            original = params.get("original", "").split(",")
            order = params.get("order", "").split(",")
            db.execute("BEGIN IMMEDIATE")
            current = [str(item[0]) for item in db.execute(
                f"SELECT id FROM sponsor_logos WHERE state='approved' ORDER BY {DISPLAY_ORDER}")]
            if original != current:
                return msg(409, tr("展示列表已变更，请返回「已展示」重新排序。", "The display list changed. Reorder it from the Approved tab."))
            if len(order) != len(current) or set(order) != set(current):
                return msg(400, tr("排序数据不完整，请返回列表重试。", "The order is incomplete. Return to the list and retry."))
            db.executemany("UPDATE sponsor_logos SET display_position=? WHERE id=?", enumerate(order))
            return redirect(DESK + "?view=approved")
        else:
            return msg(404, "404")
        return redirect(DESK)
    preview = re.fullmatch(DESK+r"/preview/([1-9][0-9]{0,15})",path)
    if preview:
        image = db.execute("SELECT png FROM sponsor_logos WHERE id=? AND (owner=? OR ?) AND png IS NOT NULL",
                           (preview[1],uid,bool(admin))).fetchone()
        return (200,{"Content-Type":"image/png"},image[0]) if image else msg(404,"404")
    if path != DESK:
        return msg(404, "404")
    upload = (f'<section class="card upload"><h2>{tr("提交单位 Logo","Submit a logo")}</h2>'
            f'<form id="logo-upload" data-max-bytes="{FILE_LIMIT}" method="post" action="{DESK}/upload?lang={lang}" enctype="multipart/form-data">{csrf}'
            f'<label>{tr("单位名称","Organization")} <input name="name" maxlength="80" required></label>'
            f'<label>{tr("官网地址（选填）","Official website (optional)")} '
            '<input name="website" type="url" maxlength="2048" placeholder="https://example.org"></label>'
            '<label>Logo <input type="file" name="logo" accept="image/png,image/jpeg,image/webp" required></label>'
            f'<p class="hint">{tr("PNG、JPEG 或 WebP，最大 4 MiB、800 万像素，单边最多 4096 像素。仅上传获授权的标识，审核通过后公开。","PNG, JPEG or WebP, up to 4 MiB, 8 MP and 4096 px per side. Submit authorized artwork for public display after review.")}</p>'
            f'<p class="upload-feedback" role="alert" hidden></p>'
            f'<button class="primary">{tr("提交审核","Submit for review")}</button></form></section>')
    labels = {"pending":tr("待审核","Pending"),"approved":tr("已展示","Approved"),"rejected":tr("已拒绝","Rejected"),"withdrawn":tr("已撤下","Withdrawn")}
    items = db.execute(f"""SELECT id,name,state,website FROM sponsor_logos WHERE owner=? OR ?
        ORDER BY (state='pending') DESC, CASE WHEN state='approved' THEN 0 ELSE 1 END, {DISPLAY_ORDER}""",
                       (uid,bool(admin))).fetchall()
    selected = params.get("view")
    filters = {"all": tr("全部","All"), **labels}
    if selected not in filters:
        selected = "all"
    counts = {key: 0 for key in labels}
    for _, _, state, _ in items:
        counts[state] += 1
    counts["all"] = len(items)
    tabs = "".join(f'<a href="{DESK}?view={key}"{(" aria-current=page" if selected == key else "")}>'
                   f'{label} <span>{counts[key]}</span></a>' for key, label in filters.items())
    heading = tr("管理员审核","Administrator review") if admin else tr("我的投稿","My submissions")
    queue = [f'<section class="card queue"><h2>{heading}</h2><nav class="filters" aria-label="{heading}">{tabs}</nav>']
    sorting = admin and selected == "approved" and counts["approved"] > 1
    if sorting:
        original = ",".join(str(ident) for ident, _, state, _ in items if state == "approved")
        queue.append(f'<form id="sponsor-order" method="post" action="{DESK}/order" hidden>{csrf}'
                     f'<input type="hidden" name="original" value="{original}">'
                     f'<input type="hidden" name="order" value="{original}">'
                     f'<p class="hint">{tr("拖动排序手柄，或用上移、下移按钮。","Drag the handle or use the move buttons.")}</p>'
                     f'<button class="primary" disabled>{tr("保存顺序","Save order")}</button></form>'
                     '<div id="sponsor-sort-list">')
    if not counts[selected]:
        queue.append(f'<p class="empty">{tr("暂无符合条件的投稿。","No submissions in this view.")}</p>')
    actions = {"approved":tr("通过","Approve"),"rejected":tr("拒绝","Reject"),"withdrawn":tr("撤下","Withdraw")}
    for i, name, state, website in items:
        if selected not in ("all", state):
            continue
        queue.append(f'<article class="submission" data-sponsor-id="{i}">' if sorting else '<article class="submission">')
        if sorting:
            queue.append(f'<div class="sort-controls" hidden><span class="drag-handle" draggable="true" aria-hidden="true">⠿</span>'
                         f'<button type="button" data-move="-1" aria-label="{tr("上移","Move up")} {escape(name)}">↑</button>'
                         f'<button type="button" data-move="1" aria-label="{tr("下移","Move down")} {escape(name)}">↓</button></div>')
        if state in ("pending","approved"):
            queue.append(f'<div class="preview"><img loading="lazy" src="{DESK}/preview/{i}" alt=""></div>')
        link = f'<p class="hint">{website_link(website, escape(website))}</p>' if website else ""
        queue.append(f'<div class="submission-info"><strong>{escape(name)}</strong>'
                     f'<span class="status {state}">{labels[state]}</span>{link}</div>')
        if admin and state in ("pending","approved"):
            buttons = ("approved","rejected") if state == "pending" else ("withdrawn",)
            queue.append(f'<form class="review" method="post" action="{DESK}/review">{csrf}'
                         f'<input type="hidden" name="id" value="{i}">')
            for value in buttons:
                style = "primary" if value == "approved" else "danger"
                queue.append(f'<button class="{style}" name="decision" value="{value}">{actions[value]}</button>')
            queue.append('</form>')
        queue.append('</article>')
    if sorting:
        queue.append('</div>')
    queue.append('</section>')
    account = (f'<section class="card account"><h2>{tr("知乎账号","Zhihu account")}</h2>'
               f'<p class="hint">UID {escape(row["subject"])}</p>'
               f'<a href="/auth/zhihu?lang={lang}">{tr("贡献榜署名","Leaderboard attribution")}</a>'
               f'<form method="post" action="{DESK}/logout">{csrf}<button>{tr("退出登录","Sign out")}</button></form></section>')
    return settings_page(200, lang, tr("设置","Settings"),
                         '<div class="layout">'+''.join(queue)+'<aside>'+upload+account+'</aside></div>')
