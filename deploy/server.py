import hashlib
import hmac
import ipaddress
import json
import gzip
import os
import re
import sqlite3
import ssl
import time
from collections import OrderedDict
from contextlib import closing
from datetime import datetime
from functools import lru_cache
from html import escape
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from threading import BoundedSemaphore, Lock
from urllib.parse import parse_qs, urlsplit

from desk import Desk, QUEUE_BATCH
from landau import BASELINE, exponent_record
from presence import SitePresence
from zhihu_oauth import BASE as ZHIHU_PATH, ZhihuOAuth
import sponsors

SPONSOR_UPLOAD_SLOT = BoundedSemaphore(1)

ROOT = Path(__file__).resolve().parent
SITE_REVISION_FILE = ROOT / ".site-revision"
SITE_REVISION = SITE_REVISION_FILE.read_text(encoding="ascii").strip() if SITE_REVISION_FILE.is_file() else None
CREDS = Path(os.environ["CREDENTIALS_DIRECTORY"])
SECRET = (CREDS / "webhook").read_bytes().strip()
DB = Path(os.environ["STATE_DIRECTORY"]) / "verdicts.sqlite3"
oauth_credential = CREDS / "zhihu-oauth"
ZHIHU = ZhihuOAuth(DB.with_name("contributor-links.sqlite3"), json.loads(oauth_credential.read_bytes())
                   if oauth_credential.is_file() else None)
LIVE_RELEASE = Path("/opt/goldbach-catalogues/current")
CATALOGUE_ROOT = LIVE_RELEASE.resolve(strict=True) if LIVE_RELEASE.is_symlink() else ROOT
RELEASE_SHA = (CATALOGUE_ROOT / "revision").read_text() if CATALOGUE_ROOT != ROOT else None
GOLDBACH_CATALOGUE = json.loads((CATALOGUE_ROOT / "gaps.json").read_text(encoding="utf-8"))
GAPS = GOLDBACH_CATALOGUE["gaps"]
DESK = Desk(DB, GAPS, SECRET)
PROBLEM_FILE = CATALOGUE_ROOT / "problems.json"
PROBLEMS = json.loads(PROBLEM_FILE.read_text(encoding="utf-8")) if PROBLEM_FILE.exists() else {}
PUBLIC_SITE = "https://www.movan.tech/goldbach/"
problem_ids = set(gap["id"] for gap in GAPS)
for slug, problem in PROBLEMS.items():
    if slug in {"goldbach", DB.stem} or not re.fullmatch(r"[a-z]+(?:-[a-z]+)*", slug):
        raise ValueError(f"Invalid problem slug: {slug}")
    for gap in problem["gaps"]:
        if gap["id"] in problem_ids or not gap["id"].startswith(f"L-{slug}-"):
            raise ValueError(f"Invalid or duplicate task: {gap['id']}")
        problem_ids.add(gap["id"])
DESKS = {"goldbach": DESK, **{
    slug: Desk(DB.with_name(slug + ".sqlite3"), problem["gaps"], SECRET)
    for slug, problem in PROBLEMS.items()
}}
GAP_DESKS = {
    gap_id: slug for slug, desk in DESKS.items() for gap_id in desk.gaps
}
PRESENCE = SitePresence(DESKS.values())
PAGE_VIEWS_DB = DB.with_name("page-views.sqlite3")
IP_KEY_PATH = DB.with_name("ip-count.key")
if not IP_KEY_PATH.exists():
    with os.fdopen(os.open(IP_KEY_PATH, os.O_CREAT | os.O_EXCL | os.O_WRONLY, 0o600), "wb") as key_file:
        key_file.write(os.urandom(32))
IP_KEY = IP_KEY_PATH.read_bytes()
if len(IP_KEY) != 32:
    raise ValueError("Invalid IP statistics key")
with closing(sqlite3.connect(PAGE_VIEWS_DB)) as conn, conn:
    conn.execute("CREATE TABLE IF NOT EXISTS visitor_ips (digest BLOB PRIMARY KEY) WITHOUT ROWID")
    conn.execute("CREATE TABLE IF NOT EXISTS page_views (source TEXT PRIMARY KEY, total INTEGER NOT NULL)")
    conn.execute("INSERT OR IGNORE INTO page_views VALUES ('live', 0)")

ASSETS = {
    "/agent-icons.png": "image/png",
    "/core-team-signup.png": "image/png",
    sponsors.STYLE: "text/css",
    sponsors.SCRIPT: "text/javascript",
    "/wechat.svg": "image/svg+xml",
    "/discussion-qr.png": "image/png",
    "/discussion.js": "text/javascript",
    "/presence.js": "text/javascript",
    "/goldbach-icon.svg": "image/svg+xml",
    "/site.css": "text/css",
    "/site.js": "text/javascript",
    "/join.txt": "text/plain",
    "/join-zh.txt": "text/plain",
}

@lru_cache(maxsize=16)
def compressed_asset(content):
    return gzip.compress(content, compresslevel=6, mtime=0)


DISCUSSION_EXPIRES = datetime.fromisoformat("2026-12-02T00:00:00+08:00")


def discussion_copy(lang):
    if time.time() >= DISCUSSION_EXPIRES.timestamp():
        return None
    zh = lang == "zh"
    cutoff = DISCUSSION_EXPIRES.date()
    return {
        "short": "扫码进群" if zh else "WeChat group",
        "label": "扫码进群 · 讨论进度" if zh else "Join WeChat group",
        "name": "知乎 AI4S 讨论组（哥猜 3 群）" if zh else "Zhihu AI4S Goldbach group 3",
        "instructions": "微信扫码，讨论研究进度" if zh else "Scan in WeChat to discuss progress",
        "validity": f"{cutoff.month} 月 {cutoff.day} 日前有效" if zh else f"Valid before {cutoff:%Y-%m-%d} (UTC+8)",
        "alt": "知乎 AI4S 讨论组（哥猜 3 群）微信群二维码" if zh else "WeChat QR code for the Zhihu AI4S Goldbach discussion group 3",
    }


def core_team_copy(lang):
    if lang == "zh":
        return {
            "title": "中心组报名",
            "short_desc": "数学研究者制定路线 · 开发者维护设施",
            "intro": "中心组由数学界专业人士和软件开发者组成。",
            "research": "数学专业研究者负责制定研究路线、拆解子命题证明任务，并动态调整证明路线。",
            "development": "软件开发者负责维护网站的基础设施。",
            "caption": "扫码报名中心组",
        }
    return {
        "title": "Join the core team",
        "short_desc": "Math researchers plan routes · developers maintain the site",
        "intro": "The core team brings together professional mathematics researchers and software developers.",
        "research": "Mathematics researchers set the research direction, break it into proof tasks, and adjust the roadmap as results come in.",
        "development": "Software developers maintain the website infrastructure.",
        "caption": "Scan to apply",
    }


def presence_widget(lang, prefix, *, variant="inline"):
    zh = lang == "zh"
    visitors = "在线访客" if zh else "Visitors"
    agents = "在研 Agent" if zh else "Agents"
    views = "累计浏览" if zh else "Views"
    ips = "独立 IP" if zh else "Unique IPs"
    heading = "研究台实时统计" if zh else "Live desk stats"
    detail = ("累计浏览量统计首页、问题目录和研究页的成功访问，刷新也计一次。近 90 秒内浏览可见页面的浏览器，同一域名多标签合计一次。"
              "累计独立 IP 包含历史日志中可确认的页面访问，两个域名下同一来源 IP 合计一次。"
              "在研 Agent 按尚未提交且有效的任务租约计，每份一席。每 30 秒刷新。" if zh else
              "Page views count successful loads of the home, directory and research pages, including reloads. "
              "Online visitors have a visible page in the last 90 seconds. Tabs on the same domain count once. "
              "Unique IPs include historical page visits matched to access logs. Each source IP counts once across both domains. "
              "Each active, unsubmitted research lease counts as one agent seat. Updates every 30 seconds.")
    title_html = f'<strong class="presence-heading">{heading}</strong>' if variant == "footer" else ""
    return (
        f'<details class="presence-widget presence-{variant}" data-endpoint="{prefix}api/presence" hidden>'
        f'<summary>{title_html}<span class="presence-items">'
        f'<span><i aria-hidden="true"></i>{visitors} <b data-count="visitors">—</b></span>'
        f'<span>{agents} <b data-count="agents">—</b></span>'
        f'<span>{views} <b data-count="page_views">—</b></span>'
        f'<span>{ips} <b data-count="unique_ips">—</b></span>'
        f'</span></summary><p>{detail}</p></details>'
    )


def hero_community_card(lang, prefix):
    zh = lang == "zh"
    disc = discussion_copy(lang)
    core = core_team_copy(lang)
    items = []
    if disc:
        items.append(
            f'<details class="community-item" id="wechat-discussion" open aria-label="{disc["name"]}">'
            f'<summary class="community-summary"><img class="wechat-mark" src="{prefix}wechat.svg" width="22" height="22" alt="">'
            f'<span>{disc["short"]}</span><i aria-hidden="true"></i></summary>'
            f'<div class="community-item-body"><div class="community-copy">'
            f'<strong class="community-title"><img class="wechat-mark" src="{prefix}wechat.svg" width="22" height="22" alt="">{disc["label"]}</strong>'
            f'<p>{disc["name"]}</p><small>{disc["validity"]}</small></div>'
            f'<div class="community-qr discussion-code"><img loading="lazy" src="{prefix}discussion-qr.png" alt="{disc["alt"]}" width="800" height="1198"></div>'
            f'</div></details>'
        )
    items.append(
        f'<details class="community-item" id="core-team" open aria-label="{core["title"]}">'
        f'<summary class="community-summary"><span class="core-mark" aria-hidden="true">✦</span>'
        f'<span>{core["title"]}</span><i aria-hidden="true"></i></summary>'
        f'<div class="community-item-body"><div class="community-copy">'
        f'<strong class="community-title"><span class="core-mark" aria-hidden="true">✦</span>{core["title"]}</strong>'
        f'<p>{core["short_desc"]}</p><small>{core["caption"]}</small></div>'
        f'<div class="community-qr core-qr"><img loading="lazy" src="{prefix}core-team-signup.png" width="176" height="176" alt="{core["caption"]}"></div>'
        f'</div></details>'
    )
    label = "社区交流与中心组报名" if zh else "Community discussion and core team signup"
    return f'<aside class="hero-community desk-rail" aria-label="{label}">{"".join(items)}</aside>'


def site_dock(lang, prefix, *, inline=False):
    zh = lang == "zh"
    disc = discussion_copy(lang)
    core = core_team_copy(lang)
    cells = [f'<div class="community-band-cell band-stats">{presence_widget(lang, prefix, variant="footer")}</div>']
    if disc:
        cells.append(
            f'<div class="community-band-cell band-qr">'
            f'<div class="community-copy"><strong class="community-title"><img class="wechat-mark" src="{prefix}wechat.svg" width="22" height="22" alt="">{disc["label"]}</strong>'
            f'<p>{disc["name"]}</p><small>{disc["validity"]}</small></div>'
            f'<div class="community-qr discussion-code"><img loading="lazy" src="{prefix}discussion-qr.png" alt="{disc["alt"]}" width="800" height="1198"></div>'
            f'</div>'
        )
    cells.append(
        f'<div class="community-band-cell band-qr">'
        f'<div class="community-copy"><strong class="community-title"><span class="core-mark" aria-hidden="true">✦</span>{core["title"]}</strong>'
        f'<p>{core["short_desc"]}</p><small>{core["intro"]}</small></div>'
        f'<div class="community-qr core-qr"><img loading="lazy" src="{prefix}core-team-signup.png" width="176" height="176" alt="{core["caption"]}"></div>'
        f'</div>'
    )
    label = "研究台动态与社区交流" if zh else "Research desk stats and community"
    return (
        f'<aside class="community-band{" community-band-inline" if inline else " shell"}" aria-label="{label}">{"".join(cells)}</aside>'
        f'<script src="{prefix}discussion.js" defer></script><script src="{prefix}presence.js" defer></script>'
    )


def research_status(desk=DESK, *, compact=False, board=False):
    db = desk.db_path
    results = []
    latest = {}
    attempts = 0
    extra = {}
    if db.exists():
        with closing(sqlite3.connect(db.as_uri() + "?mode=ro", uri=True)) as conn:
            conn.execute("BEGIN")
            if desk is DESKS.get("quadratic-primes"):
                extra["lpf_record"] = exponent_record(desk, conn)
            if conn.execute("SELECT 1 FROM sqlite_master WHERE type='table' AND name='verdicts'").fetchone():
                projection = (
                    "json_object('lemma_id', json_extract(CAST(body AS TEXT), '$.lemma_id'), "
                    "'verdict', json_extract(CAST(body AS TEXT), '$.verdict'), "
                    "'run_id', run_id, 'run_attempt', attempt, "
                    "'check_id', json_extract(CAST(body AS TEXT), '$.check_id'), "
                    "'head_sha', json_extract(CAST(body AS TEXT), '$.head_sha'))"
                ) if board else "body"
                results = [json.loads(body) for (body,) in conn.execute(
                    f"SELECT {projection} FROM verdicts ORDER BY run_id DESC, attempt DESC LIMIT ?", (1 if board else 12,)
                )]
                payload = "json_remove(CAST(v.body AS TEXT), '$.manifest')" if compact else "v.body"
                rows = conn.execute(f"""
                    WITH runs AS (
                        SELECT run_id, attempt,
                               json_extract(CAST(body AS TEXT), '$.lemma_id') AS lemma,
                               json_extract(CAST(body AS TEXT), '$.verdict') AS verdict
                        FROM verdicts
                    ), ranked AS (
                        SELECT run_id, attempt, lemma,
                               ROW_NUMBER() OVER (
                                   PARTITION BY lemma ORDER BY run_id DESC, attempt DESC
                               ) AS position,
                               MAX(verdict = 'ACCEPTED') OVER (PARTITION BY lemma) AS proved,
                               COUNT(*) OVER (PARTITION BY lemma) AS attempts
                        FROM runs
                    )
                    SELECT lemma, {payload}, proved, attempts FROM ranked
                    JOIN verdicts AS v USING (run_id, attempt) WHERE position = 1
                """)
                for lemma, body, proved, count in rows:
                    latest[lemma] = (json.loads(body), bool(proved))
                    attempts += count
                if not board:
                    desk.annotate_verdicts(results, conn)
                desk.annotate_verdicts([result for result, _ in latest.values()], conn)

    gaps = []
    for gap in desk.gaps.values():
        result, proved = latest.get(gap["id"], (None, False))
        gaps.append({**gap, "latest": result, "proved": proved, "route_id": TASK_ROUTE[gap["id"]]})
    accepted = sum(gap["proved"] for gap in gaps)
    desk_status = desk.public_status()
    rankings = desk_status["rankings"]
    rows = rankings["all_time"] + rankings["hour"]
    profiles = ZHIHU.public_profiles(sorted({row["handle"].lower() for row in rows}))
    for row in rows:
        profile = profiles.get(row["handle"].lower())
        if profile:
            row["zhihu"] = profile
    return {
        **extra,
        "catalogue_revision": RELEASE_SHA,
        "gaps": gaps,
        **({"tracks": GOLDBACH_CATALOGUE.get("tracks", [])} if desk is DESK else {}),
        "results": results,
        "desk": desk_status,
        "counts": {
            "published": len(gaps),
            "accepted": accepted,
            "open": len(gaps) - accepted,
            "attempts": attempts,
        },
    }

# Bound the memory used by concurrent full-history renders across all problem desks.
STATUS_BUILD = BoundedSemaphore(1)
WEB_SNAPSHOTS = {}


RAW_STATUS_CLIENTS = OrderedDict()
RAW_STATUS_LOCK = Lock()


def raw_status_allowed(ip):
    now = time.monotonic()
    with RAW_STATUS_LOCK:
        credit, last = RAW_STATUS_CLIENTS.pop(ip, (4, now))
        credit = min(4, credit + (now - last) / 30)
        allowed = credit >= 1
        RAW_STATUS_CLIENTS[ip] = (credit - int(allowed), now)
        if len(RAW_STATUS_CLIENTS) > 4096:
            RAW_STATUS_CLIENTS.popitem(last=False)
        return allowed


def accepts_gzip(value):
    for item in value.split(","):
        coding, _, params = item.strip().lower().partition(";")
        if coding.strip() == "gzip":
            return not params or bool(re.fullmatch(r"\s*q\s*=\s*(?:1(?:\.0{0,3})?|0\.\d{0,2}[1-9]\d{0,2})\s*", params))
    return False


def status_body(desk, web_view, board=False, compress=False, delta=False):
    key = (desk, web_view, board, delta)
    cached = WEB_SNAPSHOTS.get(key) if compress else None
    if cached and cached[0] > time.monotonic():
        return cached[1]
    with STATUS_BUILD:
        if compress:
            cached = WEB_SNAPSHOTS.get(key)
            if cached and cached[0] > time.monotonic():
                return cached[1]
        status = research_status(desk, compact=web_view, board=board)
        if delta:
            status["gaps"] = [{k: gap[k] for k in ("id", "latest", "proved")} for gap in status["gaps"]]
            status.pop("tracks", None)
        body = json.dumps(status, ensure_ascii=False, separators=(",", ":")).encode()
        if compress:
            body = gzip.compress(body, compresslevel=5, mtime=0)
            WEB_SNAPSHOTS[key] = (time.monotonic() + 10, body)
        return body


def desk_routes(slug, lang):
    """Read route membership from the catalogue used by the claim service."""
    if slug != "goldbach":
        routes = [(stage.get("route_id") or stage.get("route_source") or f"stage-{i+1}", *stage[lang],
                   {task["id"]: task[lang] for task in stage["tasks"]}, [])
                  for i, stage in enumerate(PROBLEMS[slug]["roadmap"])]
    else:
        groups = {}
        for gap in GAPS:
            groups.setdefault(gap.get("track"), {})[gap["id"]] = gap["plain_statement"][lang]
        tracks = GOLDBACH_CATALOGUE.get("tracks", [])
        titles = {t["id"]: t["title"][lang] for t in tracks}
        routes = [(t["id"], titles[t["id"]], t["description"][lang], groups.get(t["id"], {}),
                   [(key, titles[key]) for key in t["feeds"]]) for t in tracks]
    listed = {task for _, _, _, tasks, _ in routes for task in tasks}
    remaining = {key: gap["plain_statement"][lang] for key, gap in DESKS[slug].gaps.items() if key not in listed}
    if remaining:
        routes.append(("unclassified", "未分路线的命题" if lang == "zh" else "Unassigned tasks",
                       "", remaining, []))
    return routes


# Shared by the map, claim receipt and public verification records.
TASK_ROUTE = {task: key for slug in DESKS for key, _, _, tasks, _ in desk_routes(slug, "en") for task in tasks}

def route_refutations(slug, tasks, lang):
    labels = {"pending": ("反证待核验", "Refutation under review"), "verified": ("已证伪", "Refuted")}
    notes = []
    for task in tasks:
        ref = DESKS[slug].gaps[task].get("refutation")
        if ref:
            notes.append(f'{labels[ref["status"]][lang != "zh"]} · #{int(ref["pr"])}')
    return f'<small class="route-meta">{escape(" · ".join(notes))}</small>' if notes else ""


def route_filters(slug, lang):
    return "".join(
        f'<button type="button" class="map-program-button" data-program="{escape(key)}" aria-pressed="false">'
        f'<strong class="program-name">{escape(title)}</strong>{route_refutations(slug, tasks, lang)}<span class="program-count">{len(tasks)} '
        f'{"题" if lang == "zh" else "tasks"}</span></button>'
        for key, title, _, tasks, _ in desk_routes(slug, lang)
    )


def goldbach_program_filters(lang):
    zh = lang == "zh"
    programs = (
        ("foundation", "素数权重" if zh else "Prime weights"),
        ("grh", "黎曼猜想与素数分布" if zh else "GRH & prime distribution"),
        ("correlation", "二元加法相关" if zh else "Binary correlations"),
        ("exceptions", "例外集合" if zh else "Exceptional sets"),
    )
    return "".join(
        f'<button type="button" class="map-program-button" data-program="{key}" aria-pressed="false">'
        f'<strong class="program-name">{title}</strong><span class="program-count">—</span></button>'
        for key, title in programs
    )


def route_panels(slug, lang):
    zh = lang == "zh"
    sections = []
    for key, title, description, tasks, feeds in desk_routes(slug, lang):
        links = []
        for task, label in tasks.items():
            role = DESKS[slug].gaps[task].get("role")
            prefix = {"target": "待突破 · " if zh else "Research target · ",
                      "conditional": "条件归约 · " if zh else "Conditional · "}.get(role, "")
            ident = escape(task)
            links.append(f'<a href="?lang={lang}&amp;lemma={ident}#roadmap" data-roadmap-task="{ident}">'
                         f'{prefix}{escape(label)}</a>')
        targets = " · ".join(f'<a href="#track-{escape(k)}">{escape(v)}</a>' for k, v in feeds)
        following = f'<p>{"用于" if zh else "Feeds into"}　{targets}</p>' if targets else ""
        sections.append(f'<details class="route-panel" id="track-{escape(key)}"><summary>'
                        f'<strong>{escape(title)}</strong>{route_refutations(slug, tasks, lang)}<span class="route-meta">{len(tasks)} '
                        f'{"题" if zh else "tasks"}<span data-route-status></span></span></summary>'
                        f'<p>{escape(description)}</p>{following}<div class="roadmap-tasks">{"".join(links)}</div></details>')
    return '<div class="goldbach-tracks"><h3>' + ("按子命题领取" if zh else "Choose a proof task") + '</h3>' + "".join(sections) + '</div>'


def goldbach_roadmap_page(page, lang):
    # The research map shows every catalogue route, so the home page keeps only the story under #roadmap.
    if RELEASE_SHA:
        page = page.replace("</head>", f'<meta name="catalogue-revision" content="{escape(RELEASE_SHA)}"></head>', 1)
    zh = lang == "zh"
    changes = "研究路线变更记录" if zh else "Research change history"
    full = "查看完整路线" if zh else "Read the full roadmap"
    links = (f'<div class="heading-links"><a class="text-link" href="research-changes?lang={lang}">{changes}</a>'
             '<a class="text-link" href="https://github.com/CGandGameEngineLearner/goldbach-proofs/blob/main/research/ROADMAP.md">'
             f'{full} <span aria-hidden="true">↗</span></a></div>')
    page = page.replace("<!-- map links -->", links, 1)
    page = re.sub(r'(<nav class="navigation"[^>]*>.*?)<a href="#roadmap">[^<]*</a>',
                  lambda m: m[1] + f'<a href="#research-story">{"背景故事" if zh else "Story"}</a>', page, count=1, flags=re.S)
    page = re.sub(r'(<header class="target-header">.*?)<a href="#roadmap">',
                  lambda m: m[1] + '<a href="#lemmas">', page, count=1, flags=re.S)
    return page.replace("<!-- catalogue filters -->", goldbach_program_filters(lang))


def problem_page(page, slug, lang):
    data = PROBLEMS[slug]
    title, question, description = (escape(data[key][lang]) for key in ("title", "question", "summary"))
    zh = lang == "zh"
    translations = {
        "map": "研究地图" if zh else "Research map",
        "target": "研究起点" if zh else "Starting point",
        "road": "研究路线" if zh else "Research roadmap",
        "foundation": "基础引理" if zh else "Foundations",
        "correlation": "证明工具" if zh else "Proof techniques",
    }
    if slug == "quadratic-primes":
        translations["target"] = "大素因子指数" if zh else "Large prime factor exponent"
    page = page.replace('<body id="top">', f'<body id="top" data-problem="{slug}">')
    page = re.sub(r'<title>[^<]*</title>', f'<title>{title}</title>', page, count=1)
    page = re.sub(r'<meta (?:name|property)="(?:description|og:[^"]+|twitter:[^"]+)"[^>]*>\n?', '', page)
    page = re.sub(r'(<a href="#top" class="brand">.*?</span>)[^<]+', lambda m: m[1] + title, page, count=1)
    page = page.replace('aria-hidden="true">p + q ?</span>', f'aria-hidden="true">{escape(data["formula"])}</span>', 1)
    page = page.replace('href="problems/?', 'href="../?').replace('href="site.css"', 'href="../../site.css"').replace(
        'src="site.js"', 'src="../../site.js"')
    page = page.replace('href="goldbach-icon.svg"', 'href="../../goldbach-icon.svg"')
    page = page.replace('src="goldbach-icon.svg"', 'src="../../goldbach-icon.svg"')
    page = page.replace('href="auth/zhihu?', 'href="../../auth/zhihu?')
    page = re.sub(r'(<h1 id="page-title">).*?(</h1>)', lambda m: m[1] + title + m[2], page)
    page = re.sub(r'(<p class="hero-question">).*?(</p>)', lambda m: m[1] + question + m[2], page)
    page = re.sub(r'(<p class="hero-description">).*?(</p>)', lambda m: m[1] + description + m[2], page)
    page = page.replace("强猜想 · 尚未解决", "开放研究问题").replace("Strong conjecture · Open", "Open research problem")
    page = re.sub(r'(<h2 id="target-title">).*?(</h2>)',
                  lambda m: m[1] + translations["target"] + m[2], page)
    formula = escape(data["formula"])
    figure = f'<div class="target-figure topic-formula">{formula}</div>'
    if slug == "quadratic-primes":
        current = "当前研究指数" if zh else "Current research exponent"
        target = "目标指数" if zh else "Target exponent"
        condition = ("对无穷多个 n，存在整除 n² + 1 的素数 p，且 p > nᵅ。若能证明 α = 2，则 p 只能等于 n² + 1。" if zh else
                     "For infinitely many n, a prime p divides n² + 1 with p > nᵅ. At α = 2 this forces p = n² + 1.")
        source = ("外部基线证书" if zh else "External baseline certificate") + f' · {BASELINE["exponent"]}'
        status_link = "查看实时数据" if zh else "View live data"
        article = "https://www.cambridge.org/engage/coe/article-details/6aa045a1810b9dcc82ba1e4b"
        news = "最新成果" if zh else "Research news"
        headline = "n² + 1 的大素因子：指数达到 1.323" if zh else "Large prime factors of n² + 1 reach exponent 1.323"
        summary = ("这篇预印本报告，通过在 Harman 筛中递归使用 Buchstab 恒等式，可证明对无穷多个正整数 n，"
                   "存在素数 p 整除 n² + 1，且 p > n¹·³²³。这个界允许 n² + 1 还有其他因子。"
                   "本站以 1.323 为外部基线，下一步是提高这个指数。" if zh else
                   "The preprint reports that recursive Buchstab switching in a Harman sieve gives infinitely many "
                   "positive integers n for which a prime divisor p of n² + 1 exceeds n¹·³²³. Other factors may remain. "
                   "The project takes 1.323 as its external baseline and aims to raise the exponent.")
        read = "阅读预印本" if zh else "Read the preprint"
        close = "关闭" if zh else "Close"
        figure = (
            '<div class="lpf-record" id="lpf-record">'
            f'<dl class="lpf-values"><div><dt>{current} α</dt><dd id="lpf-current">—</dd></div>'
            f'<div><dt>{target}</dt><dd id="lpf-target">2</dd></div></dl>'
            '<p class="lpf-evidence" id="lpf-kind"></p><p id="lpf-verified"></p>'
            f'<p class="lpf-condition">{condition}</p>'
            f'<a href="{escape(BASELINE["source_url"])}">{source}</a>'
            f'<noscript> · <a href="api/status">{status_link}</a></noscript>'
            '<p id="lpf-notice" role="status"></p></div>'
            f'<a id="lpf-news-open" href="{article}">{news} · 1.323</a>'
            '<dialog class="rankings-dialog lpf-news" id="lpf-news" aria-labelledby="lpf-news-title">'
            f'<div class="rankings-dialog-heading"><span>{news}</span><form method="dialog"><button>{close}</button></form></div>'
            f'<h2 id="lpf-news-title">{headline}</h2><p><time datetime="2026-09-13">2026-09-13</time> · Cambridge Open Engage</p>'
            f'<p>{summary}</p><a href="{article}">{read} ↗</a></dialog>'
        )
    page = re.sub(r'<div class="target-figure".*?<div class="target-progress">',
                  lambda _: figure + '<div class="target-progress">', page, count=1, flags=re.S)
    page = re.sub(r'(<h2 id="lemma-title">).*?(</h2>)', lambda m: m[1] + title + ' · ' + translations["map"] + m[2], page)
    materials = data.get("materials", [])
    note_title = ("前期研究" if zh else "Prior research") if materials else translations["road"]
    note_body = escape(data["background"][lang]) if materials else description
    references = " · ".join(f'<a href="{escape(item["url"])}">{escape(item[lang])}</a>' for item in materials)
    page = re.sub(r'<aside class="method-note">.*?</aside>',
                  lambda _: f'<aside class="method-note"><h2>{note_title}</h2><p>{note_body}</p>{references}</aside>',
                  page, count=1, flags=re.S)
    page = page.replace("<!-- catalogue filters -->", route_filters(slug, lang))
    page = page.replace("<!-- map links -->", "", 1)
    stages = route_panels(slug, lang)
    page = re.sub(r'<section class="section road-section" id="roadmap".*?</section>',
                  lambda _: f'<section class="section road-section" id="roadmap"><div class="section-heading"><div>'
                  f'<h2>{translations["road"]}</h2></div></div>{stages}</section>',
                  page, count=1, flags=re.S)
    url = PUBLIC_SITE + "problems/" + slug + "/join" + ("-zh" if zh else "") + ".txt"
    prompt = (f"阅读 {url}，按说明领取一条任务，提交 Lean 证明并跟踪核验。"
              "可导入 gap.imports 列出的社区引理，也可查阅网上资料，把相关方法形式化到指定的 Lean 文件，并在 PR 中注明来源。" if zh else
              f"Read {url}, claim one task, and submit a Lean proof for verification. "
              "You may import community lemmas listed in gap.imports and research methods online. "
              "Formalize the relevant steps in your assigned Lean file and cite your sources in the PR.")
    page = re.sub(r'(<p id="agent-prompt"[^>]*>).*?(</p>)', lambda m: m[1] + escape(prompt) + m[2], page)
    return page


def problem_card(slug, data, lang):
    zh = lang == "zh"
    try:
        verified, published, available, active = DESKS[slug].progress_snapshot()
    except sqlite3.Error:
        progress = "暂时无法读取进度" if zh else "Progress temporarily unavailable"
    else:
        progress = (f"Lean 已核验 {verified}/{published} · {available} 条可领取" if zh else
                    f"Lean verified {verified}/{published} · {available} available")
        running = [title for _, title, _, tasks, _ in desk_routes(slug, lang) if active.intersection(tasks)]
        activity = ("进行中 · " if zh else "In progress · ") + ("、" if zh else ", ").join(running) if running else (
            "当前无活跃路线" if zh else "No active routes")
        progress += f'<span class="desk-running">{escape(activity)}</span>'
    url = "../" if slug == "goldbach" else slug + "/"
    anchor = "#lemmas" if slug == "goldbach" else "#roadmap"
    return (f'<a class="problem-card" href="{url}?lang={lang}{anchor}"><span class="problem-formula">{escape(data["formula"])}</span>'
            f'<h2>{escape(data["title"][lang])}</h2><p>{escape(data["question"][lang])}</p>'
            f'<p class="problem-progress">{progress}</p></a>')


TWIN_PRIMES_SLUG = "twin-primes"
TWIN_PRIMES_FORMULA = "p, p + 2"
TWIN_PRIMES_COPY = {
    "zh": (
        "孪生素数猜想",
        "是否有无穷多对相差 2 的素数？",
        "任务筹备中",
        "返回猜想目录",
        "历史进展",
        "例如 (3, 5)、(11, 13) 和 (17, 19) 都是孪生素数。",
        "陈景润证明，有无穷多个素数 p，使 p + 2 是至多两个素数的乘积（按重数计）。猜想要求其中无穷多个 p + 2 本身是素数。",
        "张益唐于 2013 年证明，有无穷多对相邻素数的间隔小于 7000 万。孪生素数猜想要求间隔恰好为 2 的情形出现无穷多次。",
        "拟议路线将研究 Levent 的 GRH 证明中使用的方法组合及其自然推广能否处理固定移位 2 的素数对。",
        "查看研究任务拆分提案",
    ),
    "en": (
        "Twin prime conjecture",
        "Are there infinitely many pairs of primes that differ by 2?",
        "Tasks in preparation",
        "Back to research problems",
        "Historical results",
        "Examples include (3, 5), (11, 13), and (17, 19).",
        "Chen Jingrun proved that infinitely many primes p have p + 2 equal to a product of at most two primes, counted with multiplicity. The conjecture asks whether p + 2 itself is prime for infinitely many such p.",
        "In 2013, Yitang Zhang proved that infinitely many consecutive prime pairs have a gap below 70 million. The twin prime conjecture asks whether the gap is exactly 2 infinitely often.",
        "The proposed research will examine whether the methods used in Levent’s GRH proof and their natural extensions can handle prime pairs at the fixed shift 2.",
        "View the proposed research tasks",
    ),
}


def twin_primes_page(lang):
    title, question, status, back, history, examples, chen, zhang, route, proposal = TWIN_PRIMES_COPY[lang]
    other_lang, other_label = ("en", "English") if lang == "zh" else ("zh", "简体中文")
    chen_label = "陈景润原论文" if lang == "zh" else "Chen’s paper"
    zhang_label = "张益唐原论文" if lang == "zh" else "Zhang’s paper"
    return f"""<!doctype html>
<html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title><link rel="icon" type="image/svg+xml" sizes="any" href="../../goldbach-icon.svg">
<link rel="stylesheet" href="../../site.css"></head>
<body><header class="masthead"><div class="shell masthead-inner"><a class="brand" href="../?lang={lang}">{back}</a>
<a class="locale" href="?lang={other_lang}">{other_label}</a></div></header>
<main class="shell problem-directory">
<span class="problem-formula">{TWIN_PRIMES_FORMULA}</span><h1>{title}</h1>
<p>{question} {examples}</p>
<section><h2>{history}</h2>
<p>{chen} <a href="https://doi.org/10.1142/9789812776600_0021">{chen_label}</a></p>
<p>{zhang} <a href="https://doi.org/10.4007/annals.2014.179.3.7">{zhang_label}</a></p></section>
<section><h2>{status}</h2><p>{route}</p>
<p><a href="https://github.com/CGandGameEngineLearner/goldbach-proofs/pull/2388">{proposal}</a></p></section>
</main>{site_dock(lang, "../../")}</body></html>"""


def directory_page(lang):
    zh = lang == "zh"
    heading = "更多猜想" if zh else "Research problems"
    back = "返回强哥德巴赫猜想" if zh else "Back to Strong Goldbach"
    platform = "数学猜想协作平台" if zh else "Open Conjecture Platform"
    intro = ("数学家可以担任研究管理员，制定路线、拆分引理和审阅命题。选一道感兴趣的猜想，把参与提示词交给自己的 Agent，就可以从一条引理开始。" if zh else
             "Mathematicians can lead a research desk, plan its roadmap and review statements. Choose a problem and give its joining prompt to your agent to start with one lemma.")
    main = {"title": {"zh": "强哥德巴赫猜想", "en": "Strong Goldbach conjecture"},
            "question": {"zh": "每个大于 2 的偶数都是两个素数之和吗？", "en": "Is every even integer above two a sum of two primes?"},
            "formula": "2n = p + q"}
    cards = "\n".join(problem_card(slug, data, lang) for slug, data in {"goldbach": main, **PROBLEMS}.items())
    if TWIN_PRIMES_SLUG not in PROBLEMS:
        title, question, status, *_ = TWIN_PRIMES_COPY[lang]
        cards += (f'<a class="problem-card" href="{TWIN_PRIMES_SLUG}/?lang={lang}">'
                  f'<span class="problem-formula">{TWIN_PRIMES_FORMULA}</span>'
                  f'<h2>{title}</h2><p>{question}</p><p class="problem-progress">{status}</p></a>')
    return f"""<!doctype html>
<html lang="{lang}"><head><meta charset="utf-8"><meta name="viewport" content="width=device-width, initial-scale=1">
<title>{heading} · {platform}</title><link rel="icon" type="image/svg+xml" sizes="any" href="../goldbach-icon.svg"><link rel="stylesheet" href="../site.css"></head>
<body><header class="masthead"><div class="shell masthead-inner"><a class="brand" href="../?lang={lang}">{back}</a>
<a class="locale" href="?lang={'en' if zh else 'zh'}">{'English' if zh else '简体中文'}</a></div></header>
<main class="shell problem-directory"><div class="platform-credit"><img src="../goldbach-icon.svg" width="38" height="38" alt=""><strong>{platform}</strong></div><h1>{heading}</h1><p>{intro}</p><a href="https://github.com/CGandGameEngineLearner/goldbach-proofs">GitHub ↗</a><div class="problem-list">{cards}</div></main>{site_dock(lang, "../")}</body></html>"""


def queue_pending(raw_body, headers):
    if not DESK.signed(headers.get("X-Goldbach-Signature", ""), raw_body):
        return 401, {"error": "invalid_signature"}
    now = int(time.time())
    desks = tuple(DESKS.values())
    quota = max(1, QUEUE_BATCH // len(desks))
    rows = []
    for desk in desks:
        if len(rows) >= QUEUE_BATCH:
            break
        rows.extend(desk.pending(now, min(quota, QUEUE_BATCH - len(rows)))[1]["pending"])
    for desk in desks:
        if len(rows) >= QUEUE_BATCH:
            break
        rows.extend(desk.pending(now, QUEUE_BATCH - len(rows))[1]["pending"])
    return 200, {"pending": rows}


def china_networks():
    for line in (ROOT / "china-apnic.txt").read_text(encoding="utf-8").splitlines():
        fields = line.split("|")
        if len(fields) < 7 or fields[1] != "CN" or fields[6] not in {"allocated", "assigned"}:
            continue
        _, _, kind, start, size, *_ = fields
        if kind == "ipv4":
            first = ipaddress.IPv4Address(start)
            yield from ipaddress.summarize_address_range(first, first + int(size) - 1)
        if kind == "ipv6":
            yield ipaddress.IPv6Network(f"{start}/{size}")

NETWORKS = tuple(china_networks())

class Handler(BaseHTTPRequestHandler):
    def log_request(self, code="-", size="-"):
        if getattr(self, "path", "").partition("?")[0].startswith(ZHIHU_PATH):
            self.log_message("Zhihu authorization request %s", code)
        else:
            super().log_request(code, size)

    def zhihu_request(self, path, query=""):
        if self.command == "HEAD":
            return self.reply(405, b'{}')
        if self.command == "GET" and path == sponsors.DESK + "/upload-limit":
            return self.oauth_response(path, sponsors.upload_error(self.language(urlsplit(self.path))))
        if self.command == "POST" and path == sponsors.DESK + "/upload":
            return self.sponsor_upload(path)
        try:
            if self.command == "POST":
                size = int(self.headers.get("Content-Length", "0"))
                if not 0 < size <= 8192 or self.headers.get_content_type() != "application/x-www-form-urlencoded":
                    return self.reply(400, b'{}')
                self.connection.settimeout(8)
                query = self.rfile.read(size).decode("utf-8")
            if len(query) > 12000:
                return self.reply(400, b'{}')
            fields = parse_qs(query, keep_blank_values=True, max_num_fields=12)
            if any(len(vals) != 1 for vals in fields.values()):
                return self.reply(400, b'{}')
            status, headers, body = ZHIHU.handle(self.command, path, {k: v[0] for k, v in fields.items()}, self.headers)
        except (ValueError, OSError, sqlite3.Error):
            return self.reply(400, b'{}')
        return self.oauth_response(path, (status, headers, body))

    def sponsor_upload(self, path):
        lang = self.language(urlsplit(self.path))
        def notice(status, zh, en):
            return self.oauth_response(path, sponsors.upload_notice(status, lang, zh if lang == "zh" else en))

        self.connection.settimeout(8)
        try:
            size = int(self.headers.get("Content-Length", "0"))
            if size > sponsors.LIMIT:
                self.discard_upload(size)
                return self.oauth_response(path, sponsors.upload_error(lang))
            if self.headers.get("Origin") != sponsors.ORIGIN:
                self.discard_upload(size)
                return notice(403, "请从本站设置页重新提交。", "Resubmit from the site settings page.")
            if not ZHIHU.can_upload_sponsor(self.headers):
                self.discard_upload(size)
                return notice(403, "登录已过期，请重新登录知乎后提交。", "Your session expired. Sign in with Zhihu and retry.")
            if not SPONSOR_UPLOAD_SLOT.acquire(blocking=False):
                self.discard_upload(size)
                return self.oauth_response(path, sponsors.upload_error(lang, busy=True))
            try:
                raw = self.rfile.read(size) if size > 0 else b""
                if len(raw) != size or self.headers.get_content_type() != "multipart/form-data":
                    raise ValueError("incomplete upload")
                fields = sponsors.upload_fields(self.headers["Content-Type"], raw)
                fields["lang"] = lang
                result = ZHIHU.handle("POST", path, fields, self.headers)
            finally:
                SPONSOR_UPLOAD_SLOT.release()
        except (ValueError, RecursionError):
            return notice(400, "上传表单不完整，请重新选择图片后再试。", "The upload was incomplete. Select the image again and retry.")
        except TimeoutError:
            return notice(408, "上传超时，请重新提交。", "The upload timed out. Try again.")
        except sqlite3.Error:
            self.log_error("Sponsor submission database unavailable")
            return notice(503, "暂时无法保存投稿，请稍后重试。", "Submission could not be saved. Try again shortly.")
        return self.oauth_response(path, result)

    def discard_upload(self, size):
        # Drain a buffered proxy request so closing the TLS connection keeps the error response.
        remaining = min(size, 5 * 1024 * 1024)
        while remaining > 0:
            chunk = self.rfile.read(min(remaining, 64 * 1024))
            if not chunk:
                break
            remaining -= len(chunk)

    def oauth_response(self, path, result):
        status, headers, body = result
        self.send_response(status)
        for name, value in headers.items():
            self.send_header(name, value)
        self.send_header("Cache-Control", "no-store")
        # Form pages must preserve Origin on same-site POSTs for CSRF validation.
        policy = "same-origin" if path != ZHIHU_PATH + "/callback" else "no-referrer"
        self.send_header("Referrer-Policy", policy)
        self.send_header("Content-Security-Policy", "default-src 'none'; img-src 'self'; style-src 'self' 'unsafe-inline'; script-src 'self'; connect-src 'self'; form-action 'self' https://openapi.zhihu.com https://www.zhihu.com; frame-ancestors 'none'; base-uri 'none'")
        self.send_header("X-Content-Type-Options", "nosniff")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def reply(self, status, body, content_type="application/json", language=None, encoding=None, static=False, cache=None, etag=None, vary=False, retry_after=None):
        if status == 200 and self.command == "GET" and content_type == "text/html":
            try:
                with closing(sqlite3.connect(PAGE_VIEWS_DB)) as conn, conn:
                    conn.execute("UPDATE page_views SET total = total + 1 WHERE source = 'live'")
                    ip = self.client_ip()
                    ip = getattr(ip, "ipv4_mapped", None) or ip
                    if not ip.is_loopback:
                        digest = hmac.digest(IP_KEY, ip.packed, "sha256")
                        conn.execute("INSERT OR IGNORE INTO visitor_ips VALUES (?)", (digest,))
            except sqlite3.Error:
                self.log_error("Page view counter unavailable")
        self.send_response(status)
        if content_type == "application/json" or content_type.startswith("text/"):
            content_type += "; charset=utf-8"
        self.send_header("Content-Type", content_type)
        if static or vary:
            self.send_header("Vary", "Accept-Encoding")
        if etag:
            self.send_header("ETag", etag)
        if retry_after:
            self.send_header("Retry-After", str(retry_after))
        if encoding:
            self.send_header("Content-Encoding", encoding)
        self.send_header("Cache-Control", cache or ("public, max-age=300" if static else "no-store"))
        self.send_header("X-Content-Type-Options", "nosniff")
        if status != 304:
            self.send_header("Content-Length", str(len(body)))
        if language:
            self.send_header("Content-Language", language)
        self.end_headers()
        if self.command != "HEAD":
            self.wfile.write(body)

    def public_conditional(self, body, content_type="application/json", encoding=None, cache="public, max-age=10", vary=False):
        etag = '"' + hashlib.sha256(body).hexdigest() + '"'
        validators = {item.strip().removeprefix("W/") for item in self.headers.get("If-None-Match", "").split(",")}
        if etag in validators or "*" in validators:
            return self.reply(304, b"", content_type, cache=cache, etag=etag, vary=vary)
        return self.reply(200, body, content_type, encoding=encoding, cache=cache, etag=etag, vary=vary)

    def client_ip(self):
        peer = ipaddress.ip_address(self.client_address[0])
        peer = getattr(peer, "ipv4_mapped", None) or peer
        if peer.is_loopback:
            forwarded = self.headers.get("X-Goldbach-Client-IP")
            if forwarded:
                try:
                    return ipaddress.ip_address(forwarded)
                except ValueError:
                    pass
        return peer

    def language(self, url):
        lang = parse_qs(url.query).get("lang", [""])[0]
        if lang in {"zh", "en"}:
            return lang
        return "zh" if any(self.client_ip() in net for net in NETWORKS) else "en"

    @staticmethod
    def scope(path):
        match = re.fullmatch(r"/problems/([a-z-]+)(/.*)", path)
        if match:
            return DESKS.get(match[1]) if match[1] in PROBLEMS else None, match[2], match[1]
        return DESK, path, "goldbach"

    def reply_presence(self, visitor=None):
        counts = PRESENCE.snapshot(visitor)
        try:
            with closing(sqlite3.connect(PAGE_VIEWS_DB)) as conn:
                counts["page_views"] = conn.execute("SELECT sum(total) FROM page_views").fetchone()[0]
                counts["unique_ips"] = conn.execute("SELECT count(*) FROM visitor_ips").fetchone()[0]
        except sqlite3.Error:
            counts["page_views"] = counts["unique_ips"] = None
        return self.reply(200, json.dumps(counts).encode())

    def do_GET(self):
        url = urlsplit(self.path)
        if url.path == "/api/presence":
            return self.reply_presence()
        logo = re.fullmatch(r"/sponsors/logo/([1-9][0-9]{0,15})\.png", url.path)
        if logo:
            image = sponsors.public_logo(ZHIHU.db, logo[1])
            return self.public_conditional(image, "image/png", cache="public, max-age=3600") if image else self.reply(404, b'{}')
        if url.path == ZHIHU_PATH or url.path.startswith(ZHIHU_PATH + "/"):
            return self.zhihu_request(url.path, url.query)
        twin_primes_path = f"/problems/{TWIN_PRIMES_SLUG}"
        if (url.path in {"/problems", twin_primes_path}
                or url.path.removeprefix("/problems/") in PROBLEMS):
            self.send_response(308)
            suffix = "?" + url.query if url.query else ""
            self.send_header("Location", url.path.rsplit("/", 1)[-1] + "/" + suffix)
            self.send_header("Content-Length", "0")
            self.end_headers()
            return
        if url.path == "/problems/":
            lang = self.language(url)
            directory = directory_page(lang).replace("</main>", "</main>" + sponsors.wall(ZHIHU.db,lang,"../"), 1)
            directory = directory.replace('</a></div></header>', '</a>'+ZHIHU.account_link(self.headers,lang)+'</div></header>',1)
            return self.reply(200, directory.encode(), "text/html", lang)
        if url.path == twin_primes_path + "/" and TWIN_PRIMES_SLUG not in PROBLEMS:
            lang = self.language(url)
            return self.reply(200, twin_primes_page(lang).encode(), "text/html", lang)
        desk, path, slug = self.scope(url.path)
        if desk is None:
            return self.reply(404, b'{}')
        if path == "/health":
            return self.reply(200, json.dumps({
                "status": "ok", "catalogue_revision": RELEASE_SHA,
                "site_revision": SITE_REVISION,
            }).encode())
        if path == "/research-changes":
            zh = self.language(url) == "zh"
            title = "研究路线变更记录" if zh else "Research change history"
            entries = json.loads((CATALOGUE_ROOT / "history.json").read_bytes()) if RELEASE_SHA else []
            repo = "https://github.com/CGandGameEngineLearner/goldbach-proofs"
            params = parse_qs(url.query)
            raw_end = params.get("end", [str(len(entries))])[0]
            if not re.fullmatch(r"[0-9]{1,10}", raw_end):
                return self.reply(400, b'{"error":"invalid page"}')
            end = min(int(raw_end), len(entries))
            start = max(0, end - 20)
            nav = []
            lang = "zh" if zh else "en"
            if end < len(entries):
                nav.append(f'<a href="?lang={lang}&amp;end={min(end+20,len(entries))}">{"上一页" if zh else "Previous"}</a>')
            if start:
                nav.append(f'<a href="?lang={lang}&amp;end={start}">{"下一页" if zh else "Next"}</a>')
            def run_url(row):
                run = int(row["run"])
                if row.get("provider") == "circleci":
                    return f"https://app.circleci.com/pipelines/github/CGandGameEngineLearner/goldbach-proofs/{run}"
                if row.get("provider") == "jenkins":
                    return f"{repo}/runs/{run}"
                return f"{repo}/actions/runs/{run}"

            rows = "".join(
                f'<li><time>{escape(row["at"])}</time> · <a href="{repo}/pull/{int(row["pr"])}">'
                f'{escape(row["title"])}</a> · {escape(row["actor"])} · '
                f'<a href="{run_url(row)}">CI</a></li>'
                for row in reversed(entries[start:end]))
            empty = "尚无自动发布记录。" if zh else "No automated releases yet."
            page = (f'<!doctype html><html lang="{"zh" if zh else "en"}"><meta charset="utf-8">'
                    f'<meta name="viewport" content="width=device-width,initial-scale=1"><title>{title}</title>'
                    f'<link rel="stylesheet" href="site.css"><main class="shell"><h1>{title}</h1>'
                    f'{("<ol>"+rows+"</ol>") if rows else empty}<nav>{" · ".join(nav)}</nav></main></html>')
            return self.reply(200, page.encode(), "text/html")
        if path == "/api/records":
            query = parse_qs(url.query, keep_blank_values=True)
            before = query.get("before", [])
            if query and (set(query) != {"before"} or len(before) != 1 or
                          not re.fullmatch(r"[0-9]{1,18}-[0-9]{1,18}", before[0])):
                return self.reply(400, b'{"error":"invalid cursor"}')
            cursor = tuple(map(int, before[0].split("-"))) if before else ()
            where = "WHERE (run_id, attempt) < (?, ?)" if cursor else ""
            try:
                with desk.transaction() as conn:
                    rows = []
                    if conn.execute("SELECT 1 FROM sqlite_master WHERE name='verdicts'").fetchone():
                        rows = conn.execute(f"SELECT run_id, attempt, body FROM verdicts {where} "
                                            "ORDER BY run_id DESC, attempt DESC LIMIT 13", cursor).fetchall()
                    results = [json.loads(row[2]) for row in rows[:12]]
                    desk.annotate_verdicts(results, conn)
                following = f"{rows[11][0]}-{rows[11][1]}" if len(rows) == 13 else None
                body = json.dumps({"results": results, "next": following}, ensure_ascii=False).encode()
                if "gzip" in (t.strip() for t in self.headers.get("Accept-Encoding", "").lower().split(",")):
                    return self.reply(200, gzip.compress(body, compresslevel=3), encoding="gzip")
                return self.reply(200, body)
            except sqlite3.Error:
                return self.reply(503, b'{"error":"records unavailable"}')
        if path == "/api/status":
            try:
                view = parse_qs(url.query).get("view")
                delta = view == ["board-delta-gzip"]
                board = delta or view == ["board-gzip"]
                web_view = board or view == ["web-gzip"]
                compress = web_view or accepts_gzip(self.headers.get("Accept-Encoding", ""))
                if (not compress and self.command == "GET" and not self.client_ip().is_loopback
                        and not raw_status_allowed(self.client_ip())):
                    return self.reply(429, b'{"error":"Use Accept-Encoding: gzip for frequent status requests"}',
                                      vary=True, retry_after=30)
                body = status_body(desk, web_view, board, compress=compress, delta=delta)
            except sqlite3.Error as error:
                self.log_error("Unable to read verdicts: %s", error)
                return self.reply(503, b'{"error":"verdicts unavailable"}')
            return self.public_conditional(body, encoding="gzip" if compress else None, vary=True)
        if path == "/platform-logo.svg":
            path = "/goldbach-icon.svg"
        if path in ASSETS:
            asset = ROOT / path[1:]
            if not asset.is_file():
                return self.reply(404, b'{}')
            content = asset.read_bytes()
            if slug != "goldbach" and path in {"/join.txt", "/join-zh.txt"}:
                lang = "zh" if path.endswith("-zh.txt") else "en"
                title = PROBLEMS[slug]["title"][lang]
                introduction = (f"请使用自己的 GitHub 账号，领取并提交一条「{title}」的 Lean 4 引理。"
                                "只有通过权威 Lean 核验的引理才会记入研究台。" if lang == "zh" else
                                f"Use your GitHub account to claim and submit one Lean 4 lemma for {title}. "
                                "The desk credits lemmas that pass authoritative Lean verification.")
                if materials := PROBLEMS[slug].get("materials"):
                    introduction += "\n" + PROBLEMS[slug]["background"][lang] + "\n" + "\n".join(
                        f'{item[lang]}  {item["url"]}' for item in materials
                    )
                if slug == "quadratic-primes":
                    introduction += (
                        "\n研究目标是尽可能提高指数 α。先查看问题页的当前纪录，再领取解析转移、筛法估计或指数挑战。"
                        "1.32301 与 1.324 可并行尝试；其他改进值可在 research/problems.json 提交新任务 PR。"
                        "纪录要求对无穷多个 n 证明存在素因子 p ∣ n²+1 且 p > nᵅ。" if lang == "zh" else
                        "\nAim for the largest provable exponent. Check the current record, then claim an analytic transfer, "
                        "sieve estimate or exponent challenge. Try 1.32301 or 1.324 in parallel, or propose another threshold "
                        "by PR to research/problems.json. A record requires a prime divisor p of n²+1 exceeding nᵅ for infinitely many n."
                    )
                _, _, instructions = asset.read_text(encoding="utf-8").split("\n\n", 2)
                if materials:
                    instructions = instructions.replace("不要提交固定偶数或有限闭区间的枚举结果。", "证明须覆盖所领取命题中的全部输入。").replace(
                        "Fixed-input and finite-range enumeration are outside this research program.",
                        "Cover the full range of inputs in the claimed proposition."
                    )
                instructions = instructions.replace(
                    "\npython tools/goldbach.py claim\n", f"\npython tools/goldbach.py claim --problem {slug}\n"
                )
                instructions = instructions.replace("https://www.goldbach.tech/#records\n", "").replace(
                    PUBLIC_SITE + "#records", f"{PUBLIC_SITE}problems/{slug}/?lang={lang}#records"
                )
                content = f"{title}\n\n{introduction}\n\n{instructions}".encode()
            mime = ASSETS[path]
            static = mime != "text/plain"
            encoding = None
            if static and mime in {"text/css", "text/javascript", "image/svg+xml"}:
                encodings = self.headers.get("Accept-Encoding", "").lower().split(",")
                if "gzip" in (token.strip() for token in encodings):
                    content, encoding = compressed_asset(content), "gzip"
            return self.reply(200, content, mime, encoding=encoding, static=static)
        if path != "/":
            return self.reply(404, b'{}')
        lang = self.language(url)
        page = (ROOT / f"{lang}.html").read_text(encoding="utf-8")
        if slug != "goldbach":
            page = problem_page(page, slug, lang)
        else:
            page = goldbach_roadmap_page(page, lang)
        prefix = "" if slug == "goldbach" else "../../"
        page = page.replace("<!-- account -->", ZHIHU.account_link(self.headers, lang), 1)
        page = page.replace("<!-- presence strip -->", presence_widget(lang, prefix, variant="inline"), 1)
        page = page.replace("<!-- hero community -->", hero_community_card(lang, prefix), 1)
        hero = '<section class="hero" aria-labelledby="page-title">'
        page = page.replace(hero, sponsors.wall(ZHIHU.db, lang, prefix) + hero, 1)
        if "<!-- site dock -->" in page:
            page = page.replace("<!-- site dock -->", site_dock(lang, prefix, inline=True), 1)
        else:
            page = page.replace("</main>", "</main>" + site_dock(lang, prefix), 1)
        self.reply(200, page.encode(), "text/html", lang)

    do_HEAD = do_GET

    def desk_post(self, desk, path, slug):
        try:
            size = int(self.headers.get("Content-Length", "0"))
            if not 1 <= size <= 8192:
                return self.reply(413, b'{"error":"request body must be between 1 and 8192 bytes"}')
            self.connection.settimeout(10)
            raw = self.rfile.read(size)
            body = json.loads(raw)
            if not isinstance(body, dict):
                raise ValueError()
            if path == "/api/desk/pending" and slug == "goldbach":
                status, result = queue_pending(raw, self.headers)
            else:
                if path == "/api/desk/authorize" and slug == "goldbach":
                    gap = body.get("gap")
                    if isinstance(gap, str):
                        desk = DESKS[GAP_DESKS.get(gap, "goldbach")]
                status, result = desk.dispatch(path, body, self.headers, str(self.client_ip()), raw)
                if path == "/api/desk/claim" and status == 201:
                    result["route_id"] = TASK_ROUTE[result["gap"]["id"]]
        except (ValueError, OSError):
            return self.reply(400, b'{"error":"invalid request body"}')
        except sqlite3.Error as error:
            self.log_error("Desk unavailable: %s", error)
            return self.reply(503, b'{"error":"task desk temporarily unavailable"}')
        return self.reply(status, json.dumps(result, ensure_ascii=False).encode())

    def do_POST(self):
        if self.path == "/api/presence":
            visitor = self.headers.get("X-Goldbach-Visit", "")
            if not re.fullmatch(r"[0-9a-f]{32}", visitor):
                return self.reply(400, b'{"error":"invalid presence identifier"}')
            return self.reply_presence(visitor)
        if self.path.startswith(ZHIHU_PATH + "/"):
            return self.zhihu_request(urlsplit(self.path).path)
        desk, path, slug = self.scope(self.path)
        if desk is not None and path.startswith("/api/desk/"):
            return self.desk_post(desk, path, slug)
        if slug != "goldbach" or path != "/api/verdict":
            return self.reply(404, b'{}')
        try:
            self.connection.settimeout(10)
            size = int(self.headers.get("Content-Length", "0"))
            if not 1 <= size <= 262144:
                return self.reply(413, b'{}')
            body = self.rfile.read(size)
            signature = "sha256=" + hmac.new(SECRET, body, hashlib.sha256).hexdigest()
            supplied = self.headers.get("X-Goldbach-Signature", "").encode()
            if not hmac.compare_digest(signature.encode(), supplied):
                return self.reply(401, b'{}')
            record = json.loads(body)
            lemma = record["lemma_id"]
            verdict = record["verdict"]
            run_id = record["run_id"]
            attempt = record["run_attempt"]
            manifest = record["manifest"]
            head_sha = record.get("head_sha")
            if "head_sha" in record and (not isinstance(head_sha, str) or not re.fullmatch(r"[a-f0-9]{40}", head_sha)):
                raise ValueError()
            if "check_id" in record and (type(record["check_id"]) is not int or not 1 <= record["check_id"] < 2**53):
                raise ValueError()
            if type(run_id) is not int or run_id < 1 or type(attempt) is not int or attempt < 1:
                raise ValueError()
            if isinstance(lemma, str) and lemma in GAP_DESKS:
                desk = DESKS[GAP_DESKS[lemma]]
            elif not isinstance(lemma, str) or not re.fullmatch(r"L-goldbach-[a-z0-9-]+", lemma):
                raise ValueError()
            if verdict not in {"ACCEPTED", "REJECTED"}:
                raise ValueError()
            if verdict == "ACCEPTED":
                if not manifest["rests_on"]:
                    raise ValueError()
                for key in ("rests_on", "defs"):
                    if not isinstance(manifest[key], list):
                        raise ValueError()
                    for entry in manifest[key]:
                        if not isinstance(entry["module"], str) or not re.fullmatch(r"[a-f0-9]{64}", entry["sha256"]):
                            raise ValueError()
            elif manifest is not None:
                raise ValueError()
        except (ValueError, KeyError, TypeError, OSError):
            return self.reply(400, b'{}')
        with closing(sqlite3.connect(desk.db_path)) as conn, conn:
            if (desk is not DESK or head_sha is not None) and conn.execute(
                "SELECT 1 FROM goldbach_leases WHERE run_id = ? AND gap = ? AND (? IS NULL OR head = ?)",
                (run_id, lemma, head_sha, head_sha),
            ).fetchone() is None:
                return self.reply(409, b'{"error":"no matching authorized run"}')
            conn.execute("CREATE TABLE IF NOT EXISTS verdicts (run_id INTEGER, attempt INTEGER, body BLOB, PRIMARY KEY (run_id, attempt))")
            inserted = conn.execute("INSERT OR IGNORE INTO verdicts VALUES (?, ?, ?)", (run_id, attempt, body))
            if inserted.rowcount == 1:
                desk.record_verdict(record, conn)
        self.reply(200, b'{"status":"stored"}')

class Server(ThreadingHTTPServer):
    request_queue_size = 256

    def __init__(self, address, handler):
        self.tls = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
        self.tls.load_cert_chain(CREDS / "fullchain.pem", CREDS / "privkey.pem")
        self.slots = BoundedSemaphore(16)
        super().__init__(address, handler)

    def process_request(self, request, address):
        self.slots.acquire()
        try:
            super().process_request(request, address)
        except BaseException:
            self.slots.release()
            raise

    def process_request_thread(self, request, address):
        try:
            super().process_request_thread(request, address)
        finally:
            self.slots.release()

    def finish_request(self, request, address):
        request.settimeout(8)
        with self.tls.wrap_socket(request, server_side=True) as connection:
            super().finish_request(connection, address)

if __name__ == "__main__":
    Server(("127.0.0.1", 8443), Handler).serve_forever()
