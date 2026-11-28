"""Exercise identity linking with isolated sessions and stubbed provider network calls."""

import re
import io
import json
import sys
import tempfile
import unittest
from pathlib import Path
from urllib.parse import parse_qs, urlsplit
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import zhihu_oauth as oauth


class ZhihuProviderTests(unittest.TestCase):
    config = {"app_id": "1043", "app_key": "dummy-test-secret"}

    def exchange(self, *replies):
        responses = [io.BytesIO(json.dumps(r).encode()) for r in replies]
        with patch.object(oauth, "build_opener") as factory:
            factory.return_value.open.side_effect = responses
            profile = oauth.exchange_profile(self.config, "dummy-one-time-code")
            for call in factory.call_args_list:
                self.assertIsInstance(call.args[0], oauth.NoRedirect)
            return profile, [c.args[0] for c in factory.return_value.open.call_args_list]

    def test_server_side_exchange_and_minimal_profile_with_exact_user_id(self):
        token = {"access_token": "dummy-test-token", "token_type": "Bearer", "expires_in": 3600}
        uid = 969570047710216293
        result, (exchange, info) = self.exchange(token, {
            "uid": uid, "fullname": "测试昵称", "avatar_path": "https://picx.zhimg.com/avatar.jpg",
            "url_token": "test-author", "phone_no": "private-field", "email": "private@example.invalid",
            "url": f"https://openapi.zhihu.com/users/{uid}",
        })
        self.assertEqual(exchange.get_method(), "POST")
        self.assertEqual(exchange.full_url, "https://openapi.zhihu.com/access_token")
        self.assertEqual(exchange.get_header("Content-type"), "application/x-www-form-urlencoded")
        self.assertEqual(parse_qs(exchange.data.decode()), {
            "app_id": ["1043"], "app_key": [self.config["app_key"]],
            "grant_type": ["authorization_code"], "code": ["dummy-one-time-code"],
            "redirect_uri": ["https://www.goldbach.tech/auth/zhihu/callback"],
        })
        self.assertEqual(info.full_url, "https://openapi.zhihu.com/user")
        self.assertEqual(info.get_method(), "GET")
        self.assertEqual(info.get_header("Authorization"), "Bearer dummy-test-token")
        self.assertEqual(result, {
            "subject": str(uid), "name": "测试昵称", "avatar_url": "https://picx.zhimg.com/avatar.jpg",
            "profile_url": "https://www.zhihu.com/people/test-author",
        })

    def test_discard_unverified_urls(self):
        result, _ = self.exchange({"access_token": "ok"}, {
            "uid": "1", "fullname": "example", "avatar_path": "https://zhimg.com.example.invalid/fake.png",
            "url": "https://openapi.zhihu.com/users/1", "url_token": "../settings",
        })
        self.assertEqual((result["avatar_url"], result["profile_url"]), ("", ""))

    def test_invalid_provider_replies_fail_closed(self):
        for token in [{"code": 403}, {"access_token": ""}, {"access_token": "abc\r\nBad: header"}]:
            with self.subTest(token=token), self.assertRaises(ValueError):
                self.exchange(token)
        for profile in [{"code": 20004, "data": "Token type is error"}, {"uid": True, "fullname": "ok"},
                        {"uid": 1, "fullname": " "}, {"fullname": "only-name"}]:
            with self.subTest(profile=profile), self.assertRaises(ValueError):
                self.exchange({"access_token": "ok"}, profile)


class ZhihuLinkTests(unittest.TestCase):
    origin = "https://www.goldbach.tech"
    home = "/auth/zhihu"
    callback = "/auth/zhihu/callback"
    gist = "https://gist.github.com/alice/" + "a" * 32

    def setUp(self):
        directory = self.enterContext(tempfile.TemporaryDirectory())
        self.config = {"app_id": "1043", "app_key": "dummy-test-secret"}
        self.app = oauth.ZhihuOAuth(Path(directory) / "identity.sqlite3", self.config)
        self.exchange = self.enterContext(patch.object(oauth, "exchange_profile", return_value={
            "subject": "123", "name": "测试昵称", "avatar_url": "", "profile_url": "",
        }))
        self.verify = self.enterContext(patch.object(oauth, "verify_gist", return_value=(77, "alice")))

    def request(self, method, path, params=None, cookie="", origin=None):
        headers = {"Host": "www.goldbach.tech"}
        if cookie:
            headers["Cookie"] = cookie
        if method == "POST":
            headers["Origin"] = self.origin if origin is None else origin
        return self.app.handle(method, path, params or {}, headers)

    def page(self, cookie=""):
        status, headers, body = self.request("GET", self.home, cookie=cookie)
        self.assertEqual(status, 200)
        token = re.search(r'name="csrf" value="([^"]+)"', body.decode())
        self.assertIsNotNone(token)
        if "Set-Cookie" in headers:
            cookie = headers["Set-Cookie"].split(";", 1)[0]
        self.assertTrue(cookie)
        return cookie, token[1]

    def start(self):
        cookie, csrf = self.page()
        status, headers, _ = self.request("POST", self.home + "/start", {"csrf": csrf}, cookie)
        self.assertEqual(status, 303)
        url = urlsplit(headers["Location"])
        self.assertEqual((url.scheme, url.netloc, url.path), ("https", "openapi.zhihu.com", "/authorize"))
        query = parse_qs(url.query)
        self.assertEqual(query["redirect_uri"], [self.origin + self.callback])
        self.assertEqual(query["app_id"], [self.config["app_id"]])
        self.assertNotIn(self.config["app_key"], headers["Location"])
        self.assertGreaterEqual(len(query["state"][0]), 22)
        return headers.get("Set-Cookie", cookie).split(";", 1)[0], query["state"][0]

    def login(self):
        cookie, state = self.start()
        code = "authorization-code-for-this-session"
        status, headers, body = self.request("GET", self.callback, {"state": state, "authorization_code": code}, cookie)
        self.assertEqual(status, 303)
        self.assertEqual(headers["Location"], self.home)
        self.assertNotIn(code.encode(), body)
        rotated = headers["Set-Cookie"].split(";", 1)[0]
        self.assertNotEqual(rotated, cookie)
        self.exchange.assert_called_once_with(self.config, code)
        self.assertFalse(self.app.public_profiles())
        replay, _, _ = self.request("GET", self.callback, {"state": state, "authorization_code": code}, cookie)
        self.assertGreaterEqual(replay, 400)
        self.assertEqual(self.exchange.call_count, 1)
        return self.page(rotated)

    def test_sponsor_moderation_and_authenticated_header(self):
        from PIL import Image
        import sponsors
        desk = sponsors.DESK
        owner_url = "https://www.zhihu.com/people/cg-22-2"
        self.enterContext(patch.dict("os.environ", {"GOLDBACH_INITIAL_ADMIN_PROFILE": owner_url, "GOLDBACH_INITIAL_ADMIN_UID": ""}))
        self.exchange.return_value.update(name="lifesize", avatar_url="https://picx.zhimg.com/a.jpg")
        user, csrf = self.login()
        head = self.app.account_link({"Host":"www.goldbach.tech","Cookie":user},"zh")
        self.assertIn("设置",head)
        self.assertIn("https://picx.zhimg.com/a.jpg",head)
        self.assertNotIn("设置",self.app.account_link({"Host":"www.goldbach.tech"},"zh"))
        png = io.BytesIO()
        Image.new("RGB",(4,2)).save(png,"PNG")
        url = "https://example.org/research?a=1&b=2"
        upload = {"csrf":csrf,"name":"Example <Org>","logo":png.getvalue(),"website":url}
        self.assertFalse(self.app.can_upload_sponsor({"Host":"www.goldbach.tech"}))
        self.assertTrue(self.app.can_upload_sponsor({"Host":"www.goldbach.tech","Cookie":user}))
        status, _, failure = self.request("POST",desk+"/upload",{**upload,"logo":b"<svg/>"},user)
        self.assertEqual(status, 400)
        self.assertIn("图片无法读取", failure.decode())
        for bad_url in ("javascript:alert(1)", "https://other.org@example.org", "https://127.0.0.1/"):
            self.assertEqual(self.request("POST",desk+"/upload",{**upload,"website":bad_url},user)[0],400)
        self.assertEqual(self.request("POST",desk+"/upload",upload,user,origin="https://invalid.example")[0],403)
        self.assertEqual(self.request("POST",desk+"/upload",upload,user)[0],303)
        self.assertIsNone(sponsors.public_logo(self.app.db,1))
        self.assertNotIn("example.org", sponsors.wall(self.app.db,"zh",""))
        decision = {"csrf":csrf,"id":"1","decision":"approved"}
        self.assertEqual(self.request("POST",desk+"/review",decision,user)[0],403)
        self.exchange.reset_mock()
        self.exchange.return_value.update(subject="456",profile_url=owner_url)
        admin, token = self.login()
        pending = self.request("GET",desk,{"view":"pending"},admin)[2].decode()
        self.assertIn('/sponsor-settings.css',pending)
        self.assertIn('class="status pending"',pending)
        self.assertIn('value="approved"',pending)
        self.assertIn('https://example.org/research?a=1&amp;b=2', pending)
        self.assertEqual(self.request("POST",desk+"/review",{**decision,"csrf":token},admin)[0],303)
        self.assertNotIn('Example &lt;Org&gt;', self.request("GET",desk,{"view":"pending"},admin)[2].decode())
        self.assertIn("Example &lt;Org&gt;",sponsors.wall(self.app.db,"zh",""))
        self.assertIn('href="https://example.org/research?a=1&amp;b=2"', sponsors.wall(self.app.db,"zh",""))
        raw_logo = sponsors.public_logo(self.app.db,1)
        self.assertTrue(raw_logo.startswith(b"\x89PNG"))
        webp_bytes, webp_mime = sponsors.render_public_logo(raw_logo, webp=True)
        self.assertEqual(webp_mime, "image/webp")
        self.assertEqual(webp_bytes[:4], b"RIFF")
        self.assertEqual(webp_bytes[8:12], b"WEBP")
        png_bytes, png_mime = sponsors.render_public_logo(raw_logo, webp=False)
        self.assertEqual(png_mime, "image/png")
        self.assertTrue(png_bytes.startswith(b"\x89PNG"))
        noisy = Image.effect_noise((480, 240), 50).convert("RGBA")
        noisy_buf = io.BytesIO()
        noisy.save(noisy_buf, format="PNG")
        noisy_raw = noisy_buf.getvalue()
        self.assertGreater(len(noisy_raw), 20_480)
        hd_bytes, _ = sponsors.render_public_logo(noisy_raw, webp=True, hd=True)
        sd_bytes, _ = sponsors.render_public_logo(noisy_raw, webp=True, hd=False)
        self.assertEqual(Image.open(io.BytesIO(hd_bytes)).size, (480, 240))
        self.assertEqual(Image.open(io.BytesIO(sd_bytes)).size, (280, 140))
        self.assertIn('loading="lazy" decoding="async"', sponsors.wall(self.app.db,"zh",""))
        self.assertEqual(self.request("POST",desk+"/upload",{**upload,"name":"Second Lab"},user)[0],303)
        self.assertEqual(self.request("POST",desk+"/review",{**decision,"csrf":token,"id":"2"},admin)[0],303)
        sort = {"csrf":token,"original":"1,2","order":"2,1"}
        self.assertNotIn(b'sponsor-sort-list',self.request("GET",desk,{"view":"approved"},user)[2])
        self.assertIn(b'sponsor-sort-list',self.request("GET",desk,{"view":"approved"},admin)[2])
        self.assertEqual(self.request("POST",desk+"/order",{**sort,"csrf":csrf},user)[0],403)
        self.assertEqual(self.request("POST",desk+"/order",{**sort,"order":"1,1"},admin)[0],400)
        self.assertEqual(self.request("POST",desk+"/order",sort,admin)[0],303)
        rendered = sponsors.wall(self.app.db,"zh","")
        self.assertLess(rendered.index("Second Lab"),rendered.index("Example &lt;Org&gt;"))
        self.assertIn("支持机构", rendered)
        colophon_without_logo = sponsors.author_colophon(self.app.db, "zh", "")
        self.assertIn("发起人", colophon_without_logo)
        self.assertIn("@lifesize", colophon_without_logo)
        self.assertIn("联合发起：", colophon_without_logo)
        self.assertIn("<strong>知乎科学</strong>", colophon_without_logo)
        self.assertIn("colophon-sep", colophon_without_logo)
        self.assertNotIn("colophon-x", colophon_without_logo)
        self.assertIn("author-avatar", colophon_without_logo)
        self.assertNotIn("coinitiator-logo", colophon_without_logo)
        origin_note = sponsors.hero_origin_note("zh")
        self.assertIn("由 @lifesize 发起 · 知乎科学联合推动，知乎答主 lifesize 在知乎 AI4S 讨论社群「知乎 研 Club」中发起本次活动。", origin_note)
        self.assertIn("知乎科学持续支持研究者连接、公开讨论与阶段成果传播。", origin_note)
        self.assertIn("知乎 AI Works 入口", origin_note)
        self.assertNotIn("参与知乎公开讨论", origin_note)
        self.assertEqual(sponsors.hero_origin_note("zh", goldbach=False), "")
        sub_colophon = sponsors.author_colophon(self.app.db, "zh", "../../", goldbach=False)
        self.assertIn("@lifesize", sub_colophon)
        self.assertEqual(self.request("POST",desk+"/upload",{**upload,"name":"知乎科学","website":"https://www.zhihu.com/org/zhi-hu-ke-xue"},user)[0],303)
        self.assertEqual(self.request("POST",desk+"/review",{**decision,"csrf":token,"id":"3"},admin)[0],303)
        colophon_with_logo = sponsors.author_colophon(self.app.db, "zh", "")
        self.assertIn('src="sponsors/logo/3.png"', colophon_with_logo)
        self.assertIn('alt="知乎科学"', colophon_with_logo)
        self.assertNotIn("<strong>知乎科学</strong>", colophon_with_logo)
        footer_lockup = sponsors.footer_credit(self.app.db, "zh", "")
        self.assertIn("author-avatar", footer_lockup)
        self.assertIn('src="sponsors/logo/3.png"', footer_lockup)
        self.assertIn("colophon-sep", footer_lockup)
        self.assertNotIn("colophon-x", footer_lockup)
        self.assertIn("知乎科学", sponsors.wall(self.app.db, "zh", ""))
        self.assertEqual(self.request("POST",desk+"/order",sort,admin)[0],409)
        self.assertEqual(self.request("POST",desk+"/review",{**decision,"csrf":token},admin)[0],409)
        self.assertEqual(self.request("POST",desk+"/review",{**decision,"csrf":token,"decision":"withdrawn"},admin)[0],303)
        self.assertIsNone(sponsors.public_logo(self.app.db,1))
        self.assertEqual(self.request("POST",desk+"/logout",{"csrf":token},admin)[0],303)
        self.assertNotIn("设置",self.app.account_link({"Host":"www.goldbach.tech","Cookie":admin},"zh"))

    def test_unrelated_session_missing_or_wrong_state_do_not_exchange(self):
        cookie, state = self.start()
        other, _ = self.page()
        for client, received in [(other, state), ("", state), (cookie, ""), (cookie, "unrelated")]:
            with self.subTest(client=client[:12], has_state=bool(received)):
                status, headers, body = self.request("GET", self.callback, {
                    "authorization_code": "sensitive-test-code", "state": received,
                }, client)
                self.assertGreaterEqual(status, 400)
                self.assertNotIn("sensitive-test-code", str(headers))
                self.assertNotIn(b"sensitive-test-code", body)
        self.exchange.assert_not_called()
        self.assertEqual(self.app.public_profiles(), {})

    def test_browser_link_requires_same_origin_csrf(self):
        cookie, csrf = self.page()
        for origin, token in [("https://other.example", csrf), (self.origin, "bad")]:
            status, _, _ = self.request("POST", self.home + "/start", {"csrf": token}, cookie, origin)
            self.assertGreaterEqual(status, 400)
        self.exchange.assert_not_called()

    def test_publish_only_verified_owner_with_explicit_consent_then_unlink(self):
        cookie, csrf = self.login()
        status, _, _ = self.request("POST", self.home + "/challenge", {"csrf": csrf, "handle": "alice"}, cookie)
        self.assertEqual(status, 303)
        cookie, csrf = self.page(cookie)
        bind = {"csrf": csrf, "gist": self.gist}
        status, _, _ = self.request("POST", self.home + "/bind", bind, cookie)
        self.assertGreaterEqual(status, 400)
        self.assertFalse(self.app.public_profiles())
        bind["public"] = "yes"
        with patch.object(oauth, "verify_gist", side_effect=oauth.GithubProofError("github_proof_mismatch", 422)):
            status, _, _ = self.request("POST", self.home + "/bind", bind, cookie)
            self.assertGreaterEqual(status, 400)
        self.assertFalse(self.app.public_profiles())
        status, _, _ = self.request("POST", self.home + "/bind", bind, cookie)
        self.assertEqual(status, 303)
        self.assertIn("alice", self.app.public_profiles())
        self.verify.assert_called_once()
        cookie, csrf = self.page(cookie)
        status, _, _ = self.request("POST", self.home + "/unlink", {"csrf": csrf}, cookie)
        self.assertEqual(status, 303)
        self.assertFalse(self.app.public_profiles())
