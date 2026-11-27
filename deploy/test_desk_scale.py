"""Run with python -m unittest deploy.test_desk_scale -v (Python 3.11+ and OpenSSL)."""

import gzip
import hashlib
import hmac
import json
import os
import secrets
import shutil
import sqlite3
import ssl
import subprocess
import sys
import tempfile
import threading
import time
import unittest
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from contextlib import closing
from http.client import HTTPSConnection
from pathlib import Path
from urllib.parse import urlencode

from deploy.desk import QUEUE_BATCH, fleet_pass


ROOT = Path(__file__).resolve().parents[1]
SESSIONS = 128
PROBLEMS = json.loads((ROOT / "research/problems.json").read_text(encoding="utf-8"))


class DeskServerTestCase(unittest.TestCase):
    server_setup = ""

    def configure_catalogue(self, folder):
        pass

    def setUp(self):
        folder = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.folder = folder
        self.secret = secrets.token_hex(32).encode()
        (folder / "webhook").write_bytes(self.secret)
        (folder / "china-apnic.txt").write_bytes(b"")
        for source in ("deploy/server.py", "deploy/site.js", "deploy/site.css", "deploy/desk.py", "deploy/reductions.py", "deploy/model-aliases.json", "deploy/agent-icons.svg", "deploy/landau.py", "deploy/presence.py", "deploy/join.txt", "deploy/join-zh.txt",
                       "deploy/zhihu_oauth.py", "deploy/sponsors.py", "deploy/github_identity.py", "deploy/zh.html", "deploy/en.html",
                       "research/gaps.json", "research/problems.json"):
            shutil.copy(ROOT / source, folder)
        self.configure_catalogue(folder)
        openssl = os.environ.get("OPENSSL") or shutil.which("openssl")
        if not openssl and shutil.which("git"):
            git_openssl = Path(shutil.which("git")).parents[1] / "usr/bin/openssl.exe"
            if git_openssl.is_file():
                openssl = str(git_openssl)
        if not openssl:
            self.fail("Install OpenSSL or set OPENSSL to its executable to run the HTTPS scale test")
        subprocess.run([
            openssl, "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-days", "1",
            "-subj", "/CN=localhost", "-addext", "subjectAltName=IP:127.0.0.1",
            "-keyout", "privkey.pem", "-out", "fullchain.pem",
        ], cwd=folder, check=True, capture_output=True)
        self.context = ssl.create_default_context(cafile=str(folder / "fullchain.pem"))

        # Use the production TLS/thread/SQLite handlers with a random loopback port and test-only state.
        launcher = (
            "from server import Server, Handler\n"
            f"{self.server_setup}"
            "Handler.log_request = lambda *args: None\n"
            "with Server(('127.0.0.1', 0), Handler) as server:\n"
            "    print(server.server_port, flush=True)\n"
            "    server.serve_forever()\n"
        )
        self.server = subprocess.Popen(
            [sys.executable, "-B", "-c", launcher], cwd=folder,
            env={**os.environ, "CREDENTIALS_DIRECTORY": str(folder), "STATE_DIRECTORY": str(folder)},
            stdout=subprocess.PIPE, text=True,
        )
        self.addCleanup(self.stop_server)
        self.port = int(self.server.stdout.readline())

    def stop_server(self):
        self.server.terminate()
        self.server.wait(timeout=10)
        self.server.stdout.close()

    def request(self, path, body=None, *, token=None, signed=False, ip=None, ticket=None, expected=200, text=False):
        raw = json.dumps(body).encode() if body is not None else None
        headers = {"Content-Type": "application/json"}
        if token:
            headers["Authorization"] = "Bearer " + token
        if signed:
            headers["X-Goldbach-Signature"] = "sha256=" + hmac.new(self.secret, raw, hashlib.sha256).hexdigest()
        if ip:
            # The production proxy supplies this header to the loopback upstream.
            headers["X-Goldbach-Client-IP"] = ip
        if ticket:
            headers["X-Goldbach-Fleet"] = ticket
        with closing(HTTPSConnection("127.0.0.1", self.port, timeout=45, context=self.context)) as conn:
            conn.request("POST" if raw is not None else "GET", path, body=raw, headers=headers)
            response = conn.getresponse()
            if text:
                self.assertEqual(response.status, expected, path)
                return response.read().decode("utf-8")
            result = (json.loads(gzip.decompress(response.read())) if response.getheader("Content-Encoding") == "gzip"
                      else json.load(response))
            self.assertEqual(response.status, expected, (path, result.get("error")))
            return result


class DeskScaleTest(DeskServerTestCase):
    def test_agent_attribution_across_problem_desks(self):
        for index, path in enumerate(("", "/problems/log-rank")):
            claim = self.request(path + "/api/desk/claim", {"handle": "alice"}, expected=201)
            gap, token = claim["gap"], claim["lease"]["token"]
            agent = {"model": "model-test-v1", "harness": "codex", "harness_version": "1.2.3"}
            submission = {"pr": 40 + index, "head": "a" * 40, "agent": agent}
            self.request(path + "/api/desk/submit", submission, token=token)
            self.request(path + "/api/desk/submit", submission, token=token)
            self.request(path + "/api/desk/submit", {**submission, "agent": {**agent, "model": "other"}}, token=token, expected=409)
            run_id = 500 + index
            self.request("/api/desk/authorize", {"gap": gap["id"], "pr": 40 + index, "head": "a" * 40,
                         "handle": "alice", "run_id": run_id,
                         "statement_sha256": hashlib.sha256(gap["statement"].encode()).hexdigest()}, signed=True)
            record = {"lemma_id": gap["id"], "run_id": run_id, "run_attempt": 1, "verdict": "ACCEPTED",
                      "manifest": {"rests_on": [{"module": gap["module"], "sha256": "a" * 64}], "defs": []}}
            self.request("/api/verdict", record, signed=True)
            self.request("/api/verdict", record, signed=True)
            status = self.request(path + "/api/status")
            with closing(HTTPSConnection("127.0.0.1", self.port, context=self.context)) as conn:
                conn.request("GET", path + "/api/status?view=web-gzip")
                response = conn.getresponse()
                self.assertEqual(response.status, 200)
                self.assertEqual(response.getheader("Content-Encoding"), "gzip")
                compact = json.loads(gzip.decompress(response.read()))
            self.assertEqual(compact["results"], status["results"])
            self.assertEqual(compact["counts"], status["counts"])
            latest = next(g["latest"] for g in compact["gaps"] if g["id"] == gap["id"])
            self.assertNotIn("manifest", latest)
            self.assertEqual(latest["lemma_id"], gap["id"])
            self.assertEqual(status["results"][0]["agent"], {**agent, "source": "self_reported"})
            summary = self.request(path + "/api/records?view=summary&page=1&limit=5")["results"][0]
            self.assertTrue(summary["has_manifest"])
            self.assertNotIn("manifest", summary)
            self.assertEqual(summary["agent"], status["results"][0]["agent"])
            manifest = f"{path}/api/record-manifest?run={run_id}&attempt=1"
            self.assertEqual(self.request(manifest)["manifest"], record["manifest"])
            self.request(manifest[:-1] + "2", expected=404)

            detail = path + "/api/task?" + urlencode({"lemma": gap["id"]})
            self.assertEqual(self.request(detail)["statement"], gap["statement"])
            self.assertEqual(self.request(detail)["cut_reason"], "settled")
            token_query = urlencode({"q": gap["statement"][:40], "lang": "zh", "scope": "all"})
            self.assertIn(gap["id"], self.request(path + "/api/task-search?" + token_query)["ids"])
            other_path = "/problems/log-rank" if not path else ""
            self.request(other_path + "/api/task?" + urlencode({"lemma": gap["id"]}), expected=404)
            listing = self.request(path + "/api/tasks?limit=3")
            self.assertEqual(listing["problem"], "log-rank" if path else "goldbach")
            self.assertLessEqual(len(listing["tasks"]), 3)
            self.assertNotIn(gap["id"], {task["id"] for task in listing["tasks"]})
            self.assertEqual({k: v for k, v in status["desk"]["agent_rankings"].items() if k != "providers"}, {
                "models": [{"name": "model-test-v1", "accepted": 1, "points": 1}],
                "harnesses": [{"name": "codex", "accepted": 1, "points": 1, "icon": "codex"}], "proofs": 1})
            self.assertEqual(status["desk"]["rankings"]["proofs"], 1)
            for lang in ("zh", "en"):
                page = self.request(path + "/?lang=" + lang, text=True)
                self.assertIn('data-ranking-mode="agents"', page)
                guide = self.request(path + "/join" + ("-zh" if lang == "zh" else "") + ".txt", text=True)
                self.assertIn('--model MODEL_ID --harness HARNESS', guide)

    def test_verification_history_pagination(self):
        api = "/api/"
        def publish(run, attempt):
            self.request("/api/verdict", {"lemma_id": "L-goldbach-history", "run_id": run,
                         "run_attempt": attempt, "verdict": "REJECTED", "manifest": None}, signed=True)

        for run in range(100, 113):
            publish(run, 1)
        publish(101, 2)
        first = self.request(api + "records")
        self.assertEqual(len(first["results"]), 12)
        self.assertEqual(first["next"], "101-2")
        self.assertEqual(first["total"], 14)
        publish(113, 1)
        last = self.request(api + "records?before=" + first["next"])
        self.assertEqual([r["run_id"] for r in last["results"]], [101, 100])
        self.assertIsNone(last["next"])
        self.assertEqual(last["total"], 15)
        paged = self.request(api + "records?page=2&limit=5")
        self.assertEqual(paged["page"], 2)
        self.assertEqual(paged["limit"], 5)
        self.assertEqual(paged["total"], 15)
        self.assertEqual(paged["pages"], 3)
        self.assertEqual([r["run_id"] for r in paged["results"]], [108, 107, 106, 105, 104])
        clamped = self.request(api + "records?page=99&limit=5")
        self.assertEqual(clamped["page"], 3)
        self.assertEqual([r["run_id"] for r in clamped["results"]], [103, 102, 101, 101, 100])
        self.assertEqual(self.request("/problems/log-rank/api/records")["results"], [])
        self.request(api + "records?before=invalid", expected=400)
        self.request(api + "records?page=0&limit=5", expected=400)
        self.request(api + "records?page=1&limit=50", expected=400)
        self.request(api + "records?before=101-2&page=1", expected=400)

    def test_page_views_count_only_successful_page_gets(self):
        def total():
            return self.request("/api/presence")["page_views"]

        start = total()
        for path in ("/", "/?lang=zh", "/problems/", "/problems/log-rank/"):
            self.assertIn('data-count="page_views"', self.request(path, text=True))
        self.request("/health")
        self.request("/absent", expected=404)
        with closing(HTTPSConnection("127.0.0.1", self.port, context=self.context)) as conn:
            conn.request("HEAD", "/")
            self.assertEqual(conn.getresponse().status, 200)
        self.assertEqual(total(), start + 4)
        self.assertEqual(total(), start + 4)

    def test_unique_ips_are_shared_by_pages_and_normalized(self):
        get_total = lambda: self.request("/api/presence")["unique_ips"]
        self.assertEqual(get_total(), 0)
        self.request("/", ip="192.0.2.1", text=True)
        self.request("/problems/log-rank/", ip="::ffff:192.0.2.1", text=True)
        self.request("/health", ip="192.0.2.2")
        self.request("/problems/", ip="127.0.0.1", text=True)
        self.assertEqual(get_total(), 1)
        self.request("/problems/", ip="2001:db8::1", text=True)
        self.assertEqual(get_total(), 2)

    def wave(self, pool, mode, label, action, size=SESSIONS):
        ready = threading.Barrier(size, timeout=30)

        def client(i):
            ready.wait()
            return action(i)

        start = time.monotonic()
        results = list(pool.map(client, range(size)))
        print(f"{mode}: {size} {label} in {time.monotonic() - start:.2f}s", flush=True)
        return results

    def test_128_concurrent_public_and_fleet_sessions(self):
        api = "/api/desk/"
        with ThreadPoolExecutor(max_workers=SESSIONS) as pool:
            for mode in ("public", "fleet"):
                with self.subTest(mode=mode):
                    ticket = None
                    if mode == "fleet":
                        ticket = fleet_pass(self.secret, "lab", int(time.time()) + 3600)

                    def claim(i):
                        handle = "lab" if ticket else f"researcher-{i}"
                        ip = "192.0.2.200" if ticket else f"192.0.2.{i + 1}"
                        return self.request(api + "claim", {"handle": handle}, ticket=ticket, ip=ip, expected=201)

                    claims = self.wave(pool, mode, "claims", claim)
                    tokens = [item["lease"]["token"] for item in claims]
                    gaps = {item["gap"]["id"] for item in claims}
                    catalogue = json.loads((ROOT / "research/gaps.json").read_text(encoding="utf-8"))["gaps"]
                    self.assertTrue(gaps <= {entry["id"] for entry in catalogue})
                    self.assertEqual(len(gaps), min(SESSIONS, len(catalogue)))
                    for entry in catalogue:
                        count = sum(item["gap"]["id"] == entry["id"] for item in claims)
                        if not entry.get("parallel"):
                            self.assertLessEqual(count, 1)
                    self.assertEqual(len(set(tokens)), SESSIONS)
                    status = self.request("/api/status")["desk"]
                    self.assertEqual(set(status["assignments"]), gaps)
                    self.assertEqual(status["active"], SESSIONS)
                    if ticket:
                        self.request(api + "claim", {"handle": "lab"}, ticket=ticket, expected=429)
                        self.request(api + "claim", {"handle": "outsider"}, ticket=ticket, expected=401)
                    self.wave(pool, mode, "renewals", lambda i: self.request(api + "beat", {}, token=tokens[i]))
                    self.wave(pool, mode, "submissions", lambda i: self.request(
                        api + "submit", {"pr": i + 1, "head": f"{i + 1:040x}", "agent": {"model": "test-model", "harness": "codex"}}, token=tokens[i],
                    ))
                    pending = []
                    for _ in range(0, SESSIONS, QUEUE_BATCH):
                        page = self.request(api + "pending", {}, signed=True)["pending"]
                        self.assertTrue(0 < len(page) <= QUEUE_BATCH)
                        pending.extend(page)
                    self.assertEqual(len(pending), SESSIONS)
                    self.assertEqual({row["gap"] for row in pending}, gaps)
                    self.assertEqual({row["pr"] for row in pending}, set(range(1, SESSIONS + 1)))
                    self.assertEqual(self.request(api + "pending", {}, signed=True)["pending"], [])
                    self.wave(pool, mode, "returns", lambda i: self.request(
                        api + "release", {"reason": "abandoned"}, token=tokens[i],
                    ))
                    self.assertEqual(self.request("/api/status")["desk"]["active"], 0)

    def test_parallel_problems_keep_independent_leases_and_verdicts(self):
        paths = ["", *(f"/problems/{slug}" for slug in PROBLEMS)]
        landau = "/problems/quadratic-primes"
        milestone = next(g["id"] for g in PROBLEMS["quadratic-primes"]["gaps"]
                         if g.get("lpf_exponent") == "1.324")
        baseline = self.request(landau + "/api/status")["lpf_record"]
        self.assertEqual(baseline["current"]["exponent"], "1.323")
        self.assertIsNone(baseline["verified"])
        with ThreadPoolExecutor(max_workers=len(paths)) as pool:
            claims = list(pool.map(lambda path: self.request(
                path + "/api/desk/claim", {"handle": "alice", "gap": milestone if path == landau else None},
                ip="192.0.2.17", expected=201
            ), paths))
        self.assertEqual(len({claim["gap"]["id"] for claim in claims}), len(paths))
        for i, (path, claim) in enumerate(zip(paths, claims)):
            token = claim["lease"]["token"]
            next_path = paths[(i + 1) % len(paths)]
            self.request(next_path + "/api/desk/beat", {}, token=token, expected=401)
            self.request(path + "/api/desk/submit", {"pr": i + 1, "head": f"{i + 1:040x}", "agent": {"model": "test-model", "harness": "codex"}}, token=token)
        pending = self.request("/api/desk/pending", {}, signed=True)["pending"]
        self.assertEqual({row["gap"] for row in pending}, {claim["gap"]["id"] for claim in claims})

        def finish(i):
            task = claims[i]["gap"]
            run_id = 100 + i
            record = {"lemma_id": task["id"], "run_id": run_id, "run_attempt": 1, "verdict": "ACCEPTED",
                      "manifest": {"rests_on": [{"module": task["module"], "sha256": "a" * 64}], "defs": []}}
            if i:
                self.request("/api/verdict", record, signed=True, expected=409)
            self.request("/api/desk/authorize", {"gap": task["id"], "pr": i + 1, "head": f"{i + 1:040x}",
                         "handle": "alice", "run_id": run_id,
                         "statement_sha256": hashlib.sha256(task["statement"].encode()).hexdigest()}, signed=True)
            self.request("/api/verdict", record, signed=True)
            self.request("/api/verdict", record, signed=True)
        with ThreadPoolExecutor(max_workers=len(paths)) as pool:
            list(pool.map(finish, range(len(paths))))
        for path, claim in zip(paths, claims):
            result = self.request(path + "/api/status")
            self.assertEqual(result["counts"]["accepted"], 1)
            self.assertEqual(result["counts"]["attempts"], 1)
            self.assertEqual(result["desk"]["rankings"]["proofs"], 1)
            self.assertEqual(result["results"][0]["lemma_id"], claim["gap"]["id"])
            if path == landau:
                self.assertEqual(result["lpf_record"]["current"]["exponent"], "1.324")
                self.assertEqual(result["lpf_record"]["current"]["kind"], "lean_accepted")
            else:
                self.assertNotIn("lpf_record", result)

    def test_simultaneous_fleet_claims_and_submissions_across_problems(self):
        paths = ["", *(f"/problems/{slug}" for slug in PROBLEMS)]
        ticket = fleet_pass(self.secret, "lab", int(time.time()) + 3600)
        expected_claims = Counter(paths[i % len(paths)] for i in range(SESSIONS))
        quota = max(1, QUEUE_BATCH // len(paths))

        def claim(i):
            path = paths[i % len(paths)]
            result = self.request(path + "/api/desk/claim", {"handle": "lab"},
                                  ticket=ticket, ip="192.0.2.7", expected=201)
            return path, result["lease"]["token"], result["gap"]["id"]

        with ThreadPoolExecutor(max_workers=SESSIONS) as pool:
            claims = self.wave(pool, f"{len(paths)} problems", "claims", claim)
            self.assertEqual(len({token for _, token, _ in claims}), SESSIONS)
            scopes = {gap: path for path, _, gap in claims}
            for path in paths:
                expected = [gap for owner, _, gap in claims if owner == path]
                status = self.request(path + "/api/status")
                self.assertEqual(len(expected), expected_claims[path])
                self.assertEqual(status["desk"]["active"], len(expected))
                self.assertEqual(set(status["desk"]["assignments"]), set(expected))
                catalogue = {gap["id"] for gap in status["gaps"]}
                self.assertTrue(set(expected) <= catalogue)
                self.assertEqual(len(set(expected)), min(len(expected), len(catalogue)))
            self.wave(pool, f"{len(paths)} problems", "submissions", lambda i: self.request(
                claims[i][0] + "/api/desk/submit", {"pr": i + 1, "head": f"{i + 1:040x}", "agent": {"model": "test-model", "harness": "codex"}}, token=claims[i][1]
            ))
            queued = []
            remaining = expected_claims.copy()
            for _ in range(0, SESSIONS, QUEUE_BATCH):
                batch = self.request("/api/desk/pending", {}, signed=True)["pending"]
                self.assertEqual(len(batch), QUEUE_BATCH)
                per_problem = Counter(scopes[row["gap"]] for row in batch)
                for path in paths:
                    self.assertGreaterEqual(per_problem[path], min(quota, remaining[path]))
                remaining.subtract(per_problem)
                queued.extend((row["pr"], row["gap"]) for row in batch)
            self.assertCountEqual(queued, [(i + 1, gap) for i, (_, _, gap) in enumerate(claims)])
            self.assertEqual(self.request("/api/desk/pending", {}, signed=True)["pending"], [])
            self.wave(pool, f"{len(paths)} problems", "returns", lambda i: self.request(
                claims[i][0] + "/api/desk/release", {"reason": "abandoned"}, token=claims[i][1]
            ))
        for path in paths:
            self.assertEqual(self.request(path + "/api/status")["desk"]["active"], 0)

    def test_log_rank_sources_and_claim_links(self):
        problem = PROBLEMS["log-rank"]
        path = "/problems/log-rank"
        ids = {g["id"] for g in problem["gaps"]}
        self.assertEqual(ids, {t["id"] for step in problem["roadmap"] for t in step["tasks"]})
        for lang, suffix in (("en", ""), ("zh", "-zh")):
            self.assertIn(f'log-rank/?lang={lang}', self.request(f"/problems/?lang={lang}", text=True))
            page = self.request(f"{path}/?lang={lang}", text=True)
            for stage in problem["roadmap"]:
                key = stage.get("route_id") or stage["route_source"]
                self.assertIn(f'data-program="{key}"', page)
                self.assertIn(f'id="track-{key}"', page)
            guide = self.request(f"{path}/join{suffix}.txt", text=True)
            for material in problem["materials"]:
                self.assertIn(material["url"], page)
                self.assertIn(material["url"], guide)
            self.assertIn("claim --problem log-rank", guide)
            for task in ids:
                self.assertIn(f'data-roadmap-task="{task}"', page)

    def test_directory_counts_and_scoped_join_guides(self):
        slug, problem = next(iter(PROBLEMS.items()))
        path = f"/problems/{slug}"
        total = len(problem["gaps"])
        directory = self.request("/problems/?lang=en", text=True)
        self.assertIn(f"Lean verified 0/{total} · {total} available", directory)
        claim = self.request(path + "/api/desk/claim", {"handle": "reader", "gap": problem["gaps"][0]["id"]},
                             ip="192.0.2.11", expected=201)
        gap = next(g for g in self.request(path + "/api/status")["gaps"] if g["id"] == claim["gap"]["id"])
        self.assertEqual(claim["route_id"], gap["route_id"])
        self.assertIn(f"Lean verified 0/{total} · {total} available",
                      self.request("/problems/?lang=en", text=True))
        self.assertIn(f"Lean 已核验 0/{total} · {total} 条可领取",
                      self.request("/problems/?lang=zh", text=True))
        for lang, suffix in (("en", ""), ("zh", "-zh")):
            gap = problem["gaps"][0]["id"]
            title = next((stage[lang][0] for stage in problem["roadmap"]
                          if any(task["id"] == gap for task in stage["tasks"])),
                         "未分路线的命题" if lang == "zh" else "Unassigned tasks")
            directory = self.request(f"/problems/?lang={lang}", text=True)
            self.assertIn(("进行中 · " if lang == "zh" else "In progress · ") + title, directory)
            page = self.request(f"{path}/?lang={lang}", text=True)
            for task in problem["gaps"]:
                self.assertIn(f'data-roadmap-task="{task["id"]}"', page)
            guide = self.request(f"{path}/join{suffix}.txt", text=True)
            self.assertIn(f"python tools/goldbach.py claim --problem {slug}\n", guide)
            self.assertNotIn("python tools/goldbach.py claim\n", guide)
            self.assertIn(f"{path}/?lang={lang}#records", guide)
            goldbach_guide = self.request(f"/join{suffix}.txt", text=True)
            self.assertIn("python tools/goldbach.py claim", goldbach_guide)
            self.assertNotIn(f"--problem {slug}", goldbach_guide)

    def test_rankings_pagination_and_board_initial_slice(self):
        with closing(sqlite3.connect(self.folder / "verdicts.sqlite3")) as conn:
            for i in range(18):
                handle = f"prover{i:02d}"
                gap = f"g{i:02d}"
                model = f"gpt-6.{i:02d}"
                conn.execute(
                    """
                    INSERT INTO goldbach_leases (
                        token_hash, gap, statement_sha256, handle, ip_key, claimed_at,
                        expires_at, absolute_expires_at, run_id, finished_at, verdict,
                        points, model, harness, agent_reported
                    ) VALUES (?, ?, 'hash', ?, 'network', 1, 2, 3, ?, ?, 'ACCEPTED', ?, ?, 'codex', 1)
                    """,
                    (f"tok-{i}", gap, handle, 100 + i, int(time.time()) - 10, 100 - i, model),
                )
            conn.commit()

        with closing(HTTPSConnection("127.0.0.1", self.port, context=self.context)) as conn:
            conn.request("GET", "/api/status?view=board-gzip")
            response = conn.getresponse()
            self.assertEqual(response.status, 200)
            board = json.loads(gzip.decompress(response.read()))
        self.assertEqual(len(board["desk"]["rankings"]["all_time"]), 12)
        self.assertEqual(board["desk"]["rankings"]["all_time_total"], 18)
        self.assertEqual(len(board["desk"]["agent_rankings"]["models"]), 12)
        self.assertEqual(board["desk"]["agent_rankings"]["totals"]["models"], 18)
        index = self.request("/api/status?view=board-index-gzip")
        delta = self.request("/api/status?view=board-index-delta-gzip")
        self.assertEqual(index["counts"], board["counts"])
        self.assertEqual(index["tracks"], board["tracks"])
        self.assertEqual(index["desk"]["rankings"], board["desk"]["rankings"])
        self.assertNotIn("tracks", delta)
        self.assertEqual([g["id"] for g in index["gaps"]], [g["id"] for g in board["gaps"]])
        self.assertIn("statement", board["gaps"][0])
        self.assertIn("plain_statement", index["gaps"][0])
        self.assertNotIn("plain_statement", delta["gaps"][0])
        for gap in index["gaps"] + delta["gaps"]:
            self.assertFalse({"statement", "brief", "source", "file", "imports", "cuts", "assembly"} & gap.keys())

        page1 = self.request("/api/rankings?mode=all_time&offset=0&limit=12")
        self.assertEqual(len(page1["items"]), 12)
        self.assertEqual(page1["total"], 18)
        self.assertTrue(page1["has_more"])
        self.assertEqual(page1["items"][0]["handle"], "prover00")

        page2 = self.request("/api/rankings?mode=all_time&offset=12&limit=12")
        self.assertEqual(len(page2["items"]), 6)
        self.assertFalse(page2["has_more"])
        self.assertEqual(page2["items"][0]["handle"], "prover12")

        models_p2 = self.request("/api/rankings?mode=models&offset=12&limit=10")
        self.assertEqual(len(models_p2["items"]), 6)
        self.assertFalse(models_p2["has_more"])

        self.request("/api/rankings?mode=invalid", expected=400)
        self.request("/api/rankings?mode=all_time&limit=99", expected=400)

        models_api = self.request("/api/models?q=glm")
        self.assertTrue(any(m["id"] == "glm-5.4" and m["provider"] == "Z.ai" for m in models_api["models"]))
        self.assertIn("providers", models_api)
        self.assertIn("harnesses", models_api)
        models_paged = self.request("/api/models?offset=10&limit=10")
        self.assertEqual(len(models_paged["models"]), 10)
        self.assertNotIn("providers", models_paged)
        self.request("/api/models?unknown=1", expected=400)
        self.request("/api/models?limit=101", expected=400)

        with closing(HTTPSConnection("127.0.0.1", self.port, context=self.context)) as conn:
            conn.request("GET", "/agent-icons.svg", headers={"Accept-Encoding": "gzip"})
            response = conn.getresponse()
            self.assertEqual(response.status, 200)
            self.assertEqual(response.headers.get("Content-Type"), "image/svg+xml")
            sprite_svg = gzip.decompress(response.read()).decode("utf-8")
            self.assertIn('id="brand-nex-agi"', sprite_svg)
            self.assertIn('id="brand-antigravity"', sprite_svg)
            self.assertIn('id="brand-tool-other"', sprite_svg)


class FullStatusTransferTest(DeskServerTestCase):
    server_setup = (
        "import server\n"
        "server.FULL_STATUS_BURST_BYTES = 1\n"
        "server.FULL_STATUS_MIN_BYTES = 1\n"
        "server.FULL_STATUS_REFILL_PER_SECOND = 1e-8\n"
    )

    def test_only_limit_full_body_transfers(self):
        headers = {"Accept-Encoding": "gzip", "X-Goldbach-Client-IP": "1.1.1.1"}
        with closing(HTTPSConnection("127.0.0.1", self.port, context=self.context)) as conn:
            conn.request("GET", "/api/status", headers=headers)
            response = conn.getresponse()
            self.assertEqual(response.status, 200)
            etag = response.getheader("ETag")
            self.assertIn("statement", json.loads(gzip.decompress(response.read()))["gaps"][0])

            conn.request("GET", "/api/status", headers={**headers, "If-None-Match": etag})
            response = conn.getresponse()
            self.assertEqual(response.status, 304)
            self.assertEqual(response.read(), b"")

            conn.request("GET", "/api/status", headers=headers)
            response = conn.getresponse()
            self.assertEqual(response.status, 429)
            self.assertGreater(int(response.getheader("Retry-After")), 0)
            self.assertIn("/api/tasks", json.load(response)["error"])

            conn.request("GET", "/api/status?view=board-index-gzip", headers=headers)
            response = conn.getresponse()
            self.assertEqual(response.status, 200)
            self.assertNotIn("statement", json.loads(gzip.decompress(response.read()))["gaps"][0])


if __name__ == "__main__":
    unittest.main()
