"""Opt-in kernel replay uses the repository's pinned Lean and a fresh TLS/SQLite desk."""
import base64
import hashlib
import json
import os
import subprocess
import sys
import tempfile
from concurrent.futures import ThreadPoolExecutor
from contextlib import chdir, redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import Mock, patch
from unittest import skipUnless

from deploy.test_desk_scale import DeskServerTestCase, ROOT

sys.path.insert(0, str(ROOT / "deploy/jenkins"))
from tools import goldbach as cli
from assemble import prepare_assembly
from github_revision import REPO
from prepare_proof import prepare
from verdict_manifest import module_path
from verify_proof import ProofRejected, mode_for, verifier_manifest

DESK = "/api/desk/"
PARENT = "L-goldbach-cut-integration"
NEGATIVE = PARENT + "-negative"
OTHER = PARENT + "-other"
P = "∀ k : ℕ, 0 + k = k"
A = "∀ n : ℕ, n = 0"
B = "∀ n : ℕ, n + 0 = n"
C = "∀ n : ℕ, n = n"


class CutFlow(DeskServerTestCase):
    def configure_catalogue(self, folder):
        data = json.loads((folder / "gaps.json").read_bytes())
        root = {**data["gaps"][0], "id": PARENT, "statement": P, "parallel": True,
                "module": "Conjectures.Fixtures.Parent", "file": "lean/Conjectures/Fixtures/Parent.lean",
                "reductions": True}
        self.disabled = data["gaps"][0]["id"]
        data["gaps"].append(root)
        for key, statement, name in ((NEGATIVE, f"¬ ({P})", "Negative"), (OTHER, "True", "Other")):
            data["gaps"].append({**root, "id": key, "statement": statement,
                                 "module": "Conjectures.Fixtures." + name,
                                 "file": f"lean/Conjectures/Fixtures/{name}.lean"})
        (folder / "gaps.json").write_text(json.dumps(data))
        self.published = folder
        self.i = 0

    def submit_task(self, ident, kind, handle, proof, *, rejected=False, defer=False):
        self.i += 1
        i = self.i
        ip = f"10.5.{i}.1"
        receipt = self.request(DESK + "claim", {"gap": ident, "kind": kind, "handle": handle}, ip=ip, expected=201)
        gap, token = receipt["gap"], receipt["lease"]["token"]
        self.assertEqual(receipt["kind"], kind)
        if gap["module"].startswith("Conjectures.Cuts."):
            frozen = self.request(DESK + "task?module=" + gap["module"])["gap"]
            self.assertEqual(frozen, {key: value for key, value in gap.items() if key != "points"})
        if kind == "cut":
            self.assertEqual(gap["points"], 1)
        else:
            self.assertGreaterEqual(gap["points"], 1)
        self.request(DESK + "beat", {}, token=token)
        head = f"{i:040x}"
        submission = {"pr": i, "head": head, "agent": {"model": "test", "harness": "codex"}}
        self.request(DESK + "submit", submission, token=token)
        authorization = dict(submission, gap=ident, handle=handle, kind=kind, module=gap["module"],
                             run_id=i, statement_sha256=hashlib.sha256(gap["statement"].encode()).hexdigest())
        self.request(DESK + "authorize", dict(authorization, head="f" * 40), signed=True, expected=409)
        self.request(DESK + "authorize", authorization, signed=True)
        if self.native:
            try:
                manifest = self.replay(gap, kind, proof)
            except ProofRejected:
                if not rejected:
                    raise
                manifest = None
        else:
            manifest = None if rejected else {"rests_on": [{"module": gap["module"], "sha256": head.zfill(64)}],
                                              "defs": [], **({"children": proof} if kind == "cut" else {})}
        self.assertEqual(manifest is None, rejected)
        verdict = dict(lemma_id=ident, run_id=i, run_attempt=1, head_sha=head, kind=kind,
                       module=gap["module"], manifest=manifest, verdict="REJECTED" if rejected else "ACCEPTED")
        self.request("/api/verdict", dict(verdict, head_sha="f" * 40), signed=True, expected=409)
        def deliver():
            with ThreadPoolExecutor(max_workers=2) as threads:
                list(threads.map(lambda _: self.request("/api/verdict", verdict, signed=True), range(2)))
        if defer:
            return deliver
        deliver()
        return gap, manifest

    def replay(self, gap, kind, value):
        module = gap["module"]
        if kind == "cut":
            binders = " ".join(f"(h{i} : {p})" for i, p in enumerate(value))
            declaration = f"{binders} : ({gap['statement']}) := Nat.zero_add"
        else:
            declaration = value
        annotations = "-- child 1 zh: 自然数性质\n-- child 1 en: Natural number property\n" if kind == "cut" else ""
        source = f"import Mathlib.Data.Nat.Basic\n{annotations}\ntheorem {module} {declaration}\n"
        encoded = source.encode()
        blob = hashlib.sha1(f"blob {len(encoded)}\0".encode() + encoded).hexdigest()
        head, tree = f"{self.i:040x}", "f" * 40
        pr = {"base": {"ref": "main", "repo": {"full_name": REPO.split("/repos/")[1]}, "sha": "e" * 40},
              "head": {"sha": head}, "state": "open", "changed_files": 1, "user": {"login": "tester"}}
        responses = {
            f"/pulls/{self.i}": pr,
            f"/pulls/{self.i}/files?per_page=2": [{"filename": gap["file"], "status": "added", "sha": blob}],
            f"/git/commits/{head}": {"sha": head, "tree": {"sha": tree}},
            f"/git/trees/{tree}?recursive=1": {"truncated": False, "tree": [
                {"path": gap["file"], "type": "blob", "mode": "100644", "sha": blob, "size": len(encoded)}]},
            f"/git/blobs/{blob}": {"sha": blob, "size": len(encoded), "encoding": "base64",
                                   "content": base64.b64encode(encoded).decode()},
        }
        app = Mock()
        app.request.side_effect = lambda method, path: responses[path.removeprefix(REPO)]
        def native_guard(base, work, operation, *args):
            paths = [a.replace("/input", str(work)).replace("/base", str(base)) for a in args]
            subprocess.run(["node", ROOT / ".github/scripts/outside-guard.mjs", operation, *paths],
                           check=True, stdout=subprocess.DEVNULL)
        with tempfile.TemporaryDirectory() as directory, patch("prepare_proof.guard", native_guard), patch(
                "prepare_proof.os.chown"), patch.dict(os.environ, {
                    "GOLDBACH_DESK_URL": f"https://127.0.0.1:{self.port}/api/desk",
                    "SSL_CERT_FILE": str(self.published / "fullchain.pem") }):
            work = Path(directory)
            self.assertEqual(prepare(app, self.i, head, ROOT, work), gap["file"])
            self.assertEqual((work / "task.kind").read_text(), kind)
            self.assertEqual((work / "gap.id").read_text().strip(), gap["id"])
            self.assertEqual((work / "statement.txt").read_text(), gap["statement"])
            self.assertEqual((work / "proof.lean").read_text(), source)
            return self.compile(module, source, gap["statement"], mode_for(work))

    def compile(self, module, source, statement, mode):
        project = ROOT / "lean"
        path = self.snapshot / "lean" / module_path(module)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source)
        out = self.output / Path(module_path(module)).with_suffix(".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run([self.lean, "--root=" + str(self.snapshot / "lean"), "-o", out, path], env=self.env,
                       cwd=project, check=True, timeout=240, stdout=subprocess.DEVNULL)
        frozen = self.snapshot / "statement.txt"
        frozen.write_text(statement)
        result = subprocess.run([project / ".lake/build/bin/checklemma", module, frozen, mode],
                                env=self.env, cwd=project, stdout=subprocess.PIPE, text=True, timeout=1200)
        def read(name):
            relative = Path(module_path(name))
            path = self.snapshot / "lean" / relative
            return (path if path.exists() else project / relative).read_bytes()
        return verifier_manifest(result, module, source.encode(), read, mode)

    def exercise(self, native):
        self.native = native
        self.request(DESK + "claim", {"gap": self.disabled, "handle": "x", "kind": "cut"}, expected=409)
        _, first = self.submit_task(PARENT, "cut", "split-one", [A, B])
        _, second = self.submit_task(PARENT, "cut", "split-two", [C, B])
        def gaps():
            return {g["id"]: g for g in self.request("/api/status")["gaps"]}
        board = gaps()
        left, right = [c["children"] for c in board[PARENT]["cuts"]]
        self.assertEqual(self.request(f"/api/task?lemma={PARENT}")["cuts"], board[PARENT]["cuts"])
        child = left[0]
        self.assertEqual(self.request(f"/api/task?lemma={child}")["statement"], board[child]["statement"])
        delta = self.request("/api/status?view=board-index-delta-gzip")
        child_row = next(row for row in delta["gaps"] if row["id"] == child)
        self.assertEqual(child_row["plain_statement"], board[child]["plain_statement"])
        self.assertNotIn("statement", child_row)
        self.assertEqual(left[1], right[1])
        a, b, c = left[0], left[1], right[0]
        self.assertEqual(board[a]["statement"], first["children"][0])
        self.assertEqual(board[c]["statement"], second["children"][0])
        if native:
            self.assertEqual(board[a]["plain_statement"]["en"], "Natural number property")
            self.assertTrue(board[a]["cut_origin"]["contributor_wording"])
        self.assertTrue(board[b]["takes_cuts"])
        self.assertEqual(board[b]["depth"], 1)
        self.assertEqual(board[PARENT]["reductions_live"], 2)
        self.submit_task(a, "refute", "unsuccessful", ": True := True.intro", rejected=True)
        self.assertNotIn("refutation", gaps()[a])
        self.submit_task(a, "refute", "counterexample",
                         f": ¬ ({board[a]['statement']}) := by\n  intro h\n  have bad := h 1\n  omega")
        board = gaps()
        self.assertEqual(board[a]["refutation"]["handle"], "counterexample")
        self.assertTrue(board[a]["resolved"])
        self.assertIsNone(board[a]["points"])
        rankings = self.request("/api/status")["desk"]["rankings"]["all_time"]
        scores = {r["handle"]: (r["accepted"], r["points"], r.get("cuts", 0)) for r in rankings}
        self.assertEqual(scores, {"counterexample": (1, 1, 0), "split-one": (0, 1, 1), "split-two": (0, 1, 1)})
        self.request(DESK + "claim", {"gap": a, "kind": "prove", "handle": "late"}, expected=409)
        self.assertEqual([x["status"] for x in board[PARENT]["cuts"]], ["refuted", "live"])
        self.assertFalse(board[PARENT]["proved"])
        self.submit_task(b, "prove", "shared-proof", f": ({board[b]['statement']}) := by intro n; rfl")
        self.assertIsNone(self.request(DESK + "assembly-next", {}, signed=True)["plan"])
        self.submit_task(c, "prove", "last-proof", f": ({board[c]['statement']}) := by intro n; rfl")
        plan = self.request(DESK + "assembly-next", {}, signed=True)["plan"]
        self.assertEqual([p["handle"] for p in plan["proof"]["premises"]], ["last-proof", "shared-proof"])
        self.assertEqual(plan["proof"]["handle"], "split-two")
        self.assertFalse(gaps()[PARENT]["proved"])
        return plan

    def test_desk_flow(self):
        self.exercise(False)

    def test_catalogued_negative_proof_settles_original_and_blocks_dependent_cuts(self):
        self.native = False
        self.submit_task(PARENT, "cut", "split-original", [A, B])
        self.submit_task(OTHER, "cut", "split-other", [P, B])
        late = self.submit_task(OTHER, "cut", "late-cut", [P, C], defer=True)
        self.submit_task(NEGATIVE, "prove", "legacy-refuter", "")
        late()
        status = self.request("/api/status")
        gaps = {g["id"]: g for g in status["gaps"]}
        self.assertTrue(gaps[NEGATIVE]["proved"])
        self.assertTrue(gaps[PARENT]["resolved"])
        self.assertFalse(gaps[PARENT]["proved"] or gaps[PARENT]["takes_cuts"])
        self.assertIsNone(gaps[PARENT]["points"])
        self.assertEqual([r["status"] for r in gaps[PARENT]["cuts"]], ["superseded"])
        self.assertEqual([r["status"] for r in gaps[OTHER]["cuts"]], ["refuted", "refuted"])
        scores = {r["handle"]: r["points"] for r in status["desk"]["rankings"]["all_time"]}
        self.assertEqual(scores, {"legacy-refuter": 1, "split-original": 1, "split-other": 1})
        self.request(DESK + "claim", {"gap": PARENT, "handle": "late"}, expected=409)

    def test_refuted_cut_cancels_only_its_exclusive_work(self):
        self.native = False
        self.submit_task(PARENT, "cut", "bad-route", [A, B, "Exclusive"])
        self.submit_task(PARENT, "cut", "good-route", [B, C])
        before = {g["id"]: g for g in self.request("/api/status")["gaps"]}
        first, second = before[PARENT]["cuts"]
        bad, shared, exclusive = first["children"]
        self.submit_task(bad, "refute", "refuter", f"¬ ({A})")
        after = {g["id"]: g for g in self.request("/api/status")["gaps"]}
        self.assertEqual([cut["status"] for cut in after[PARENT]["cuts"]], ["refuted", "live"])
        self.assertTrue(after[exclusive]["claims_closed"])
        self.assertFalse(after[shared].get("claims_closed", False))
        self.request(DESK + "claim", {"gap": exclusive, "handle": "late"}, expected=409)
        self.request(DESK + "claim", {"gap": PARENT, "handle": "direct"}, expected=201)

    def test_limits_inheritance_and_reuse(self):
        self.native = False
        known = json.loads((self.published / "gaps.json").read_bytes())["gaps"][0]
        self.submit_task(PARENT, "cut", "c1", [A, known["statement"]])
        self.submit_task(PARENT, "cut", "c2", [A, B])
        self.submit_task(PARENT, "cut", "duplicate", [B, A])
        overflow = self.submit_task(PARENT, "cut", "overflow", ["D", "E"], defer=True)
        self.submit_task(PARENT, "cut", "c3", [A, C])
        overflow()
        gaps = {g["id"]: g for g in self.request("/api/status")["gaps"]}
        cuts = gaps[PARENT]["cuts"]
        self.assertEqual(cuts[2]["reason"], "duplicate_cut")
        self.assertEqual(cuts[3]["reason"], "cut_limit")
        self.assertFalse(cuts[3]["children"])
        self.assertEqual(gaps[PARENT]["reductions_live"], 3)
        self.assertEqual([cut.get("points", 0) for cut in cuts], [1, 1, 0, 0, 1])
        rankings = self.request("/api/status")["desk"]
        for period in ("hour", "all_time"):
            self.assertEqual({r["handle"]: (r["accepted"], r["points"], r["cuts"])
                              for r in rankings["rankings"][period]}, {"c1": (0, 1, 1), "c2": (0, 1, 1), "c3": (0, 1, 1)})
        self.assertEqual(rankings["rankings"]["proofs"], 0)
        for dimension in ("models", "harnesses", "providers"):
            self.assertEqual([(r["accepted"], r["points"], r["cuts"])
                              for r in rankings["agent_rankings"][dimension]], [(0, 3, 3)])
        self.assertEqual(gaps[PARENT]["cut_reason"], "cut_limit")
        self.assertEqual(self.request(DESK + "claim", {"gap": PARENT, "handle": "full", "kind": "cut"},
                                      expected=409)["error"], "cut_limit")
        a, reused = cuts[0]["children"]
        self.assertEqual(reused, known["id"])
        self.assertFalse(gaps[reused]["takes_cuts"])
        self.submit_task(a, "cut", "recursive", ["X", "Y"])
        self.submit_task(a, "cut", "cycle", [P, "Z"])
        board = self.request("/api/status?view=board-delta-gzip")
        by_id = {g["id"]: g for g in board["gaps"]}
        self.assertEqual(by_id[a]["cuts"][1]["reason"], "cyclic_cut")
        for child in by_id[a]["cuts"][0]["children"]:
            self.assertEqual(by_id[child]["depth"], 2)
            self.assertEqual(by_id[child]["cut_reason"], "cut_depth_limit")

        self.submit_task(PARENT, "prove", "first-proof", P)
        scores = {r["handle"]: r for r in self.request("/api/status")["desk"]["rankings"]["all_time"]}
        self.assertEqual(scores["first-proof"]["accepted"], 1)
        self.assertNotIn("cuts", scores["first-proof"])
        self.assertEqual(scores["c1"]["points"], 1)

    def test_cli_receipt_and_templates(self):
        for kind in ("cut", "refute"):
            with self.subTest(kind=kind), tempfile.TemporaryDirectory() as directory, chdir(directory):
                subprocess.run(["git", "init", "-q"], check=True)
                Path("research").mkdir()
                Path("research/gaps.json").write_bytes((self.published / "gaps.json").read_bytes())
                subprocess.run(["git", "add", "research"], check=True)
                subprocess.run(["git", "-c", "user.name=test", "-c", "user.email=test@example.org",
                                "commit", "-qm", "catalogue"], check=True)
                state = Path(".git/goldbach-lease.json")
                with patch.object(cli, "authenticated_login", return_value="cli-user"), patch.object(
                        cli, "SITE", f"https://127.0.0.1:{self.port}"), patch.dict(
                        os.environ, {"SSL_CERT_FILE": str(self.published / "fullchain.pem")}), redirect_stdout(StringIO()):
                    cli.claim(state, PARENT, "goldbach", kind)
                    receipt = json.loads(state.read_bytes())
                    gap = receipt["gap"]
                    source = Path(gap["file"]).read_text(encoding="utf-8")
                    self.assertIn(gap["module"], source)
                    self.assertIn(("¬ " if kind == "refute" else "") + "(" + P + ")", source)
                    self.assertEqual(receipt["kind"], kind)
                    self.assertEqual(cli.current_branch(), receipt["branch"])
                    self.assertIn("expires_at", cli.desk("beat", {}, receipt["token"]))
                    cli.desk("release", {"reason": "statement_seems_false"}, receipt["token"])
                self.assertFalse(any(g.get("refutation") for g in self.request("/api/status")["gaps"] if g["id"] == PARENT))

    @skipUnless(os.environ.get("GOLDBACH_TEST_LEAN") == "1", "requires pinned Lean and built mathlib cache")
    def test_kernel_flow(self):
        self.snapshot = Path(self.enterContext(tempfile.TemporaryDirectory()))
        self.output = self.snapshot / "oleans"
        project = ROOT / "lean"
        def lake(*args):
            return subprocess.check_output(["lake", "env", *args], cwd=project, text=True).strip()
        self.lean = lake("which", "lean")
        self.env = {**os.environ, "LEAN_PATH": str(self.output) + os.pathsep + lake("printenv", "LEAN_PATH")}
        plan = self.exercise(True)
        with tempfile.TemporaryDirectory() as directory:
            work = Path(directory)
            leaf = self.snapshot / "lean" / module_path(plan["proof"]["premises"][0]["module"])
            saved = leaf.read_bytes()
            leaf.write_bytes(saved + b"\n")
            with self.assertRaisesRegex(ValueError, "differs"):
                prepare_assembly(plan, self.snapshot, work)
            leaf.write_bytes(saved)
            key, file, source = prepare_assembly(plan, self.snapshot, work)
            subprocess.run(["node", ROOT / ".github/scripts/outside-guard.mjs", "assembly-closure",
                            self.snapshot, work / "imports.json", file, work], check=True, stdout=subprocess.DEVNULL)
            self.assertEqual(set((work / "outside-build-order.txt").read_text().splitlines()), {
                plan["proof"]["module"], *(p["module"] for p in plan["proof"]["premises"])})
            module = (work / "pr.module").read_text()
            manifest = self.compile(module, source, plan["statement"], "check")
        bad = "Conjectures.Cuts.BadCut"
        with self.assertRaisesRegex(ProofRejected, "reduce-shape"):
            self.compile(bad, f"import Mathlib.Data.Nat.Basic\ntheorem {bad} (h : True) : ({P}) := Nat.zero_add\n",
                         P, "reduce")
        cast = "Conjectures.Cuts.CoercionCut"
        premise = "let r := fun x : ℕ => Nat.floor ((x : ℝ) ^ (1/3 : ℝ)); ∀ x : ℕ, r x ≤ x"
        accepted = self.compile(cast, f"import Mathlib\ntheorem {cast} : ({premise}) → ({B}) → ({P}) := by\n"
                                      "  intro _ _ n; exact Nat.zero_add n\n", P, "reduce")
        self.assertEqual(len(accepted["children"]), 2)
        self.assertIn("ℝ", accepted["children"][0])
        result = dict(parent=PARENT, run=plan["run"], plan_hash=key, source=source, manifest=manifest)
        self.request(DESK + "assembly-complete", dict(result, plan_hash="a" * 64), signed=True, expected=409)
        for _ in range(2):
            self.request(DESK + "assembly-complete", result, signed=True)
        parent = next(g for g in self.request("/api/status")["gaps"] if g["id"] == PARENT)
        self.assertTrue(parent["proved"])
        self.assertEqual(parent["assembly"]["proof"], plan["proof"])
        self.assertEqual([c["status"] for c in parent["cuts"]], ["refuted", "completed"])
        self.assertIsNone(self.request(DESK + "assembly-next", {}, signed=True)["plan"])
