import hashlib
import json
import sqlite3
import unittest
from tempfile import TemporaryDirectory
from pathlib import Path
from unittest.mock import MagicMock, Mock, patch

from merge_proofs import REPO, SkipMerge, drain, git_blob, merge


class MergeProofTests(unittest.TestCase):
    head = "1" * 40
    main = "2" * 40
    merged = "3" * 40
    module = "PEqualNP.Outside.L_test"
    file = "lean/PEqualNP/Outside/L_test.lean"
    proof = b"verified proof bytes"

    def setUp(self):
        root = Path(self.enterContext(TemporaryDirectory()))
        self.base = root / "base"
        research = self.base / "research"
        research.mkdir(parents=True)
        gap = {"id": "L-test", "file": self.file, "module": self.module}
        (research / "gaps.json").write_text(json.dumps({"gaps": [gap]}))
        (research / "problems.json").write_text("{}")
        self.record = {
            "lemma_id": gap["id"], "head_sha": self.head, "verdict": "ACCEPTED",
            "manifest": {"rests_on": [
                {"module": self.module, "sha256": hashlib.sha256(self.proof).hexdigest()},
            ], "defs": []},
        }
        self.pr = {"state": "open", "draft": False, "mergeable": True, "merged": False, "changed_files": 1,
                   "head": {"sha": self.head},
                   "base": {"ref": "main", "sha": self.main, "repo": {"full_name": REPO.removeprefix("/repos/")}}}

    def test_merge_uses_verified_head_and_squash(self):
        app = Mock()
        app.request.side_effect = [[{"filename": self.file, "status": "added"}],
                                   {"merged": True, "sha": self.merged}]
        # GitHub may still be computing mergeability. The SHA-bound merge endpoint
        # can decide after the worker has checked the files and dependency hashes.
        with patch("merge_proofs.pull_request", return_value=self.pr | {"mergeable": None}), \
             patch("merge_proofs.verify_dependency"), \
             patch("merge_proofs.metadata", return_value={"sha": git_blob(self.proof)}), \
             patch("merge_proofs.proven_content", return_value=self.proof):
            self.assertEqual(merge(app, 55, self.head, self.record, self.base),
                             (self.merged, self.file, self.proof))
        app.request.assert_called_with("PUT", REPO + "/pulls/55/merge",
                                       {"sha": self.head, "merge_method": "squash"})

    def test_changed_head_and_extra_files_never_merge(self):
        for pr, extra_files in ((self.pr | {"head": {"sha": self.merged}}, []),
                                (self.pr | {"changed_files": 2}, [{"filename": self.file},
                                                                {"filename": "lakefile.toml"}])):
            with self.subTest(pr=pr):
                app = Mock()
                app.request.return_value = extra_files
                with patch("merge_proofs.pull_request", return_value=pr), self.assertRaises(SkipMerge):
                    merge(app, 55, self.head, self.record, self.base)
                self.assertTrue(all(call.args[0] == "GET" for call in app.request.call_args_list))

    def test_only_delivered_official_success_enters_queue_once(self):
        db = sqlite3.connect(":memory:")
        self.addCleanup(db.close)
        db.executescript("""
            CREATE TABLE ci_jobs (id, pr, sha, kind);
            CREATE TABLE desk_runs (job_id, run_id);
            CREATE TABLE desk_outbox (run, attempt, payload, delivered);
            CREATE TABLE jenkins_dispatches (job_id, result);
        """)
        for number, kind, verdict, delivered, result in (
            (1, "authoritative", "ACCEPTED", 1, "SUCCESS"),
            (2, "authoritative", "ACCEPTED", 0, "SUCCESS"),
            (3, "advisory", "ACCEPTED", 1, "SUCCESS"),
            (4, "authoritative", "REJECTED", 1, "FAILURE"),
            (5, "authoritative", "ACCEPTED", 1, "ABORTED"),
        ):
            db.execute("INSERT INTO ci_jobs VALUES (?, ?, ?, ?)", (number, number + 50, self.head, kind))
            db.execute("INSERT INTO desk_runs VALUES (?, ?)", (number, number))
            db.execute("INSERT INTO desk_outbox VALUES (?, 1, ?, ?)",
                       (number, json.dumps(self.record | {"verdict": verdict}), delivered))
            db.execute("INSERT INTO jenkins_dispatches VALUES (?, ?)", (number, result))
        store = MagicMock()
        (store / "current").resolve.return_value = self.base
        with patch("merge_proofs.merge", return_value=(self.merged, self.file, self.proof)) as action, \
             patch("merge_proofs.publish_source") as publish:
            drain(db, Mock(), store, 1)
            drain(db, Mock(), store, 1)
        self.assertEqual(action.call_count, 1)
        self.assertEqual(action.call_args.args[1], 51)
        publish.assert_called_once_with(store, self.base, self.merged, self.file, self.proof)
