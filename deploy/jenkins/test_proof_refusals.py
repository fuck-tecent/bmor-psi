import sqlite3
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from build_checks import enqueue_formal_checks, refusal_summary
from check_outbox import database
from formal_proof import judge
from desk_outbox import drain, enqueue_runner_failures, initialize
from prepare_proof import ProofRefused, report_guard_result


class ProofRefusalTests(unittest.TestCase):
    def test_reconcile_failed_runner_then_publish_distinct_check(self):
        with tempfile.TemporaryDirectory() as directory, sqlite3.connect(":memory:") as jobs:
            jobs.executescript("""
                CREATE TABLE ci_jobs (id, kind, sha, pr, trigger);
                CREATE TABLE desk_runs (job_id, run_id);
                CREATE TABLE jenkins_dispatches (job_id, result);
                CREATE TABLE proof_refusals (job_id, reason);
                INSERT INTO ci_jobs VALUES (1, 'authoritative', 'aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa', 72, '8');
                INSERT INTO ci_jobs VALUES (2, 'authoritative', 'bbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbbb', 73, '9');
                INSERT INTO desk_runs VALUES (1, 101), (2, 102);
                INSERT INTO jenkins_dispatches VALUES (1, 'FAILURE'), (2, 'FAILURE');
                INSERT INTO proof_refusals VALUES (2, 'source guard');
            """)
            initialize(jobs)
            enqueue_runner_failures(jobs, 100)
            enqueue_runner_failures(jobs, 100)
            self.assertEqual(jobs.execute("SELECT run FROM desk_outbox").fetchall(), [(101,)])
            with patch("desk_outbox.signed_post") as failure, patch("desk_outbox.send_verdict") as result:
                drain(jobs, "https://example.org/api/verdict", b"test")
                failure.assert_called_once()
                self.assertEqual(failure.call_args.args[0], "https://example.org/api/desk/check-failed")
                result.assert_not_called()
            outbox = database(Path(directory) / "checks.sqlite")
            enqueue_formal_checks(jobs, outbox)
            check = outbox.execute("SELECT * FROM checks WHERE name LIKE '%Lean verdict'").fetchone()
            self.assertEqual(check["conclusion"], "failure")
            self.assertIn("before issuing a Lean verdict", check["summary"])
            outbox.close()

    def test_modulo_refusal_suggests_explicit_arithmetic_only(self):
        self.assertIn("Nat.mod p 30", refusal_summary('line 64: "p%" is not allowed in a proof file'))
        self.assertNotIn("Nat.mod", refusal_summary('line 12: "macro" is not allowed in a proof file'))

    def test_only_an_explicit_guard_refusal_is_reported(self):
        with self.assertRaisesRegex(ProofRefused, "line 64"):
            report_guard_result(subprocess.CompletedProcess(
                ["guard"], 1, 'REFUSED: line 64: "p%" is not allowed\nIgnored diagnostic\n',
            ))
        with self.assertRaises(subprocess.CalledProcessError):
            report_guard_result(subprocess.CompletedProcess(["guard"], 125, ""))

    def test_refusal_is_published_without_issuing_a_lean_verdict(self):
        with tempfile.TemporaryDirectory() as directory:
            jobs = sqlite3.connect(":memory:")
            jobs.execute("CREATE TABLE ci_jobs (id, kind, sha, pr, trigger)")
            jobs.execute("INSERT INTO ci_jobs VALUES (2, 'authoritative', ?, 3754, '7')", ("a" * 40,))
            jobs.execute("CREATE TABLE desk_runs (job_id INTEGER PRIMARY KEY, run_id INTEGER UNIQUE NOT NULL)")
            outbox = database(Path(directory) / "checks.sqlite")
            with patch("formal_proof.prepare", side_effect=ProofRefused("line 64: token is not allowed")), \
                    patch("formal_proof.authorize") as authorize, patch("formal_proof.verify") as verify:
                with self.assertRaises(ProofRefused):
                    judge(jobs, None, 2, None, None, None, None, desk_url="", secret=b"")
            authorize.assert_not_called()
            verify.assert_not_called()
            self.assertEqual(jobs.execute("SELECT count(*) FROM desk_outbox").fetchone()[0], 0)
            enqueue_formal_checks(jobs, outbox)
            check = outbox.execute("SELECT name, conclusion, summary FROM checks").fetchone()
            self.assertEqual(tuple(check)[:2], ("Goldbach CI / formal submission refused", "failure"))
            self.assertIn("before Lean ran", check["summary"])
            self.assertIn("line 64: token is not allowed", check["summary"])
            outbox.close()
            jobs.close()
