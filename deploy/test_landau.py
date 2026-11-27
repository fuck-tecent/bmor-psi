import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from deploy.desk import Desk
from deploy.landau import BASELINE, exponent_record, record_statement


class LandauRecordTests(unittest.TestCase):
    def test_only_unconditional_accepted_statements_with_matching_hash_advance(self):
        tasks = json.loads((Path(__file__).parents[1] / "research/problems.json")
                           .read_text(encoding="utf-8"))["quadratic-primes"]["gaps"]
        targets = {g["lpf_exponent"]: g for g in tasks if "lpf_exponent" in g}
        ordinary = next(g for g in tasks if "lpf_exponent" not in g)
        with tempfile.TemporaryDirectory() as directory:
            desk = Desk(Path(directory) / "quadratic-primes.sqlite3", tasks, b"local-test")
            with desk.transaction(write=True) as conn:
                def report(gap, run, verdict, digest=None):
                    conn.execute("""
                        INSERT INTO goldbach_leases
                        (token_hash,gap,statement_sha256,handle,ip_key,claimed_at,expires_at,absolute_expires_at,run_id)
                        VALUES (?,?,?,'test','test',0,1,1,?)
                    """, (str(run), gap["id"], digest or desk.statement_hashes[gap["id"]], run))
                    desk.record_verdict({"lemma_id": gap["id"], "verdict": verdict, "run_id": run}, conn)

                self.assertEqual(exponent_record(desk, conn)["current"], BASELINE)
                report(ordinary, 1, "ACCEPTED")
                report(targets["1.324"], 2, "REJECTED")
                report(targets["2"], 3, "ACCEPTED", hashlib.sha256(b"older statement").hexdigest())
                self.assertIsNone(exponent_record(desk, conn)["verified"])
                report(targets["1.323"], 4, "ACCEPTED")
                self.assertEqual(exponent_record(desk, conn)["current"]["kind"], "lean_accepted")
                report(targets["1.324"], 5, "ACCEPTED")
                report(targets["1.323"], 6, "ACCEPTED")
                report(targets["1.324"], 7, "REJECTED")
                best = exponent_record(desk, conn)["current"]
                self.assertEqual(best["exponent"], "1.324")
                self.assertTrue(best["source_url"].endswith("/runs/5"))
                final = targets["2"]["id"]
                conn.execute("INSERT INTO assembled_proofs VALUES (?,?,?)", (final, 42,
                             json.dumps({"statement_sha256": desk.statement_hashes[final]})))
                assembled = exponent_record(desk, conn)["current"]
                self.assertEqual(assembled["exponent"], "2")
                self.assertTrue(assembled["source_url"].endswith("?lemma=" + final))
                report(targets["2"], 8, "ACCEPTED")
                self.assertEqual(exponent_record(desk, conn)["current"]["exponent"], "2")

    def test_thresholds_match_their_exact_lean_proposition(self):
        self.assertTrue(record_statement("1.324").endswith("n ^ 331 < p ^ 250"))
        with self.assertRaises(ValueError):
            record_statement("2.01")
