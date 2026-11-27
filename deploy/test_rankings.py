import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from deploy.desk import Desk


class RankingTests(unittest.TestCase):
    def test_first_acceptance_per_lemma_and_rolling_hour(self):
        now = 1_800_000_000
        with tempfile.TemporaryDirectory() as directory:
            desk = Desk(Path(directory) / "rankings.sqlite", [], b"test-secret")
            with patch("deploy.desk.time.time", return_value=now):
                self.assertEqual(desk.public_status()["rankings"], {
                    "all_time": [], "hour": [], "contributors": 0, "proofs": 0, "latest_accepted_at": None,
                })
            with desk.transaction(write=True) as conn:
                rows = [
                    ("alpha", "first", 10, now - 7200, "ACCEPTED"),
                    ("beta", "first", 11, now - 5, "ACCEPTED"),
                    ("alpha", "first", 12, now - 3, "ACCEPTED"),
                    ("alpha", "second", 13, now - 3600, "ACCEPTED"),
                    ("gamma", "third", 14, now - 120, "ACCEPTED"),
                    ("beta", "fourth", 15, now - 60, "REJECTED"),
                ]
                conn.executemany("""
                    INSERT INTO goldbach_leases (
                        token_hash, gap, statement_sha256, handle, ip_key, claimed_at,
                        expires_at, absolute_expires_at, run_id, finished_at, verdict
                    ) VALUES (?, ?, 'hash', ?, 'network', 0, 0, 0, ?, ?, ?)
                """, [(str(run), gap, handle, run, at, verdict) for handle, gap, run, at, verdict in rows])
                conn.execute("UPDATE goldbach_leases SET points = 9 WHERE run_id = 14")
            with patch("deploy.desk.time.time", return_value=now):
                payload = desk.public_status()
            self.assertEqual(payload["rankings"], {
                "all_time": [
                    {"handle": "gamma", "accepted": 1, "points": 9, "latest_accepted_at": now - 120},
                    {"handle": "alpha", "accepted": 2, "points": 2, "latest_accepted_at": now - 3600},
                ],
                "hour": [
                    {"handle": "gamma", "accepted": 1, "points": 9, "latest_accepted_at": now - 120},
                    {"handle": "alpha", "accepted": 1, "points": 1, "latest_accepted_at": now - 3600},
                ],
                "contributors": 2,
                "proofs": 3,
                "latest_accepted_at": now - 120,
            })
            self.assertEqual(payload["leaderboard"][1], {"handle": "alpha", "accepted": 2})


if __name__ == "__main__":
    unittest.main()
