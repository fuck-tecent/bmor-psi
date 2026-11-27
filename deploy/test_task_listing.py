import gzip
import json
import unittest
from unittest.mock import MagicMock, patch
from urllib.error import HTTPError

from tools import goldbach


class TaskListingTests(unittest.TestCase):
    def test_downloads_only_the_requested_count_from_the_tasks_api(self):
        payload = {"problem": "twin-primes", "available": 10, "tasks": [{"id": "one"}]}
        opener = MagicMock()
        response = opener.open.return_value.__enter__.return_value
        response.headers = {"Content-Encoding": "gzip"}
        response.read.return_value = gzip.compress(json.dumps(payload).encode())
        with patch.object(goldbach.urllib.request, "build_opener", return_value=opener):
            self.assertEqual(goldbach.list_tasks("twin-primes", 1), payload)
        self.assertTrue(opener.open.call_args.args[0].full_url.endswith("/problems/twin-primes/api/tasks?limit=1"))
        self.assertEqual(opener.open.call_count, 1)

    def test_fallback_board_excludes_unclaimable_tasks_and_keeps_parallel_claims(self):
        board = {
            "desk": {"assignments": {"parallel-task": "working", "occupied": "working"}},
            "gaps": [
                {"id": "parallel-task", "parallel": True, "points": 4},
                {"id": "occupied"},
                {"id": "closed", "claims_closed": True},
                {"id": "refuted", "refutation": {"status": "verified"}},
                {"id": "proved", "proved": True},
                {"id": "resolved", "resolved": True},
                {"id": "challenge", "challenge_only": True, "points": 7},
            ],
        }
        opener = MagicMock()
        response = opener.open.return_value.__enter__.return_value
        response.headers = {"Content-Encoding": "gzip"}
        response.read.return_value = gzip.compress(json.dumps(board).encode())
        opener.open.side_effect = [HTTPError("", 404, "", None, None), opener.open.return_value]
        with patch.object(goldbach.urllib.request, "build_opener", return_value=opener):
            listing = goldbach.list_tasks("twin-primes", 1)
        self.assertEqual(listing, {
            "problem": "twin-primes", "available": 2,
            "tasks": [{"id": "challenge", "points": 7, "challenge_only": True}],
        })
        request = opener.open.call_args.args[0]
        self.assertEqual(request.get_method(), "GET")
        self.assertTrue(request.full_url.endswith("/problems/twin-primes/api/status?view=board-gzip"))
