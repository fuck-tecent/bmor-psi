import gzip
import json
import unittest
from unittest.mock import MagicMock, patch

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

    def test_large_requests_use_bounded_pages(self):
        def response(items):
            reply = MagicMock()
            reply.__enter__.return_value.headers = {"Content-Encoding": "gzip"}
            reply.__enter__.return_value.read.return_value = gzip.compress(json.dumps({
                "problem": "twin-primes", "available": 101, "tasks": items,
            }).encode())
            return reply
        opener = MagicMock()
        opener.open.side_effect = [response([{"id": str(i)} for i in range(100)]), response([{"id": "100"}])]
        with patch.object(goldbach.urllib.request, "build_opener", return_value=opener):
            self.assertEqual(len(goldbach.list_tasks("twin-primes", 101)["tasks"]), 101)
        self.assertTrue(opener.open.call_args.args[0].full_url.endswith("/api/tasks?limit=1&offset=100"))
