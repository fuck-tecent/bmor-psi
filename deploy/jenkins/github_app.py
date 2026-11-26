"""Repository-scoped GitHub App authentication for trusted CI processes."""

import base64
import json
import subprocess
import time
from datetime import datetime
from threading import RLock
from urllib.error import HTTPError
from urllib.request import Request, urlopen

APP_ID = 5932842
INSTALLATION_ID = 186036038
REPOSITORY = "goldbach-proofs"
CI_PERMISSIONS = {"checks": "write", "contents": "read", "issues": "read", "pull_requests": "read"}


class RateLimited(Exception):
    def __init__(self, retry_at):
        super().__init__(f"GitHub API rate limited until {retry_at}")
        self.retry_at = retry_at


def base64url(value):
    return base64.urlsafe_b64encode(value).rstrip(b"=")


class GitHubApp:
    def __init__(self, private_key, *, request_interval=0, permissions=None):
        self.private_key = private_key
        self.token = None
        self.expires_at = 0
        self.retry_at = 0
        self.request_interval = request_interval
        self.permissions = CI_PERMISSIONS if permissions is None else permissions
        self.next_request = 0
        self.lock = RLock()

    def app_request(self, method, path, data=None):
        with self.lock:
            return self._app_request(method, path, data)

    def _app_request(self, method, path, data):
        if time.time() < self.retry_at:
            raise RateLimited(self.retry_at)
        now = int(time.time())
        header = base64url(b'{"alg":"RS256","typ":"JWT"}')
        claims = base64url(json.dumps({"iat": now - 60, "exp": now + 480, "iss": str(APP_ID)}).encode())
        signing_input = header + b"." + claims
        signature = subprocess.check_output(
            ["openssl", "dgst", "-sha256", "-sign", self.private_key],
            input=signing_input, timeout=10,
        )
        jwt = (signing_input + b"." + base64url(signature)).decode()
        return self._request(method, path, jwt, data)

    def request(self, method, path, data=None):
        with self.lock:
            return self._installation_request(method, path, data)

    def _installation_request(self, method, path, data):
        if time.time() < self.retry_at:
            raise RateLimited(self.retry_at)
        if time.time() + 60 >= self.expires_at:
            installation = self.app_request(
                "POST", f"/app/installations/{INSTALLATION_ID}/access_tokens",
                {"repositories": [REPOSITORY], "permissions": self.permissions},
            )
            self.token = installation["token"]
            self.expires_at = datetime.fromisoformat(installation["expires_at"]).timestamp()
        try:
            return self._request(method, path, self.token, data)
        except HTTPError as error:
            if error.code == 401:
                self.expires_at = 0
            raise

    def _request(self, method, path, credential, data):
        if not path.startswith("/") or path.startswith("//"):
            raise ValueError("Expected a GitHub API path")
        request = Request(
            "https://api.github.com" + path, method=method,
            data=json.dumps(data).encode() if data is not None else None,
            headers={
                "Authorization": f"Bearer {credential}",
                "Accept": "application/vnd.github+json",
                "Content-Type": "application/json",
                "User-Agent": "goldbach-ci",
            },
        )
        delay = self.next_request - time.monotonic()
        if delay > 0:
            time.sleep(delay)
        self.next_request = time.monotonic() + self.request_interval
        try:
            with urlopen(request, timeout=15) as response:
                body = response.read()
                return json.loads(body) if body else None
        except HTTPError as error:
            if error.code not in (403, 429):
                raise
            headers = error.headers
            now = int(time.time())
            retry_after = headers.get("Retry-After", "")
            reset = headers.get("X-RateLimit-Reset", "")
            exhausted = headers.get("X-RateLimit-Remaining") == "0"
            if not (error.code == 429 or retry_after or exhausted
                    or b"secondary rate limit" in error.read(8192).lower()):
                raise
            retry_at = now + (int(retry_after) if retry_after.isdecimal() else 60)
            if exhausted and reset.isdecimal():
                retry_at = max(retry_at, int(reset))
            self.retry_at = retry_at + 1
            raise RateLimited(self.retry_at) from error
