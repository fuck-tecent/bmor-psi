"""Send a previously persisted verdict to the Goldbach desk."""

import hashlib
import hmac
import json
from urllib.parse import urlsplit
from urllib.request import HTTPRedirectHandler, Request, build_opener


class NoRedirect(HTTPRedirectHandler):
    def redirect_request(self, *args):
        return None


def signed_post(url, secret, payload, expected):
    target = urlsplit(url)
    if target.scheme != "https" or not target.hostname or target.username is not None or target.fragment:
        raise ValueError("Expected an HTTPS verdict endpoint")
    if not secret or not isinstance(payload, bytes) or not 1 <= len(payload) <= 262144:
        raise ValueError("Expected a signing secret and a valid verdict payload")
    signature = hmac.new(secret, payload, hashlib.sha256).hexdigest()
    request = Request(url, payload, {
        "Content-Type": "application/json",
        "X-Goldbach-Signature": "sha256=" + signature,
    })
    with build_opener(NoRedirect()).open(request, timeout=15) as response:
        if response.status != 200 or json.loads(response.read(1025)) != expected:
            raise RuntimeError("Desk endpoint did not acknowledge the request")


def authorize(url, secret, *, pr, head, handle, gap, run_id, statement):
    payload = json.dumps({
        "pr": pr,
        "head": head,
        "handle": handle,
        "gap": gap,
        "run_id": run_id,
        "statement_sha256": hashlib.sha256(statement).hexdigest(),
    }).encode()
    signed_post(url.rstrip("/") + "/authorize", secret, payload, {"authorized": True})


def send_verdict(url, secret, payload):
    signed_post(url, secret, payload, {"status": "stored"})