"""Verify the IP endpoint and configure the existing GitHub App webhook."""

import argparse
import hashlib
import hmac
import json
import uuid
from pathlib import Path
from urllib.error import HTTPError
from urllib.request import Request, build_opener

from desk_verdict import NoRedirect
from github_app import APP_ID, GitHubApp

URL = "https://114.55.113.128/github/webhook"
EVENTS = {"pull_request", "issue_comment", "push"}


def verify_endpoint(secret):
    body = b"{}"
    signature = hmac.new(secret, body, hashlib.sha256).hexdigest()
    request = Request(URL, body, {
        "Content-Type": "application/json",
        "X-GitHub-Event": "ping",
        "X-GitHub-Delivery": str(uuid.uuid4()),
        "X-Hub-Signature-256": "sha256=" + signature,
    })
    with build_opener(NoRedirect()).open(request, timeout=10) as response:
        if response.status != 204:
            raise RuntimeError("The IP endpoint did not acknowledge the signed ping")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--private-key", required=True, type=Path)
    parser.add_argument("--secret-file", required=True, type=Path)
    parser.add_argument("--apply", action="store_true")
    args = parser.parse_args()
    secret = args.secret_file.read_bytes().strip()
    if len(secret) < 32:
        parser.error("Webhook secret is shorter than 32 bytes")
    verify_endpoint(secret)
    app = GitHubApp(args.private_key)
    info = app.app_request("GET", "/app")
    if info["id"] != APP_ID:
        parser.error("Unexpected GitHub App")
    events = sorted(EVENTS - set(info["events"]))
    try:
        config = app.app_request("GET", "/app/hook/config")
    except HTTPError as error:
        if error.code != 404:
            raise
        print(json.dumps({"signed_ip_ping": True, "github_webhook": "unavailable", "missing_events": events}))
        return
    if args.apply:
        config = app.app_request("PATCH", "/app/hook/config", {
            "url": URL, "content_type": "json", "insecure_ssl": "0", "secret": secret.decode("utf-8"),
        })
        if config["url"] != URL or str(config["insecure_ssl"]) != "0":
            raise RuntimeError("GitHub did not retain the expected Webhook settings")
    deliveries = app.app_request("GET", "/app/hook/deliveries?per_page=10")
    print(json.dumps({
        "signed_ip_ping": True, "github_url_matches": config["url"] == URL,
        "tls_verification": str(config["insecure_ssl"]) == "0", "missing_events": events,
        "deliveries": [{k: delivery.get(k) for k in ("id", "event", "status_code", "delivered_at")}
                       for delivery in deliveries],
    }))


if __name__ == "__main__":
    main()
