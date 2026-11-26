"""Queue builds and read results from the local Jenkins controller."""

import base64
import json
import re
from http.cookiejar import CookieJar
from urllib.parse import urlencode, urlsplit
from urllib.request import HTTPCookieProcessor, Request, build_opener


class Jenkins:
    def __init__(self, url, username, credential):
        target = urlsplit(url)
        if target.scheme != "http" or target.hostname != "127.0.0.1":
            raise ValueError("Expected a local Jenkins controller URL")
        self.url = url.rstrip("/")
        encoded = base64.b64encode(f"{username}:{credential}".encode()).decode()
        self.headers = {"Authorization": f"Basic {encoded}"}
        self.opener = build_opener(HTTPCookieProcessor(CookieJar()))
        self.crumb = None

    def request(self, path, data=None, *, content_type=None):
        headers = dict(self.headers)
        if data is not None:
            if self.crumb is None:
                self.crumb = self.get("/crumbIssuer/api/json")
            headers[self.crumb["crumbRequestField"]] = self.crumb["crumb"]
        if content_type is not None:
            headers["Content-Type"] = content_type
        request = Request(self.url + path, data=data, headers=headers)
        return self.opener.open(request, timeout=15)

    def get(self, path):
        with self.request(path) as response:
            return json.load(response)

    def job_path(self, name):
        if not re.fullmatch(r"[a-z0-9][a-z0-9-]*", name):
            raise ValueError("Invalid Jenkins job name")
        return f"/job/{name}"

    def enqueue(self, name, parameters=None):
        path = self.job_path(name)
        endpoint = "/buildWithParameters" if parameters is not None else "/build"
        with self.request(path + endpoint, urlencode(parameters or {}).encode()) as response:
            location = urlsplit(response.headers.get("Location", "")).path
            match = re.fullmatch(r"/queue/item/([0-9]+)/?", location)
            if response.status != 201 or match is None:
                raise RuntimeError("Jenkins did not return a queue item")
            return int(match[1])

    def queued(self, queue_id):
        return self.get(f"/queue/item/{int(queue_id)}/api/json")

    def result(self, name, build_number):
        return self.get(f"{self.job_path(name)}/{int(build_number)}/api/json")
