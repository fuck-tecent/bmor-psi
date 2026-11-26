"""Resolve GitHub webhook revisions and changed paths before routing."""

import re

REPO = "/repos/CGandGameEngineLearner/goldbach-proofs"
SHA = re.compile(r"[0-9a-f]{40}")


class StaleDelivery(ValueError):
    pass


def pull_request(app, number):
    if type(number) is not int or number < 1:
        raise ValueError("Invalid pull request number")
    return app.request("GET", f"{REPO}/pulls/{number}")


def changed_paths(app, event, payload):
    """Return changed paths, or None when GitHub cannot provide a complete list."""
    if event == "pull_request":
        number = payload["number"]
        expected = payload["pull_request"]["head"]["sha"]
        before = pull_request(app, number)
        if before["state"] != "open" or before["head"]["sha"] != expected:
            raise StaleDelivery("Pull request has moved")
        count = before["changed_files"]
        if count > 3000:
            return None
        files = []
        for page in range(1, (count + 99) // 100 + 1):
            files.extend(app.request("GET", f"{REPO}/pulls/{number}/files?per_page=100&page={page}"))
        after = pull_request(app, number)
        if (after["state"] != "open" or after["head"]["sha"] != expected
                or after["base"]["sha"] != before["base"]["sha"]):
            raise StaleDelivery("Pull request changed while listing files")
        if len(files) != count:
            return None
    elif event == "push":
        before = payload["before"]
        after = payload["after"]
        if not all(isinstance(sha, str) and SHA.fullmatch(sha) for sha in (before, after)):
            raise ValueError("Invalid push revision")
        if before == "0" * 40:
            return None
        comparison = app.request("GET", f"{REPO}/compare/{before}...{after}?per_page=1&page=1")
        files = comparison["files"]
        if len(files) >= 300:
            return None
    else:
        return set()
    return {entry[key] for entry in files for key in ("filename", "previous_filename") if entry.get(key)}
