"""Read a proof blob selected by the outside submission guard."""

import base64
import hashlib
import re

from github_revision import REPO, SHA

MAX_PROOF_BYTES = 2 * 1024 * 1024


def proof_blob(app, blob_sha, expected_size):
    if not isinstance(blob_sha, str) or not SHA.fullmatch(blob_sha):
        raise ValueError("Invalid proof blob SHA")
    if type(expected_size) is not int or not 1 <= expected_size <= MAX_PROOF_BYTES:
        raise ValueError("Proof must be between 1 and 2097152 bytes")
    blob = app.request("GET", f"{REPO}/git/blobs/{blob_sha}")
    if (blob.get("sha") != blob_sha or blob.get("size") != expected_size
            or blob.get("encoding") != "base64"):
        raise ValueError("GitHub proof blob metadata does not match the guard")
    content = blob.get("content")
    if not isinstance(content, str):
        raise ValueError("GitHub did not return proof bytes")
    encoded = re.sub(r"[\r\n]", "", content)
    if len(encoded) != 4 * ((expected_size + 2) // 3):
        raise ValueError("GitHub proof blob has an invalid encoded length")
    proof = base64.b64decode(encoded, validate=True)
    if len(proof) != expected_size:
        raise ValueError("GitHub proof blob has an invalid byte count")
    actual = hashlib.sha1(f"blob {len(proof)}\0".encode() + proof).hexdigest()
    if actual != blob_sha:
        raise ValueError("GitHub proof bytes do not match the selected blob")
    return proof
