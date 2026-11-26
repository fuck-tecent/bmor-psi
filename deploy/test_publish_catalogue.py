import json
import os
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from deploy import publish_catalogue as pub


class CataloguePublisherTests(unittest.TestCase):
    def test_merge_preserves_independent_changes_to_the_same_lemma(self):
        base = {"gaps": [{"id": "L-one", "statement": "True"}]}
        live = {"gaps": [dict(base["gaps"][0], refutation={"status": "verified"})]}
        candidate = {"gaps": [dict(base["gaps"][0], claims_closed=True), {"id": "L-two"}]}
        self.assertEqual(pub.merge_catalogue(base, live, candidate, "gaps.json"), {
            "gaps": [dict(live["gaps"][0], claims_closed=True), {"id": "L-two"}],
        })

    def test_merge_rejects_competing_changes_to_the_same_field(self):
        base = {"gaps": [{"id": "L-one", "statement": "True"}]}
        live = {"gaps": [dict(base["gaps"][0], statement="False")]}
        candidate = {"gaps": [dict(base["gaps"][0], statement="0 = 0")]}
        with self.assertRaisesRegex(ValueError, r"L-one\.statement"):
            pub.merge_catalogue(base, live, candidate, "gaps.json")

    def test_owner_and_exact_successful_build(self):
        sha = "a" * 40
        pr = dict(number=12, merge_commit_sha=sha, merged_at="today",
                  base=dict(ref="main", repo=dict(full_name=pub.REPO)))
        detail = dict(pr, merged_by=dict(id=pub.OWNER_ID, login=pub.REPO.split("/")[0]))
        runs = dict(workflow_runs=[dict(head_sha=sha, conclusion="success", id=4)])
        with patch.object(pub, "api", side_effect=[[pr], detail, runs]):
            self.assertEqual(pub.approved(sha), (detail, runs["workflow_runs"][0]))
        with patch.object(pub, "api", side_effect=[[pr], detail, dict(workflow_runs=[])]):
            self.assertIsNone(pub.approved(sha))
        collaborator = dict(pr, merged_by=dict(id=1234, login="researcher"))
        with patch.dict(os.environ, {"GOLDBACH_CATALOGUE_MERGER_IDS": "1234 5678"}):
            with patch.object(pub, "api", side_effect=[[pr], collaborator, runs]):
                self.assertEqual(pub.approved(sha), (collaborator, runs["workflow_runs"][0]))
            wrong_commit = dict(workflow_runs=[dict(head_sha="b" * 40, conclusion="success")])
            with patch.object(pub, "api", side_effect=[[pr], collaborator, wrong_commit]):
                self.assertIsNone(pub.approved(sha))
        with patch.dict(os.environ, {"GOLDBACH_CATALOGUE_MERGER_IDS": ""}), \
                patch.object(pub, "api", side_effect=[[pr], collaborator]):
            with self.assertRaises(RuntimeError):
                pub.approved(sha)

    @unittest.skipUnless(os.name == "posix", "Production switches directory symlinks on Linux")
    def test_publish_and_rollback(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            old = root / ("a" * 40)
            old.mkdir()
            for f in pub.FILES:
                (old / f).write_text('{"old":1}')
            (old / "history.json").write_text("[]")
            current = root / "current"
            current.symlink_to(old)
            new = "b" * 40
            def blob(_, ref):
                return b'{"new":1}' if ref.startswith(new + ":") else b'{"old":1}'
            pr = dict(number=1, title="release", merged_by=dict(login="owner"))
            with patch.object(pub, "STORE", root), patch.object(pub, "CURRENT", current), patch.object(pub, "git", blob):
                with patch.object(pub, "reload_revision", side_effect=[RuntimeError(), None]):
                    with self.assertRaises(RuntimeError):
                        pub.activate(new, new+"^1", pr, dict(id=9))
                self.assertEqual(current.resolve(), old)
                with patch.object(pub, "reload_revision"):
                    pub.activate(new, new+"^1", pr, dict(id=9))
                self.assertEqual(json.loads((current / "history.json").read_text())[0]["sha"], new)
                self.assertEqual(json.loads((current / pub.FILES[0]).read_text()), {"new":1})
