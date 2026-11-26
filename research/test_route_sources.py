import json
import tempfile
import unittest
from pathlib import Path

from research.build_catalogue import build


class RouteSourcesTest(unittest.TestCase):
    def test_mixed_generation_and_route_move(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def save(name, data):
                path = root / name
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps(data), encoding="utf8")
            save("gaps.json", {"gaps": [{"id": "legacy"}], "tracks": []})
            save("problems.json", {"log-rank": {"gaps": [], "roadmap": []}})
            name = {"zh": "路线", "en": "Route"}
            for slug in ("goldbach", "log-rank"):
                folder = f"problems/{slug}/routes/sample"
                save(folder + "/route.json", dict(id="sample", title=name, description=name, feeds=[]))
                ident = "L-" + slug + "-sample"
                save(folder + "/tasks/" + ident + ".json", dict(id=ident, statement="True", brief=name, plain_statement=name))
            first = build(root)
            for k, v in first.items():
                save(k, v)
            self.assertEqual(build(root), first)
            self.assertEqual(first["gaps.json"]["gaps"][0], {"id": "legacy"})
            self.assertEqual(first["gaps.json"]["gaps"][1]["file"], "lean/Conjectures/Goldbach/Sample.lean")
            self.assertEqual(first["problems.json"]["log-rank"]["gaps"][0]["module"], "Conjectures.LogRank.Sample")
            self.assertEqual(first["problems.json"]["log-rank"]["roadmap"][0]["tasks"][0]["id"], ident)
            route = root / "problems/goldbach/routes/sample"
            route.rename(route.with_name("next"))
            save("problems/goldbach/routes/next/route.json", dict(id="next", title=name, description=name, feeds=[]))
            self.assertEqual(build(root)["gaps.json"]["gaps"][1]["track"], "next")
            task = next(route.with_name("next").glob("tasks/*.json"))
            data = json.loads(task.read_text())
            save(task, {**data, "statement": "False"})
            with self.assertRaisesRegex(ValueError, "Frozen statement"):
                build(root)
