import hashlib
import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from prepare_proof import allow_verified_imports


class VerifiedImportTests(unittest.TestCase):
    def test_select_only_requested_verified_source_and_preserve_task_permissions(self):
        with TemporaryDirectory() as tmp:
            base = Path(tmp)
            name = "Conjectures.Goldbach.First"
            path = base / "lean/Conjectures/Goldbach/First.lean"
            path.parent.mkdir(parents=True)
            path.write_bytes(b"accepted bytes")
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            (base / "verified-imports.json").write_text(json.dumps({name: digest, "Conjectures.Other.Unused": digest}))
            permissions = base / "imports.json"
            permissions.write_text('["PEqualNP.Defs"]')
            (base / "proof.lean").write_text("import " + name + "\nimport Conjectures.Other.Pending\n")
            allow_verified_imports(base, base)
            self.assertEqual(set(json.loads(permissions.read_text())), {name, "PEqualNP.Defs"})
            permissions.write_text("[]")
            path.write_bytes(b"changed")
            with self.assertRaisesRegex(ValueError, "differs"):
                allow_verified_imports(base, base)
