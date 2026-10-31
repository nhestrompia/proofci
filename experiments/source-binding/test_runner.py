import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


class RunnerFailureTests(unittest.TestCase):
    def test_bad_archive_returns_unproven_report(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            for name in ("archive", "package", "candidate", "contract"):
                (root / name).write_text("invalid")
            env = dict(os.environ, PROOFCI_LEAN_ARCHIVE=str(root / "archive"),
                       PROOFCI_BWRAP_PACKAGE=str(root / "package"))
            result = subprocess.run([str(Path(__file__).with_name("linux.sh")),
                                     str(root / "candidate"), str(root / "contract")],
                                    env=env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertEqual(json.loads(result.stdout)["decision"], "unproven")


if __name__ == "__main__":
    unittest.main()
