"""The examples verify, and the getting-started guide shows exactly their files."""

import json
import os
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GUIDE = ROOT / "docs" / "getting-started.md"
BANK = ROOT / "examples" / "bank"


def guide_blocks():
    return re.findall(r"```(\w+)\n(.*?)```", GUIDE.read_text(), re.S)


class GuideMatchesExample(unittest.TestCase):
    def test_guide_code_is_the_example(self):
        blocks = guide_blocks()
        yaml = [b for lang, b in blocks if lang == "yaml" and "targets:" in b]
        lean = [b for lang, b in blocks if lang == "lean"]
        self.assertEqual(yaml, [(BANK / "proofci.yaml").read_text()])
        self.assertIn((BANK / "proofci" / "Contract.lean").read_text(), lean)
        self.assertIn((BANK / "proofci" / "Proofs.lean").read_text(), lean)


@unittest.skipUnless(os.environ.get("PROOFCI_TOOLCHAIN"), "needs the ProofCI toolchain image")
class ExamplesVerify(unittest.TestCase):
    def test_every_example_passes(self):
        for example in sorted(p for p in (ROOT / "examples").iterdir() if (p / "proofci.yaml").exists()):
            with self.subTest(example=example.name), tempfile.TemporaryDirectory() as tmp:
                report = Path(tmp) / "report.json"
                done = subprocess.run(
                    [sys.executable, "-m", "proofci", "check", "--base", example, "--head", example,
                     "--report", report], cwd=ROOT, capture_output=True, text=True, timeout=1800)
                data = json.loads(report.read_text())
                self.assertTrue(data["passed"], done.stdout)
                self.assertEqual([g for g in data["guarantees"] if g.get("warnings")], [])


if __name__ == "__main__":
    unittest.main()
