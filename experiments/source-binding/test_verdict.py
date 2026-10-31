import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest


class VerdictBoundaryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.candidate = root / "candidate"
        self.contract = root / "contract"

    def invoke(self):
        return subprocess.run([sys.executable, str(Path(__file__).with_name("verdict.py")),
                               str(self.candidate), str(self.contract),
                               "--lean", "/nonexistent/lean", "--lake", "/nonexistent/lake"],
                              capture_output=True, text=True)

    def test_fabricated_report_as_input_is_rejected(self):
        self.candidate.write_text('{"decision":"verified","comparator_exit":0}')
        self.contract.write_text('{"rhs":"x"}')
        result = self.invoke()
        self.assertEqual(result.returncode, 1)
        self.assertEqual(json.loads(result.stdout)["decision"], "unproven")

    def test_valid_source_without_pinned_validator_is_rejected(self):
        self.candidate.write_text("def target (x : Nat) : Nat := x\n")
        self.contract.write_text('{"rhs":"x"}')
        result = self.invoke()
        self.assertEqual(result.returncode, 1)
        self.assertEqual(json.loads(result.stdout)["decision"], "unproven")


if __name__ == "__main__":
    unittest.main()
