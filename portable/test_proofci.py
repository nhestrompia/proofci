import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

CLI = Path(__file__).with_name("proofci.py")


class CLITest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 1")
        (self.root / "contract.json").write_text('{"rhs":"x + 1"}')
        sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
        baseline = {"version": 1, "candidate": "candidate.lean", "obligations": [
            {"id": "one", "policy": "required", "contract": "contract.json",
             "contract_sha256": sha(self.root / "contract.json"), "evidence": "missing"},
            {"id": "two", "policy": "advisory", "contract": "contract.json",
             "contract_sha256": sha(self.root / "contract.json"), "evidence": "missing2"}]}
        (self.root / "baseline.json").write_text(json.dumps(baseline))
        envelope = {"version": 1, "repository": "repo", "head": "head", "base": "base",
                    "candidate_sha256": sha(self.root / "candidate.lean"),
                    "baseline_sha256": sha(self.root / "baseline.json"), "dependency": "dep",
                    "toolchain": "tool", "trust_policy": "policy",
                    "resource_policy": {"timeout_seconds": 5, "cpu_seconds": 5,
                      "memory_bytes": 1000000000, "file_bytes": 1000000, "processes": 100}}
        (self.root / "envelope.json").write_text(json.dumps(envelope))

    def run_cli(self):
        p = subprocess.run([sys.executable, str(CLI), "--envelope", str(self.root / "envelope.json"),
          "--baseline", str(self.root / "baseline.json"), "--snapshot", str(self.root),
          "--toolchain", str(self.root / "toolchain"), "--report", str(self.root / "report.json")])
        return p.returncode, json.loads((self.root / "report.json").read_text())

    def test_all_obligations_are_reported_when_proofs_missing(self):
        status, report = self.run_cli()
        self.assertEqual(status, 1)
        self.assertEqual([r["reason"] for r in report["results"]], ["missing_evidence"] * 2)

    def test_modified_baseline_is_configuration_error(self):
        (self.root / "baseline.json").write_text('{"version":1,"candidate":"x","obligations":[]}')
        status, report = self.run_cli()
        self.assertEqual(status, 2)
        self.assertEqual(report["status"], "error")

    def test_unavailable_validator_accounts_for_remaining_obligations(self):
        (self.root / "missing").mkdir()
        status, report = self.run_cli()
        self.assertEqual(status, 2)
        self.assertEqual([r["reason"] for r in report["results"]],
                         ["validation_unavailable", "missing_evidence"])


if __name__ == "__main__":
    unittest.main()
