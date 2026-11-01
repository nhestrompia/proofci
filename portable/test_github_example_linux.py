"""Run the GitHub example inputs through the pinned local validator."""
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
FIXTURES = ROOT / "experiments/source-binding/fixtures"


@unittest.skipUnless(os.environ.get("PROOFCI_TEST_PACKAGED"), "requires Docker and the pinned image")
class GitHubLinuxTests(unittest.TestCase):
    def test_source_head_pass_unproven_and_execution_failure(self):
        with tempfile.TemporaryDirectory(prefix="proofci-github-") as temp:
            root = Path(temp)
            snapshot = root / "snapshot"
            snapshot.mkdir()
            def git(*args):
                return subprocess.check_output(["git", "-C", str(snapshot), *args], text=True).strip()
            git("init", "-q")
            git("config", "user.name", "ProofCI")
            git("config", "user.email", "proofci@example.invalid")
            git("remote", "add", "origin", "https://github.com/example/project")
            shutil.copy(FIXTURES / "candidate.lean", snapshot / "candidate.lean")
            shutil.copytree(FIXTURES / "verified", snapshot / "evidence")
            git("add", ".")
            git("commit", "-qm", "base")
            base = git("rev-parse", "HEAD")
            protected = root / "protected"
            protected.mkdir()
            shutil.copy(FIXTURES / "contract.json", protected / "contract.json")
            import hashlib
            contract_sha = hashlib.sha256((protected / "contract.json").read_bytes()).hexdigest()
            baseline = protected / "baseline.json"
            baseline.write_text(json.dumps({"version": 1, "candidate": "candidate.lean", "obligations": [
                {"id": "increment", "policy": "required", "contract": "contract.json",
                 "contract_sha256": contract_sha, "evidence": "evidence"}]}))
            event = root / "event.json"
            output = root / "output"
            env = dict(os.environ, PROOFCI_VERIFIER=str(ROOT), GITHUB_EVENT_NAME="pull_request_target",
                       GITHUB_EVENT_PATH=str(event), PYTHONDONTWRITEBYTECODE="1")
            def run():
                head = git("rev-parse", "HEAD")
                event.write_text(json.dumps({"action": "synchronize", "pull_request": {"number": 7,
                    "head": {"sha": head}, "base": {"sha": base}}}))
                subprocess.run([sys.executable, str(ROOT / "examples/github-actions/prepare.py"),
                    str(snapshot), str(baseline), str(output)], check=True, env=env)
                result = subprocess.run([sys.executable, str(ROOT / "portable/container.py"),
                    "--envelope", str(output / "envelope.json"), "--baseline", str(baseline),
                    "--snapshot", str(snapshot), "--report", str(output / "report.json")], env=env)
                return result.returncode, json.loads((output / "report.json").read_text())
            status, report = run()
            self.assertEqual(status, 0, report)
            self.assertEqual(report["results"][0]["decision"], "verified")
            (snapshot / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 2\n")
            git("commit", "-qam", "obsolete proof")
            status, report = run()
            self.assertEqual(status, 1, report)
            self.assertEqual(report["results"][0]["decision"], "unproven")
            (protected / "contract.json").write_text("tampered\n")
            status, report = run()
            self.assertEqual(status, 2, report)
            self.assertEqual(report["status"], "error")


if __name__ == "__main__":
    unittest.main()
