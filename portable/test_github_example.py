"""Exercise the GitHub example at its envelope boundary."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent.parent
SCRIPT = ROOT / "examples/github-actions/prepare.py"


class GitHubExampleTests(unittest.TestCase):
    def test_pull_request_head_and_base_are_bound_to_checkout(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            checkout = root / "snapshot"
            checkout.mkdir()
            def git(*args):
                return subprocess.check_output(["git", "-C", str(checkout), *args], text=True).strip()
            git("init", "-q")
            git("config", "user.name", "ProofCI")
            git("config", "user.email", "proofci@example.invalid")
            git("remote", "add", "origin", "https://github.com/example/project")
            (checkout / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 1\n")
            git("add", ".")
            git("commit", "-qm", "base")
            base = git("rev-parse", "HEAD")
            (checkout / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 2\n")
            git("commit", "-qam", "head")
            head = git("rev-parse", "HEAD")
            baseline = root / "baseline.json"
            baseline.write_text(json.dumps({"candidate": "candidate.lean"}))
            event = root / "event.json"
            event.write_text(json.dumps({"action": "synchronize", "pull_request": {"number": 7,
                "head": {"sha": head}, "base": {"sha": base}}}))
            env = dict(os.environ, PROOFCI_VERIFIER=str(ROOT), GITHUB_EVENT_NAME="pull_request_target",
                       GITHUB_EVENT_PATH=str(event), PYTHONDONTWRITEBYTECODE="1")
            command = [sys.executable, str(SCRIPT), str(checkout), str(baseline), str(root / "output")]
            result = subprocess.run(command, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            envelope = json.loads((root / "output/envelope.json").read_text())
            self.assertEqual((envelope["head"], envelope["base"]), (head, base))
            self.assertEqual(json.loads((root / "output/github.json").read_text())["scope"], "source-head-only")
            env["GITHUB_EVENT_NAME"] = "pull_request"
            result = subprocess.run(command, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            self.assertEqual(json.loads((root / "output/github.json").read_text())["event"], "pull_request")
            event.write_text(json.dumps({"action": "synchronize", "pull_request": {"number": 7,
                "head": {"sha": base}, "base": {"sha": base}}}))
            result = subprocess.run(command, env=env, capture_output=True, text=True)
            self.assertEqual(result.returncode, 2)
            self.assertIn("requested head", result.stderr)


if __name__ == "__main__":
    unittest.main()
