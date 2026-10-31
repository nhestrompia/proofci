"""End-to-end CLI tests with the pinned offline Linux validator."""
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import signal
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

HERE = Path(__file__).resolve().parent
FIXTURES = HERE.parent / "experiments/source-binding/fixtures"
spec = importlib.util.spec_from_file_location("proofci", HERE / "proofci.py")
proofci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(proofci)


@unittest.skipUnless(os.environ.get("PROOFCI_TEST_PACKAGED"), "requires the pinned local image and Docker")
class LinuxCLITests(unittest.TestCase):
    def test_pass_and_obsolete_proof(self):
        with tempfile.TemporaryDirectory(prefix="proofci-cli-test-") as temp:
            root = Path(temp)
            snapshot = root / "snapshot"
            snapshot.mkdir()
            shutil.copy(FIXTURES / "candidate.lean", snapshot / "candidate.lean")
            shutil.copytree(FIXTURES / "verified", snapshot / "evidence")
            shutil.copy(FIXTURES / "contract.json", root / "contract.json")
            def git(*args):
                return subprocess.check_output(["git", "-C", str(snapshot), *args], text=True).strip()
            git("init", "-q")
            git("config", "user.name", "ProofCI")
            git("config", "user.email", "proofci@example.invalid")
            git("remote", "add", "origin", "https://example.invalid/fixture.git")
            def commit(message):
                git("add", ".")
                git("commit", "-qm", message)
                return git("rev-parse", "HEAD")
            head = commit("valid")
            checkout = root / "linked-checkout"
            git("worktree", "add", "-qb", "fixture-worktree", str(checkout))
            snapshot = checkout
            sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
            baseline = {"version": 1, "candidate": "candidate.lean", "obligations": [
                {"id": "increment", "policy": "required", "contract": "contract.json",
                 "contract_sha256": sha(root / "contract.json"), "evidence": "evidence"},
                {"id": "advice", "policy": "advisory", "contract": "contract.json",
                 "contract_sha256": sha(root / "contract.json"), "evidence": "missing"}]}
            (root / "baseline.json").write_text(json.dumps(baseline))
            envelope = {"version": 1, "repository": "https://example.invalid/fixture.git", "head": head, "base": head,
                "candidate_sha256": sha(snapshot / "candidate.lean"), "baseline_sha256": sha(root / "baseline.json"),
                "dependency": sha(proofci.VALIDATOR / "core-dependencies.json"), "toolchain": proofci.TOOLCHAIN_SHA256,
                "trust_policy": proofci.policy_digest(), "resource_policy": {"timeout_seconds": 180, "cpu_seconds": 180,
                "memory_bytes": 2147483648, "file_bytes": 2147483648, "processes": 256}}
            def run(cancel=False):
                (root / "envelope.json").write_text(json.dumps(envelope))
                command = [sys.executable, str(HERE / "container.py"),
                    "--envelope", str(root / "envelope.json"), "--baseline", str(root / "baseline.json"),
                    "--snapshot", str(snapshot), "--report", str(root / "report.json")]
                result = subprocess.Popen(command)
                if cancel:
                    time.sleep(2)
                    result.send_signal(signal.SIGTERM)
                result.wait(timeout=60)
                remaining = subprocess.check_output(["docker", "ps", "-aq", "--filter", f"label=proofci.run={result.pid}"], text=True)
                self.assertEqual(remaining.strip(), "")
                return result.returncode, json.loads((root / "report.json").read_text())
            status, report = run()
            self.assertEqual(status, 0, report)
            if os.environ.get("PROOFCI_FIXTURE_OUTPUT"):
                output = Path(os.environ["PROOFCI_FIXTURE_OUTPUT"])
                output.mkdir(parents=True, exist_ok=True)
                (output / "passing.json").write_text(json.dumps({"envelope": envelope, "baseline": baseline, "report": report}, indent=2) + "\n")
            self.assertEqual([x["decision"] for x in report["results"]], ["verified", "unproven"])
            self.assertIn("manifest.json", report["results"][0]["evidence_sha256"])
            archive = root / "evidence.tar"
            exported = subprocess.run([sys.executable, str(HERE / "replay.py"), "export", "--envelope", str(root / "envelope.json"),
                "--baseline", str(root / "baseline.json"), "--snapshot", str(snapshot), "--report", str(root / "report.json"),
                "--output", str(archive)], capture_output=True, text=True)
            self.assertEqual(exported.returncode, 0, exported.stderr)
            replay_report = root / "replay.json"
            replayed = subprocess.run([sys.executable, str(HERE / "replay.py"), "replay", "--bundle", str(archive),
                "--sha256", exported.stdout.strip().removeprefix("sha256:"), "--output", str(replay_report)], capture_output=True, text=True)
            self.assertEqual(replayed.returncode, 0, replayed.stderr + replay_report.read_text())
            self.assertEqual(json.loads(replay_report.read_text())["status"], "reproduced")
            (snapshot / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 2\n")
            envelope["head"] = commit("changed")
            envelope["candidate_sha256"] = sha(snapshot / "candidate.lean")
            status, report = run()
            self.assertEqual(status, 1, report)
            self.assertEqual(report["results"][0]["reason"], "invalid_evidence")
            if os.environ.get("PROOFCI_FIXTURE_OUTPUT"):
                (Path(os.environ["PROOFCI_FIXTURE_OUTPUT"]) / "obsolete.json").write_text(json.dumps({"envelope": envelope, "baseline": baseline, "report": report}, indent=2) + "\n")
            shutil.copy(FIXTURES / "candidate.lean", snapshot / "candidate.lean")
            envelope["head"] = commit("restore")
            envelope["candidate_sha256"] = sha(snapshot / "candidate.lean")
            envelope["resource_policy"]["timeout_seconds"] = 1
            envelope["resource_policy"]["cpu_seconds"] = 1
            status, report = run()
            self.assertEqual(status, 2, report)
            self.assertEqual(report["results"][0]["reason"], "timeout")
            envelope["resource_policy"]["timeout_seconds"] = 180
            envelope["resource_policy"]["cpu_seconds"] = 180
            status, report = run(cancel=True)
            self.assertEqual(status, 2, report)
            self.assertEqual(report["reason"], "cancelled")


if __name__ == "__main__":
    unittest.main()
