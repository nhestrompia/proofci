"""Exercise local and isolated dispatch with the pinned Lean image."""

import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import report


FIXTURES = Path(__file__).resolve().parent.parent / "experiments/source-binding/fixtures"
HERE = Path(__file__).resolve().parent


@unittest.skipUnless(os.environ.get("PROOFCI_TEST_PACKAGED"),
                     "requires the pinned local image and Docker")
class IsolatedDispatchLinuxTests(unittest.TestCase):
    def test_local_and_dispatched_outcomes_match(self):
        with tempfile.TemporaryDirectory(prefix="proofci-dispatch-test-") as temporary:
            root = Path(temporary)
            snapshot = root / "snapshot"
            snapshot.mkdir()
            shutil.copy(FIXTURES / "candidate.lean", snapshot / "candidate.lean")
            shutil.copytree(FIXTURES / "verified", snapshot / "evidence")
            contract = root / "contract.json"
            shutil.copy(FIXTURES / "contract.json", contract)

            def git(*args):
                return subprocess.check_output(["git", "-C", str(snapshot), *args], text=True).strip()

            git("init", "-q")
            git("config", "user.name", "ProofCI")
            git("config", "user.email", "proofci@example.invalid")
            git("remote", "add", "origin", "https://example.invalid/fixture.git")
            git("add", ".")
            git("commit", "-qm", "dispatch fixture")
            head = git("rev-parse", "HEAD")
            sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
            baseline = root / "baseline.json"
            baseline.write_text(json.dumps({"version": 1, "candidate": "candidate.lean",
                "obligations": [{"id": "increment", "policy": "required",
                    "contract": "contract.json", "contract_sha256": sha(contract),
                    "evidence": "evidence"}]}))
            envelope = root / "envelope.json"
            import proofci
            envelope.write_text(json.dumps({"version": 1,
                "repository": "https://example.invalid/fixture.git", "head": head, "base": head,
                "candidate_sha256": sha(snapshot / "candidate.lean"),
                "baseline_sha256": sha(baseline),
                "dependency": sha(proofci.VALIDATOR / "core-dependencies.json"),
                "toolchain": proofci.TOOLCHAIN_SHA256, "trust_policy": proofci.policy_digest(),
                "resource_policy": {"timeout_seconds": 180, "cpu_seconds": 180,
                    "memory_bytes": 2147483648, "file_bytes": 2147483648, "processes": 256}}))
            image = os.environ.get("PROOFCI_TEST_IMAGE", "proofci-validator-local")
            local_report = root / "local.json"
            local = subprocess.run([sys.executable, str(HERE / "container.py"),
                "--envelope", str(envelope), "--baseline", str(baseline),
                "--snapshot", str(snapshot), "--report", str(local_report), "--image", image,
                "--validator-only"],
                timeout=240)
            self.assertEqual(local.returncode, 0, local_report.read_text())
            dispatched_report = root / "dispatched.json"
            dispatched = subprocess.run([sys.executable, str(HERE / "dispatch.py"),
                "--envelope", str(envelope), "--baseline", str(baseline),
                "--snapshot", str(snapshot), "--report", str(dispatched_report), "--image", image],
                timeout=420)
            self.assertEqual(dispatched.returncode, 0, dispatched_report.read_text())
            local_value = json.loads(local_report.read_text())
            dispatched_value = json.loads(dispatched_report.read_text())
            self.assertEqual(report.normalized(local_value, json.loads(envelope.read_text()),
                                               json.loads(baseline.read_text())),
                             report.normalized(dispatched_value, json.loads(envelope.read_text()),
                                               json.loads(baseline.read_text())))
            self.assertEqual(dispatched_value["dispatch"]["mode"], "isolated-worker")
            self.assertEqual(dispatched_value["dispatch"]["worker_status"], 0)
            self.assertEqual(dispatched_value["dispatch"]["final_status"], 0)


if __name__ == "__main__":
    unittest.main()
