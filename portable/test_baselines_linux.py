"""End-to-end baseline lifecycle with the pinned validator image."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

import baselines
import proofci

HERE = Path(__file__).resolve().parent
FIXTURES = HERE.parent / "experiments/source-binding/fixtures"


@unittest.skipUnless(os.environ.get("PROOFCI_TEST_PACKAGED"), "requires the pinned local image and Docker")
class LifecycleTest(unittest.TestCase):
    def test_activation_and_followup(self):
        with tempfile.TemporaryDirectory(prefix="proofci-lifecycle-") as temp:
            root = Path(temp)
            snapshot = root / "snapshot"
            snapshot.mkdir()
            shutil.copy(FIXTURES / "candidate.lean", snapshot / "candidate.lean")
            shutil.copytree(FIXTURES / "verified", snapshot / "evidence")
            manifest = {"version": 1, "candidate": "candidate.lean", "contracts": [{"id": "increment",
                "explanation": "Adds one", "owner": "maintainer", "formal_statement": "x + 1",
                "assumptions": [], "specification_closure": [], "implementation_bindings": ["target"],
                "policy": "required", "evidence": "evidence"}]}
            data = baselines.encoded(manifest)
            (snapshot / "contracts.json").write_bytes(data)
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
            head = commit("initial")
            sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
            envelope = {"version": 1, "repository": "https://example.invalid/fixture.git", "head": head, "base": head,
                "candidate_sha256": sha(snapshot / "candidate.lean"), "baseline_sha256": "0" * 64,
                "dependency": sha(proofci.VALIDATOR / "core-dependencies.json"), "toolchain": proofci.TOOLCHAIN_SHA256,
                "trust_policy": proofci.policy_digest(), "resource_policy": {"timeout_seconds": 180, "cpu_seconds": 180,
                "memory_bytes": 2147483648, "file_bytes": 2147483648, "processes": 256}}
            envelope_path, report, store = root / "envelope.json", root / "report.json", root / "store.db"
            def call(command, *extra):
                envelope_path.write_text(json.dumps(envelope))
                return subprocess.run([sys.executable, str(HERE / "baselines.py"), command, "--store", str(store),
                    "--snapshot", str(snapshot), "--envelope", str(envelope_path), "--report", str(report), *extra],
                    timeout=210).returncode
            self.assertEqual(call("activate", "--manifest-path", "contracts.json", "--reviewed-sha256", baselines.sha(data),
                                  "--approver", "maintainer"), 0, report.read_text())
            manifest["contracts"][0]["policy"] = "advisory"
            (snapshot / "contracts.json").write_bytes(baselines.encoded(manifest))
            envelope["head"] = commit("propose weakening")
            self.assertEqual(call("run"), 1, report.read_text())
            result = json.loads(report.read_text())
            self.assertEqual(result["results"][0]["decision"], "verified")
            self.assertEqual(result["proposed_guarantee_changes"][0]["fields"], ["policy"])
            (snapshot / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 2\n")
            envelope["head"] = commit("change implementation")
            envelope["candidate_sha256"] = sha(snapshot / "candidate.lean")
            self.assertEqual(call("run"), 1, report.read_text())
            self.assertEqual(json.loads(report.read_text())["results"][0]["decision"], "unproven")


if __name__ == "__main__":
    unittest.main()
