import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

CLI = Path(__file__).with_name("proofci.py")
spec = importlib.util.spec_from_file_location("proofci", CLI)
proofci = importlib.util.module_from_spec(spec)
spec.loader.exec_module(proofci)


class CLITest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.snapshot = self.root / "snapshot"
        self.snapshot.mkdir()
        subprocess.run(["git", "-C", str(self.snapshot), "init", "-q"], check=True)
        subprocess.run(["git", "-C", str(self.snapshot), "config", "user.name", "ProofCI"], check=True)
        subprocess.run(["git", "-C", str(self.snapshot), "config", "user.email", "proofci@example.invalid"], check=True)
        subprocess.run(["git", "-C", str(self.snapshot), "remote", "add", "origin", "repo"], check=True)
        (self.snapshot / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 1")
        (self.root / "contract.json").write_text('{"rhs":"x + 1"}')
        sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
        baseline = {"version": 1, "candidate": "candidate.lean", "obligations": [
            {"id": "one", "policy": "required", "contract": "contract.json",
             "contract_sha256": sha(self.root / "contract.json"), "evidence": "missing"},
            {"id": "two", "policy": "advisory", "contract": "contract.json",
             "contract_sha256": sha(self.root / "contract.json"), "evidence": "missing2"}]}
        (self.root / "baseline.json").write_text(json.dumps(baseline))
        subprocess.run(["git", "-C", str(self.snapshot), "add", "."], check=True)
        subprocess.run(["git", "-C", str(self.snapshot), "commit", "-qm", "fixture"], check=True)
        head = subprocess.check_output(["git", "-C", str(self.snapshot), "rev-parse", "HEAD"], text=True).strip()
        envelope = {"version": 1, "repository": "repo", "head": head, "base": head,
                    "candidate_sha256": sha(self.snapshot / "candidate.lean"),
                    "baseline_sha256": sha(self.root / "baseline.json"), "dependency": sha(proofci.VALIDATOR / "core-dependencies.json"),
                    "toolchain": proofci.TOOLCHAIN_SHA256, "trust_policy": proofci.policy_digest(),
                    "resource_policy": {"timeout_seconds": 5, "cpu_seconds": 5,
                      "memory_bytes": 1000000000, "file_bytes": 1000000, "processes": 100}}
        (self.root / "envelope.json").write_text(json.dumps(envelope))

    def run_cli(self):
        p = subprocess.run([sys.executable, str(CLI), "--envelope", str(self.root / "envelope.json"),
          "--baseline", str(self.root / "baseline.json"), "--snapshot", str(self.snapshot),
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

    def test_empty_baseline_is_rejected_even_with_matching_digest(self):
        baseline_path = self.root / "baseline.json"
        baseline = json.loads(baseline_path.read_text())
        baseline["obligations"] = []
        baseline_path.write_text(json.dumps(baseline))
        envelope_path = self.root / "envelope.json"
        envelope = json.loads(envelope_path.read_text())
        envelope["baseline_sha256"] = hashlib.sha256(baseline_path.read_bytes()).hexdigest()
        envelope_path.write_text(json.dumps(envelope))
        status, report = self.run_cli()
        self.assertEqual(status, 2)
        self.assertEqual(report["reason"], "empty baseline")

    def test_unavailable_validator_accounts_for_remaining_obligations(self):
        (self.snapshot / "missing").mkdir()
        status, report = self.run_cli()
        self.assertEqual(status, 2)
        self.assertEqual([r["reason"] for r in report["results"]],
                         ["validation_unavailable", "missing_evidence"])

    def test_assume_unchanged_cannot_hide_modified_candidate(self):
        subprocess.run(["git", "-C", str(self.snapshot), "update-index", "--assume-unchanged", "candidate.lean"], check=True)
        (self.snapshot / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 2")
        path = self.root / "envelope.json"
        envelope = json.loads(path.read_text())
        envelope["candidate_sha256"] = hashlib.sha256((self.snapshot / "candidate.lean").read_bytes()).hexdigest()
        path.write_text(json.dumps(envelope))
        status, report = self.run_cli()
        self.assertEqual(status, 2)
        self.assertIn("committed content", report["reason"])

    def test_deadline_interrupts_host_side_snapshot_check(self):
        envelope_path = self.root / "envelope.json"
        envelope = json.loads(envelope_path.read_text())
        envelope["resource_policy"]["timeout_seconds"] = 1
        envelope_path.write_text(json.dumps(envelope))
        args = [str(CLI), "--envelope", str(envelope_path), "--baseline", str(self.root / "baseline.json"),
                "--snapshot", str(self.snapshot), "--toolchain", str(self.root / "toolchain"),
                "--report", str(self.root / "report.json")]
        started = time.monotonic()
        with patch.object(sys, "argv", args), patch.object(proofci, "verify_snapshot", side_effect=lambda *args: time.sleep(10)):
            status = proofci.main()
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(status, 2)
        self.assertEqual(report["reason"], "timeout")
        self.assertEqual(len(report["results"]), 2)
        self.assertLess(time.monotonic() - started, 5)

    def test_validator_container_name_is_not_an_evidence_filename(self):
        proof = self.root / "bundle"
        proof.mkdir()
        (proof / "solution.ndjson").write_bytes(b"evidence")
        bwrap = self.root / "bwrap"
        bwrap.write_bytes(b"bwrap")
        candidate = self.snapshot / "candidate.lean"
        contract = self.root / "contract.json"
        sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
        class Process:
            returncode = 0
            def communicate(self, timeout):
                return b'{"decision":"verified","reason":"accepted"}', b""
        limits = {"memory_bytes": 1000000000, "file_bytes": 1000000000, "processes": 100}
        with (patch.object(proofci, "BWRAP_SHA256", sha(bwrap)),
              patch.object(proofci.subprocess, "run") as create,
              patch.object(proofci.subprocess, "Popen", return_value=Process()) as popen):
            proofci.run_validator(proof, candidate, contract, self.root, bwrap, limits,
                                  time.monotonic() + 10, sha(candidate), sha(contract),
                                  {"solution.ndjson": sha(proof / "solution.ndjson")})
        command = create.call_args.args[0]
        name = command[command.index("--name") + 1]
        self.assertTrue(name.startswith("proofci-"))
        self.assertEqual(popen.call_args.args[0], ["docker", "start", "-a", name])
        for flag, expected in (("--network", "none"), ("--memory", "1000000000"),
                               ("--memory-swap", "1000000000"), ("--pids-limit", "100"), ("--cpus", "1")):
            self.assertEqual(command[command.index(flag) + 1], expected)


if __name__ == "__main__":
    unittest.main()
