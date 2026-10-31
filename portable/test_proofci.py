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

    def test_report_classifies_accepted_refutation_and_preserves_contradictions(self):
        baseline_path = self.root / "baseline.json"
        baseline = json.loads(baseline_path.read_text())
        baseline["obligations"][0]["refutation"] = "refutation"
        baseline_path.write_text(json.dumps(baseline))
        for name in ("missing", "refutation"):
            directory = self.snapshot / name
            directory.mkdir()
            (directory / "manifest.json").write_text(name)
        subprocess.run(["git", "-C", str(self.snapshot), "add", "."], check=True)
        subprocess.run(["git", "-C", str(self.snapshot), "commit", "-qm", "evidence"], check=True)
        envelope_path = self.root / "envelope.json"
        envelope = json.loads(envelope_path.read_text())
        envelope["head"] = subprocess.check_output(["git", "-C", str(self.snapshot), "rev-parse", "HEAD"], text=True).strip()
        envelope["baseline_sha256"] = hashlib.sha256(baseline_path.read_bytes()).hexdigest()
        envelope_path.write_text(json.dumps(envelope))
        (self.root / "toolchain").mkdir()
        (self.root / "bwrap").touch()
        args = [str(CLI), "--envelope", str(envelope_path), "--baseline", str(baseline_path),
                "--snapshot", str(self.snapshot), "--toolchain", str(self.root / "toolchain"),
                "--bwrap", str(self.root / "bwrap"), "--report", str(self.root / "report.json")]
        def validate(proof, *args):
            decision = "violated" if proof.name == "refutation" else "unproven"
            return {"decision": decision, "reason": "accepted" if decision == "violated" else "proof_failed"}, {"manifest.json": proofci.digest(proof / "manifest.json")}
        with patch.object(sys, "argv", args), patch.object(proofci, "run_validator", side_effect=validate):
            self.assertEqual(proofci.main(), 1)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(report["results"][0]["decision"], "violated")
        self.assertEqual(report["results"][0]["evidence"], "refutation")
        self.assertEqual(report["property_counts"]["violated"], 1)
        self.assertTrue(any(c["path"].startswith("refutation/") and c["scope"] == "proof_evidence"
                            for c in report["coverage"]["changes"]))
        self.assertEqual(report["status"], "blocked")
        # The same checked violation is visible but does not block an advisory obligation.
        baseline["obligations"][0]["policy"] = "advisory"
        baseline["obligations"][1]["policy"] = "required"
        baseline["obligations"][1]["evidence"] = "missing"
        baseline_path.write_text(json.dumps(baseline))
        envelope["baseline_sha256"] = hashlib.sha256(baseline_path.read_bytes()).hexdigest()
        envelope_path.write_text(json.dumps(envelope))
        def advisory(proof, *args):
            decision = "violated" if proof.name == "refutation" else "verified"
            return {"decision": decision, "reason": "accepted"}, {"manifest.json": proofci.digest(proof / "manifest.json")}
        # Give the advisory obligation only the refutation; keep a separate required proof.
        baseline["obligations"][0]["evidence"] = "absent"
        baseline_path.write_text(json.dumps(baseline))
        envelope["baseline_sha256"] = hashlib.sha256(baseline_path.read_bytes()).hexdigest()
        envelope_path.write_text(json.dumps(envelope))
        with patch.object(sys, "argv", args), patch.object(proofci, "run_validator", side_effect=advisory):
            self.assertEqual(proofci.main(), 0)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual([r["decision"] for r in report["results"]], ["violated", "verified"])
        baseline["obligations"][0]["policy"] = "required"
        baseline["obligations"][0]["evidence"] = "missing"
        baseline["obligations"][1]["policy"] = "advisory"
        baseline_path.write_text(json.dumps(baseline))
        envelope["baseline_sha256"] = hashlib.sha256(baseline_path.read_bytes()).hexdigest()
        envelope_path.write_text(json.dumps(envelope))
        def contradictory(proof, *args):
            decision = "violated" if proof.name == "refutation" else "verified"
            return {"decision": decision, "reason": "accepted"}, {"manifest.json": proofci.digest(proof / "manifest.json")}
        with patch.object(sys, "argv", args), patch.object(proofci, "run_validator", side_effect=contradictory):
            self.assertEqual(proofci.main(), 2)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(report["results"][0]["reason"], "contradictory_evidence")
        self.assertEqual([e["evidence"] for e in report["results"][0]["submissions"]], ["missing", "refutation"])

        def refutation_timeout(proof, *args):
            if proof.name == "refutation":
                raise subprocess.TimeoutExpired("refutation", 120)
            return {"decision": "verified", "reason": "accepted"}, {"manifest.json": proofci.digest(proof / "manifest.json")}
        with patch.object(sys, "argv", args), patch.object(proofci, "run_validator", side_effect=refutation_timeout):
            self.assertEqual(proofci.main(), 1)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(report["results"][0]["decision"], "unproven")
        self.assertEqual(report["results"][0]["reason"], "obligation_budget_exhausted")

    def test_search_exhaustion_is_a_nonpassing_unproven_reason(self):
        search = self.root / "search.json"
        search.write_text(json.dumps({"version": 1, "exhausted": ["one"]}))
        args = [str(CLI), "--envelope", str(self.root / "envelope.json"), "--baseline", str(self.root / "baseline.json"),
                "--snapshot", str(self.snapshot), "--toolchain", str(self.root / "toolchain"),
                "--report", str(self.root / "report.json"), "--search-results", str(search)]
        with patch.object(sys, "argv", args):
            self.assertEqual(proofci.main(), 1)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(report["results"][0]["reason"], "search_exhausted")
        self.assertEqual(report["results"][0]["decision"], "unproven")
        self.assertEqual(report["results"][1]["reason"], "missing_evidence")
    def commit_changes(self):
        subprocess.run(["git", "-C", str(self.snapshot), "add", "--all"], check=True)
        subprocess.run(["git", "-C", str(self.snapshot), "commit", "-qm", "changes"], check=True)
        head = subprocess.check_output(["git", "-C", str(self.snapshot), "rev-parse", "HEAD"], text=True).strip()
        envelope_path = self.root / "envelope.json"
        envelope = json.loads(envelope_path.read_text())
        envelope["head"] = head
        envelope["candidate_sha256"] = hashlib.sha256((self.snapshot / "candidate.lean").read_bytes()).hexdigest()
        envelope_path.write_text(json.dumps(envelope))

    def test_complete_diff_and_admission_diagnostics(self):
        for i in range(310):
            (self.snapshot / f"file-{i}.txt").write_text("untrusted")
        (self.snapshot / "uncovered\nname.lean").write_text("def target (x : Nat) : Nat := x + 2")
        (self.snapshot / "unsupported.lean").write_text("import Evil\ndef target (x : Nat) : Nat := x")
        self.commit_changes()
        status, report = self.run_cli()
        self.assertEqual(status, 1)
        self.assertEqual(len(report["coverage"]["changes"]), 312)
        self.assertEqual(report["coverage"]["uncovered_supported_symbols"],
                         [{"path": "uncovered\nname.lean", "symbol": "target"}])
        self.assertTrue(any(x["path"] == "unsupported.lean" for x in report["coverage"]["unsupported_changed_code"]))
        self.assertEqual([r["reason"] for r in report["results"]], ["missing_evidence"] * 2)
        self.assertEqual(report["support"]["policy_version"], "lean-target-v1")

    def test_unsupported_required_dependency_blocks_without_evidence(self):
        (self.snapshot / "candidate.lean").write_text("import Evil\ndef target (x : Nat) : Nat := x")
        self.commit_changes()
        status, report = self.run_cli()
        self.assertEqual(status, 1)
        self.assertEqual([r["reason"] for r in report["results"]], ["unsupported_semantics"] * 2)
        self.assertIn("candidate must", report["support"]["unsupported_dependency"]["reason"])
        self.assertEqual(report["results"][0]["property"], "target x = x + 1")

    def test_diff_does_not_execute_external_diff_or_hooks(self):
        (self.snapshot / "change.txt").write_text("change")
        self.commit_changes()
        marker = self.root / "executed"
        script = self.root / "trap"
        script.write_text("#!/bin/sh\ntouch '" + str(marker) + "'\n")
        script.chmod(0o755)
        subprocess.run(["git", "-C", str(self.snapshot), "config", "diff.external", str(script)], check=True)
        hooks = self.root / "hooks"
        hooks.mkdir()
        (hooks / "post-checkout").symlink_to(script)
        subprocess.run(["git", "-C", str(self.snapshot), "config", "core.hooksPath", str(hooks)], check=True)
        status, report = self.run_cli()
        self.assertEqual(status, 1)
        self.assertEqual(len(report["coverage"]["changes"]), 1)
        self.assertFalse(marker.exists())

    def test_oversized_candidate_is_unproven(self):
        (self.snapshot / "candidate.lean").write_text("x" * 17000)
        self.commit_changes()
        status, report = self.run_cli()
        self.assertEqual(status, 1)
        self.assertEqual(report["results"][0]["reason"], "unsupported_semantics")
        self.assertIn("input limit", report["results"][0]["detail"])

    def test_deleted_unsupported_code_and_docs_are_distinguished(self):
        (self.snapshot / "old.lean").write_text("import Std")
        self.commit_changes()
        (self.snapshot / "old.lean").unlink()
        (self.snapshot / "README.md").write_text("documentation")
        self.commit_changes()
        envelope_path = self.root / "envelope.json"
        envelope = json.loads(envelope_path.read_text())
        envelope["base"] = subprocess.check_output(["git", "-C", str(self.snapshot), "rev-parse", "HEAD^"], text=True).strip()
        envelope_path.write_text(json.dumps(envelope))
        status, report = self.run_cli()
        self.assertEqual(status, 1)
        self.assertEqual([x["path"] for x in report["coverage"]["unsupported_changed_code"]], ["old.lean"])

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

    def test_host_validator_refuses_unlimited_execution(self):
        proof = self.root / "bundle"
        proof.mkdir()
        (proof / "solution.ndjson").write_bytes(b"evidence")
        bwrap = self.root / "bwrap"
        bwrap.write_bytes(b"bwrap")
        candidate = self.snapshot / "candidate.lean"
        contract = self.root / "contract.json"
        sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
        limits = {"memory_bytes": 1000000000, "file_bytes": 1000000000, "processes": 100}
        with (patch.object(proofci, "BWRAP_SHA256", sha(bwrap)),
              patch.dict("os.environ", {}, clear=True)):
            with self.assertRaisesRegex(RuntimeError, "resource-limited"):
                proofci.run_validator(proof, candidate, contract, self.root, bwrap, limits,
                                      time.monotonic() + 10, sha(candidate), sha(contract),
                                      {"solution.ndjson": sha(proof / "solution.ndjson")})



if __name__ == "__main__":
    unittest.main()
