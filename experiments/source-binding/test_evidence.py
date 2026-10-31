import hashlib
import base64
import io
import json
import sys
import time
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import evidence


META = {
    "meta": {
        "exporter": {"name": "lean4export", "version": "3.1.0"},
        "format": {"version": "3.1.0"},
        "lean": {"githash": evidence.LEAN_COMMIT, "version": "4.35.0"},
    }
}


def export(*, challenge=False, extra=None):
    records = [META]
    for number, name, kind in (
        (1, "target", "def"),
        (2, "contract", "thm"),
    ):
        records.extend(({"in": number, "str": {"pre": 0, "str": name}}, {kind: {"name": number}}))
    if challenge:
        records.extend(({"in": 3, "str": {"pre": 0, "str": "sorryAx"}}, {"axiom": {"name": 3}}))
    if extra:
        records.append(extra)
    return "".join(json.dumps(record, separators=(",", ":")) + "\n" for record in records).encode()


def digest(data):
    return hashlib.sha256(data).hexdigest()


class EvidenceBundleTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        root = Path(self.temp.name)
        self.candidate = root / "candidate.lean"
        self.contract = root / "contract.json"
        self.bundle = root / "bundle"
        self.bundle.mkdir()
        self.candidate.write_text("def target (x : Nat) : Nat := x + 1\n")
        self.contract.write_text('{"rhs":"x + 1"}\n')

    def write_bundle(self, **overrides):
        solution = overrides.pop("solution", b"import CandidateCheck\ntheorem contract := by rfl\n")
        challenge_export = overrides.pop("challenge_export", export(challenge=True))
        solution_export = overrides.pop("solution_export", export())
        files = {
            "solution.lean": solution,
            "challenge.ndjson": challenge_export,
            "solution.ndjson": solution_export,
        }
        for name, contents in files.items():
            (self.bundle / name).write_bytes(contents)
        manifest = {
            "version": 1,
            "candidate_sha256": digest(self.candidate.read_bytes()),
            "contract_sha256": digest(self.contract.read_bytes()),
            "solution_sha256": digest(solution),
            "challenge_export_sha256": digest(challenge_export),
            "solution_export_sha256": digest(solution_export),
            "claimed_decision": "verified",
        }
        manifest.update(overrides)
        (self.bundle / "manifest.json").write_text(json.dumps(manifest))

    def test_valid_bundle_is_admitted_before_toolchain_replay(self):
        self.write_bundle()
        loaded = evidence.load_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(loaded.candidate_sha256, digest(self.candidate.read_bytes()))
        self.assertEqual(loaded.permitted_axioms, evidence.PERMITTED_AXIOMS)

    def test_refutation_challenge_is_the_negation_of_the_approved_proposition(self):
        self.write_bundle(claimed_decision="violated")
        bundle = evidence.load_bundle(self.bundle, self.candidate, self.contract)
        _, _, challenge, _ = evidence._sources(bundle)
        self.assertIn("¬ (∀ x : Nat, target x = x + 1)", challenge)

    def test_witness_is_bound_to_a_concrete_failure(self):
        self.write_bundle(claimed_decision="violated", witness=2)
        bundle = evidence.load_bundle(self.bundle, self.candidate, self.contract)
        _, _, challenge, _ = evidence._sources(bundle)
        self.assertIn("let x : Nat := 2; ¬ (target x = x + 1)", challenge)

    def test_witness_forms_are_strictly_admitted(self):
        for witness in (-1, True, "0", 1000001):
            with self.subTest(witness=witness):
                self.write_bundle(claimed_decision="violated", witness=witness)
                self.assertEqual(evidence.validate_bundle(self.bundle, self.candidate, self.contract)["reason"], "invalid_evidence")

    def test_wrong_candidate_refutation_is_invalid(self):
        self.write_bundle(claimed_decision="violated", candidate_sha256="0" * 64)
        self.assertEqual(evidence.validate_bundle(self.bundle, self.candidate, self.contract)["reason"], "invalid_evidence")

    def test_conditional_witness_requires_precondition_and_failure(self):
        self.contract.write_text('{"rhs":"x", "precondition":{"lhs":"x", "op":"<", "rhs":"3"}}')
        self.write_bundle(claimed_decision="violated", witness=2)
        bundle = evidence.load_bundle(self.bundle, self.candidate, self.contract)
        _, _, challenge, _ = evidence._sources(bundle)
        self.assertIn("(x < 3) → target x = x", challenge)
        self.assertIn("(x < 3) ∧ ¬ (target x = x)", challenge)

    def test_candidate_hash_mismatch_is_invalid_evidence(self):
        self.write_bundle(candidate_sha256="0" * 64)
        result = evidence.validate_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "invalid_evidence")

    def test_bundle_cannot_supply_validation_policy(self):
        self.write_bundle(policy={"permitted_axioms": ["sorryAx"], "checker": ["evil"]})
        result = evidence.validate_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "invalid_evidence")

    def test_solution_sorry_dependency_is_rejected(self):
        solution_export = export(extra={"in": 4, "str": {"pre": 0, "str": "sorryAx"}})
        solution_export += b'{"axiom":{"name":4}}\n'
        self.write_bundle(solution_export=solution_export)
        result = evidence.validate_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "invalid_evidence")

    def test_custom_axiom_is_rejected_transitively(self):
        custom = export(extra={"in": 4, "str": {"pre": 0, "str": "cheat"}})
        custom += b'{"axiom":{"name":4}}\n'
        self.write_bundle(solution_export=custom)
        result = evidence.validate_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "invalid_evidence")

    def test_unavailable_pinned_validator_is_not_a_verified_result(self):
        self.write_bundle()
        result = evidence.validate_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "validation_unavailable")

    def test_checker_disagreement_is_not_downgraded_to_unproven(self):
        with self.assertRaises(evidence.CheckerDisagreement):
            evidence.classify_checker(0, "nanoda kernel accepts the solution")

    def test_checker_failure_is_distinct_from_checker_disagreement(self):
        result = evidence.classify_checker(1, "Your solution is not okay!")
        self.assertEqual(result, "unproven")

    def test_checker_infrastructure_failure_is_not_proof_rejection(self):
        with self.assertRaises(evidence.BuildFailure):
            evidence.classify_checker(1, "Child exited with 134")

    def test_pinned_checker_rejection_is_unproven(self):
        result = evidence.classify_checker(
            1,
            "Lean default kernel rejected the solution\n"
            "nanoda kernel rejected the solution\n",
        )
        self.assertEqual(result, "unproven")

    def test_acceptance_and_rejection_is_contradictory(self):
        with self.assertRaises(evidence.ContradictoryEvidence):
            evidence.classify_checker(
                0,
                "Lean default kernel accepts the solution\n"
                "nanoda kernel accepts the solution\n"
                "Lean default kernel rejected the solution\n",
            )

    def test_checker_acceptance_with_failure_status_is_contradictory(self):
        with self.assertRaises(evidence.ContradictoryEvidence):
            evidence.classify_checker(
                1,
                "nanoda kernel accepts the solution\n"
                "Lean default kernel accepts the solution\n",
            )

    def test_checker_infrastructure_failure_is_a_build_failure(self):
        with self.assertRaises(evidence.BuildFailure):
            evidence.classify_checker(2, "")

    def test_final_sandbox_mounts_precede_the_lake_command(self):
        with tempfile.TemporaryDirectory() as tmp:
            workspace = Path(tmp) / "workspace"
            workspace.mkdir()
            policy = Path(tmp) / "comparator.json"
            policy.write_text("{}")
            with (patch.object(evidence.platform, "system", return_value="Linux"),
                  patch.object(evidence.platform, "machine", return_value="aarch64"),
                  patch.object(evidence.shutil, "which", return_value="/usr/bin/bwrap")):
                command = evidence._sandbox_prefix(
                    Path(tmp), workspace, policy, read_only_sources=True
                )
        self.assertEqual(command[command.index("--setenv") + 1], "HOME")
        separator = command.index("--")
        self.assertEqual(command[separator + 1], "/lean/bin/lake")
        self.assertTrue(all(command.index(f"/workspace/{name}") < separator for name in (
            "Candidate.lean", "Challenge.lean", "Solution.lean"
        )))
        self.assertIn("--tmpfs", command)
        self.assertLess(command.index("--tmpfs", command.index("/workspace")), separator)

    def test_untrusted_non_utf8_checker_output_is_normalized(self):
        class FakeProcess:
            returncode = 1
            stdout = io.BytesIO(b"\xff")
            stderr = io.BytesIO(b"\xfe")

            def wait(self, timeout=None):
                return self.returncode

            def kill(self):
                return None

        with (patch.object(evidence, "_sandbox_prefix", return_value=["bwrap"]),
              patch.object(evidence.subprocess, "Popen", return_value=FakeProcess())):
            status, output = evidence._run(
                Path("/toolchain"), Path("/workspace"), Path("/policy"),
                ("comparator",), allow_failure=True, combined=True
            )
        self.assertEqual(status, 1)
        self.assertEqual(output, "��")

    def test_timeout_terminates_descendants_holding_output_open(self):
        program = ("import subprocess,sys,time; "
                   "subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)']); "
                   "time.sleep(30)")
        with patch.object(evidence, "_sandbox_prefix", return_value=[sys.executable, "-c", program]):
            start = time.monotonic()
            with self.assertRaises(evidence.ValidationUnavailable):
                evidence._run(Path("/unused"), Path("/unused"), Path("/unused"), (), timeout=0.2)
        self.assertLess(time.monotonic() - start, 5)

    def test_timeout_applies_after_parent_exits_with_output_open(self):
        program = ("import subprocess,sys; "
                   "subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)'])")
        with patch.object(evidence, "_sandbox_prefix", return_value=[sys.executable, "-c", program]):
            start = time.monotonic()
            with self.assertRaises(evidence.ValidationUnavailable):
                evidence._run(Path("/unused"), Path("/unused"), Path("/unused"), (), timeout=0.2)
        self.assertLess(time.monotonic() - start, 5)

    def test_fixed_replay_output_preserves_exports(self):
        challenge = b'{"meta":1}\n\xff\n'
        solution = b'{"meta":2}\n'
        challenge_output = evidence.CHALLENGE_MARKER + base64.b64encode(challenge)
        solution_output = evidence.SOLUTION_MARKER + base64.b64encode(solution)
        self.assertEqual(
            evidence._extract_export(challenge_output, evidence.CHALLENGE_MARKER), challenge
        )
        self.assertEqual(
            evidence._extract_export(solution_output, evidence.SOLUTION_MARKER), solution
        )

    def test_workspace_failure_is_normalized_to_validation_unavailable(self):
        self.write_bundle()
        with (patch.object(evidence, "_verify_toolchain", return_value=Path("/toolchain")),
              patch.object(evidence.tempfile, "TemporaryDirectory",
                           side_effect=OSError("temporary storage unavailable"))):
            result = evidence.validate_bundle(
                self.bundle, self.candidate, self.contract, toolchain="/toolchain"
            )
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "validation_unavailable")

    def test_malformed_export_is_normalized_to_invalid_evidence(self):
        self.write_bundle()
        malformed = b'{"meta":null}\n'
        (self.bundle / "challenge.ndjson").write_bytes(malformed)
        manifest = json.loads((self.bundle / "manifest.json").read_text())
        manifest["challenge_export_sha256"] = digest(malformed)
        (self.bundle / "manifest.json").write_text(json.dumps(manifest))
        result = evidence.validate_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "invalid_evidence")

    def test_deeply_nested_manifest_is_normalized_to_invalid_evidence(self):
        self.write_bundle()
        manifest = json.loads((self.bundle / "manifest.json").read_text())
        nested = "0"
        for _ in range(2000):
            nested = "[" + nested + "]"
        fields = []
        for key, value in manifest.items():
            encoded = nested if key == "version" else json.dumps(value)
            fields.append(json.dumps(key) + ":" + encoded)
        (self.bundle / "manifest.json").write_text("{" + ",".join(fields) + "}")
        result = evidence.validate_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "invalid_evidence")

    def test_changed_contract_cannot_reuse_bundle(self):
        self.write_bundle()
        self.contract.write_text('{"rhs":"x + 2"}\n')
        result = evidence.validate_bundle(self.bundle, self.candidate, self.contract)
        self.assertEqual(result["decision"], "unproven")
        self.assertEqual(result["reason"], "invalid_evidence")


if __name__ == "__main__":
    unittest.main()
