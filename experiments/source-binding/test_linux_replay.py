"""Real replay, enabled only when the pinned Linux toolchain is provided."""
import os
import hashlib
import json
import shutil
import tempfile
from pathlib import Path
import unittest

import evidence


@unittest.skipUnless(os.environ.get("PROOFCI_TEST_TOOLCHAIN"), "requires pinned Linux arm64 toolchain")
class LinuxReplayTests(unittest.TestCase):
    def test_verified_bundle_passes_both_checkers(self):
        fixtures = Path(__file__).with_name("fixtures")
        result = evidence.validate_bundle(
            fixtures / "verified", fixtures / "candidate.lean", fixtures / "contract.json",
            Path(os.environ["PROOFCI_TEST_TOOLCHAIN"]),
        )
        self.assertEqual(result["decision"], "verified", result)


    def test_negation_passes_both_checkers(self):
        fixtures = Path(__file__).with_name("fixtures")
        result = evidence.validate_bundle(
            fixtures / "refuted", fixtures / "candidate.lean", fixtures / "violated-contract.json",
            Path(os.environ["PROOFCI_TEST_TOOLCHAIN"]),
        )
        self.assertEqual(result["decision"], "violated", result)

    def test_failed_proof_is_unproven(self):
        fixtures = Path(__file__).with_name("fixtures")
        with tempfile.TemporaryDirectory() as temp:
            bundle = Path(temp) / "bundle"
            shutil.copytree(fixtures / "violated", bundle)
            solution = bundle / "solution.lean"
            solution.write_text("import CandidateCheck\ntheorem contract : False := by rfl\n")
            manifest = json.loads((bundle / "manifest.json").read_text())
            manifest["solution_sha256"] = hashlib.sha256(solution.read_bytes()).hexdigest()
            (bundle / "manifest.json").write_text(json.dumps(manifest))
            result = evidence.validate_bundle(bundle, fixtures / "candidate.lean", fixtures / "violated-contract.json",
                                              Path(os.environ["PROOFCI_TEST_TOOLCHAIN"]))
            self.assertEqual((result["decision"], result["reason"]), ("unproven", "proof_failed"), result)

    def test_conditional_witness_checks_precondition(self):
        fixtures = Path(__file__).with_name("fixtures")
        toolchain = Path(os.environ["PROOFCI_TEST_TOOLCHAIN"])
        result = evidence.validate_bundle(fixtures / "conditional", fixtures / "candidate.lean",
                                          fixtures / "conditional-contract.json", toolchain)
        self.assertEqual(result["decision"], "violated", result)
        result = evidence.validate_bundle(fixtures / "false-precondition", fixtures / "candidate.lean",
                                          fixtures / "conditional-contract.json", toolchain)
        self.assertEqual((result["decision"], result["reason"]), ("unproven", "proof_failed"), result)

    def test_conditional_positive_proof_passes_both_checkers(self):
        fixtures = Path(__file__).with_name("fixtures")
        result = evidence.validate_bundle(fixtures / "conditional-verified", fixtures / "candidate.lean",
                                          fixtures / "conditional-verified-contract.json",
                                          Path(os.environ["PROOFCI_TEST_TOOLCHAIN"]))
        self.assertEqual(result["decision"], "verified", result)

    def test_concrete_witness_passes_both_checkers(self):
        fixtures = Path(__file__).with_name("fixtures")
        result = evidence.validate_bundle(
            fixtures / "violated", fixtures / "candidate.lean", fixtures / "violated-contract.json",
            Path(os.environ["PROOFCI_TEST_TOOLCHAIN"]),
        )
        self.assertEqual(result["decision"], "violated", result)
        self.assertEqual(result["witness"], 0)



if __name__ == "__main__":
    unittest.main()
