"""Real replay, enabled only when the pinned Linux toolchain is provided."""
import os
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


if __name__ == "__main__":
    unittest.main()
