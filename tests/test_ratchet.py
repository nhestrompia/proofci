import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import check  # noqa: E402

F = "src/ledger.ts::transfer"


class DowngradeTests(unittest.TestCase):
    def test_proved_to_tested_is_a_downgrade(self):
        [d] = check._downgrades({F: ("tested", "did not check")}, {F: "proved"}, set())
        self.assertEqual((d["function"], d["was"], d["now"], d["accepted"], d["reason"]),
                         (F, "proved", "tested", False, "did not check"))

    def test_proved_to_proved_is_not(self):
        self.assertEqual(check._downgrades({F: ("proved", "")}, {F: "proved"}, set()), [])

    def test_tested_to_tested_is_not(self):
        self.assertEqual(check._downgrades({F: ("tested", "")}, {F: "tested"}, set()), [])
        self.assertEqual(check._downgrades({F: ("unsupported", "")}, {F: "not proved"}, set()), [])

    def test_proved_to_unsupported_or_removed(self):
        for now in (("unsupported", "only `number` operands"), ("removed", "the function is not in the pull request's code")):
            [d] = check._downgrades({F: now}, {F: "proved"}, set())
            self.assertEqual((d["was"], d["now"]), ("proved", now[0]))

    def test_unknown_base_fails_closed(self):
        [d] = check._downgrades({F: ("tested", "did not check")}, {F: "unknown"}, set())
        self.assertEqual((d["was"], d["accepted"]), ("unknown", False))
        self.assertIn("unknown", d["reason"])
        # ...but a function proved now cannot be a downgrade however the base check went.
        self.assertEqual(check._downgrades({F: ("proved", "")}, {F: "unknown"}, set()), [])

    def test_accepted(self):
        [d] = check._downgrades({F: ("tested", "")}, {F: "proved"}, {F})
        self.assertTrue(d["accepted"])

    def test_blocks_the_report(self):
        report = check.Report(language="typescript")
        report.outcomes = [check.Outcome("fees", "capped", "f", "fee_capped", True, check.VERIFIED)]
        self.assertTrue(report.passed)
        report.downgrades = [{"function": F, "was": "proved", "now": "tested", "reason": "", "accepted": False}]
        self.assertFalse(report.passed)
        report.downgrades[0]["accepted"] = True
        self.assertTrue(report.passed)


if __name__ == "__main__":
    unittest.main()
