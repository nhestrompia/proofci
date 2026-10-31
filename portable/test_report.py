import copy
import unittest

import report


class ReportContractTests(unittest.TestCase):
    def setUp(self):
        self.envelope = {"candidate_sha256": "a" * 64}
        self.baseline = {"obligations": [{"id": "one", "policy": "required",
            "contract_sha256": "b" * 64, "evidence": "evidence"}]}
        validation = {"decision": "verified", "candidate_sha256": "a" * 64,
                      "contract_sha256": "b" * 64}
        self.value = {"version": 1, "status": "passed", "envelope": self.envelope,
                      "results": [{"id": "one", "policy": "required", "evidence": "evidence",
                                   "decision": "verified", "reason": "accepted",
                                   "validation": validation}],
                      "property_counts": {"verified": 1, "violated": 0, "unproven": 0}}

    def test_normalized_outcome_discards_worker_metadata(self):
        value = copy.deepcopy(self.value)
        value["started_at"] = 1
        value["finished_at"] = 2
        self.assertEqual(report.normalized(value, self.envelope, self.baseline), {
            "status": "passed", "results": [{"id": "one", "policy": "required",
                "decision": "verified", "reason": "accepted", "evidence": "evidence",
                "evidence_sha256": {}}],
            "property_counts": {"verified": 1, "violated": 0, "unproven": 0}})

    def test_forged_accepted_result_without_independent_validation_is_rejected(self):
        value = copy.deepcopy(self.value)
        del value["results"][0]["validation"]
        with self.assertRaisesRegex(ValueError, "independent validation"):
            report.validate(value, self.envelope, self.baseline)

    def test_pass_cannot_hide_a_required_unproven_result(self):
        value = copy.deepcopy(self.value)
        value["status"] = "passed"
        value["results"][0]["decision"] = "unproven"
        value["results"][0]["reason"] = "missing_evidence"
        value["property_counts"] = {"verified": 0, "violated": 0, "unproven": 1}
        with self.assertRaisesRegex(ValueError, "passed with a blocking"):
            report.validate(value, self.envelope, self.baseline)


if __name__ == "__main__":
    unittest.main()
