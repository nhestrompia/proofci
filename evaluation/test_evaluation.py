"""Offline checks for the evaluation corpus, oracle, scenario plans and aggregation."""
import copy
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))

import aggregate  # noqa: E402
import evaluation_corpus as corpus  # noqa: E402
import evaluate  # noqa: E402
import oracle  # noqa: E402

POLICY_ESCAPES = ("simp", "omega", "decide", "cases ", "rcases", "native_decide", "sorry", "axiom")


class OracleTests(unittest.TestCase):
    def test_polynomial_normalization(self):
        self.assertEqual(oracle.polynomial("x * (x + 1) + 2"), {2: 1, 1: 1, 0: 2})
        self.assertEqual(oracle.polynomial("x * (x + 0 + 1) + 2"), oracle.polynomial("x * x + x + 1 + 1"))
        self.assertEqual(oracle.polynomial("0 * x"), {})
        with self.assertRaises(ValueError):
            oracle.polynomial("x - 1")

    def test_judgements_and_smallest_counterexample(self):
        self.assertEqual(oracle.judge("def target (x : Nat) : Nat := x * 3 + 2\n", {"rhs": "x * 2 + x + 2"}), (True, None))
        self.assertEqual(oracle.judge("def target (x : Nat) : Nat := x * x + 2 * x + 2\n", {"rhs": "x * 3 + 2"}), (False, 2))
        bounded = {"rhs": "x * 2 + 2", "precondition": {"lhs": "x", "op": "<", "rhs": "2"}}
        self.assertEqual(oracle.judge("def target (x : Nat) : Nat := x * x + 2\n", bounded), (False, 1))
        at_most = {"rhs": "x * x * 2 + 5", "precondition": {"lhs": "x", "op": "≤", "rhs": "1"}}
        self.assertEqual(oracle.judge("def target (x : Nat) : Nat := (x + 1) * 2 + 3\n", at_most), (True, None))

    def test_rejects_unbounded_preconditions(self):
        with self.assertRaises(ValueError):
            oracle.precondition_domain({"lhs": "3", "op": "<", "rhs": "x"})


class CorpusTests(unittest.TestCase):
    def setUp(self):
        self.packages, self.scenarios = corpus.load()

    def test_corpus_is_well_formed(self):
        self.assertEqual(corpus.check(self.packages, self.scenarios), [])

    def test_corpus_size_and_coverage(self):
        self.assertGreaterEqual(sum(len(p["properties"]) for p in self.packages.values()), 30)
        self.assertEqual({p["domain"] for p in self.packages.values()}, corpus.REQUIRED_DOMAINS)
        self.assertEqual({s["category"] for s in self.scenarios}, corpus.CATEGORIES)

    def test_corpus_matches_its_freeze_lock(self):
        lock, problems = corpus.verify_lock()
        self.assertIsNotNone(lock)
        self.assertEqual(problems, [])

    def test_reviewed_truth_must_agree_with_oracle(self):
        packages = copy.deepcopy(self.packages)
        packages["arithmetic"]["properties"][0]["truth"]["violating"] = True
        problems = corpus.check(packages, self.scenarios)
        self.assertTrue(any("disagrees with oracle" in p for p in problems))

    def test_fresh_proof_of_false_property_is_rejected(self):
        scenarios = copy.deepcopy(self.scenarios)
        scenario = next(s for s in scenarios if s["id"] == "arithmetic-intentional-violation")
        scenario["head"]["evidence"]["fee-definition"] = "fresh"
        self.assertTrue(any("does not hold" in p for p in corpus.check(self.packages, scenarios)))


class PlanTests(unittest.TestCase):
    def setUp(self):
        self.packages, self.scenarios = corpus.load()

    def test_every_scenario_has_constructible_evidence_plans(self):
        for spec in self.scenarios:
            scenario = evaluate.Scenario(spec, self.packages)
            self.assertTrue(scenario.jobs(), spec["id"])

    def test_reviewed_proofs_avoid_policy_escapes(self):
        for package in self.packages.values():
            for prop in package["properties"]:
                for body in evaluate.positive_bodies(prop["contract"]):
                    self.assertFalse([w for w in POLICY_ESCAPES if w in body], body)
                for kind in ("base", "equivalent", "violating"):
                    if not prop["truth"][kind]:
                        body = evaluate.refutation_job(package["candidates"][kind], prop["contract"])["bodies"][0]
                        self.assertFalse([w for w in POLICY_ESCAPES if w in body], body)

    def test_bounded_proof_nests_one_case_per_value(self):
        contract = {"rhs": "x * 2 + 5", "precondition": {"lhs": "x", "op": "<", "rhs": "3"}}
        body = evaluate.positive_bodies(contract)[-1]
        self.assertEqual(body.count("Nat.casesOn"), 3)
        self.assertEqual(body.count("Nat.le_of_succ_le_succ"), 3)

    def test_refutation_requires_a_false_property(self):
        package = self.packages["arithmetic"]
        with self.assertRaises(ValueError):
            evaluate.refutation_job(package["candidates"]["base"], package["properties"][0]["contract"])

    def test_forgery_post_processing(self):
        class Cache(evaluate.EvidenceCache):
            def __init__(self):
                pass

            def path(self, job):
                return self.directory

        import tempfile
        with tempfile.TemporaryDirectory() as temp:
            cache = Cache()
            cache.directory = Path(temp)
            manifest = {"claimed_decision": "violated", "witness": 1, "solution_sha256": "0" * 64}
            (cache.directory / "manifest.json").write_text(json.dumps(manifest))
            (cache.directory / "solution.lean").write_text("proof")
            flipped = cache.materialize({}, {"manifest": {"claimed_decision": "verified"}, "drop": ["witness"]})
            self.assertEqual(json.loads(flipped["manifest.json"]), {"claimed_decision": "verified", "solution_sha256": "0" * 64})
            edited = cache.materialize({}, {"solution": b"other"})
            self.assertEqual(json.loads(edited["manifest.json"])["solution_sha256"], evaluate.sha(b"other"))
            extra = cache.materialize({}, {"extra": {"notes.txt": b"x"}})
            self.assertIn("notes.txt", extra)


class FakeCache:
    built_keys = set()

    def key(self, job):
        return evaluate.sha(json.dumps(job, sort_keys=True).encode())


def report(results, status="blocked", **extra):
    return {"status": status, "results": results, **extra}


class RecordTests(unittest.TestCase):
    def setUp(self):
        packages, scenarios = corpus.load()
        self.packages = packages
        self.specs = {s["id"]: s for s in scenarios}

    def scenario(self, name):
        return evaluate.Scenario(self.specs[name], self.packages)

    def test_false_verified_and_gate_are_detected(self):
        scenario = self.scenario("forged-shadow-definition")
        forged = report([{"id": "fee-definition", "decision": "verified", "reason": "accepted"}], status="passed")
        run = evaluate.record(scenario, "deterministic", 1, 0, 1.0, forged, "", None, None, "b", "h", FakeCache())
        kinds = {item["kind"] for item in run["false_acceptances"]}
        self.assertEqual(kinds, {"false_verified", "false_passing_gate"})
        self.assertFalse(run["expectation"]["met"])

    def test_expected_rejection_is_met(self):
        scenario = self.scenario("forged-shadow-definition")
        rejected = report([{"id": "fee-definition", "decision": "unproven", "reason": "invalid_evidence"}])
        run = evaluate.record(scenario, "deterministic", 1, 1, 1.0, rejected, "", None, None, "b", "h", FakeCache())
        self.assertEqual(run["false_acceptances"], [])
        self.assertTrue(run["expectation"]["met"], run["expectation"])

    def test_unsupported_target_cannot_be_verified(self):
        scenario = self.scenario("source-substitution-unsupported-candidate")
        claimed = report([{"id": "step-definition", "decision": "verified", "reason": "x"},
                          {"id": "step-initial", "decision": "unproven", "reason": "unsupported_semantics"}])
        run = evaluate.record(scenario, "deterministic", 1, 1, 1.0, claimed, "", None, None, "b", "h", FakeCache())
        self.assertEqual([item["kind"] for item in run["false_acceptances"]], ["false_verified"])

    def test_baseline_replacement_is_a_false_acceptance(self):
        scenario = self.scenario("persistence-unapproved-activation")
        before, after = {"digest": "a", "revision": 1}, {"digest": "b", "revision": 2}
        run = evaluate.record(scenario, "deterministic", 1, 2, 1.0, {"status": "error", "reason":
                              "active baseline replacement requires an authorized migration"}, "", before, after,
                              "b", "h", FakeCache())
        self.assertEqual([item["kind"] for item in run["false_acceptances"]], ["baseline_replaced"])

    def test_run_timeout_is_counted_without_host_paths(self):
        scenario = self.scenario("timeout-run-budget")
        reason = ("Command '['/usr/bin/python3', '/tmp/timeout-run-budget-x/container.py']' "
                  "timed out after 19.99 seconds")
        run = evaluate.record(scenario, "deterministic", 1, 2, 20.0, {"status": "error", "reason": reason}, "",
                              None, None, "b", "h", FakeCache())
        self.assertEqual(run["run_reason"], "timeout")
        self.assertTrue(run["expectation"]["met"], run["expectation"])
        self.assertEqual(evaluate.normalize_reason("cannot read /var/x/report.json"), "cannot read <path>")

    def test_model_repair_is_classified(self):
        scenario = self.scenario("arithmetic-obsolete-proofs")
        results = [{"id": p["id"], "decision": "verified", "reason": "accepted", "proof_suggestion": "exact foo"}
                   for p in scenario.props]
        run = evaluate.record(scenario, "assisted", 1, 0, 1.0, report(results, status="passed"), "", None, None,
                              "b", "h", FakeCache())
        self.assertEqual({r["repaired_by"] for r in run["results"]}, {"model"})

    def test_usage_separates_unknown_cost(self):
        usage = evaluate.summarize_usage({"usage": {"model_calls": 2, "requests": [
            {"request_id": "a", "state": "reserved", "cost_micros": 50, "input_tokens": 10, "output_tokens": 5},
            {"request_id": "a", "state": "settled", "cost_micros": 7, "input_tokens": 3, "output_tokens": 2},
            {"request_id": "b", "state": "reserved", "cost_micros": 50, "input_tokens": 10, "output_tokens": 5},
            {"request_id": "b", "state": "uncertain", "cost_micros": 50, "input_tokens": 10, "output_tokens": 5}]}})
        self.assertEqual(usage["settled_cost_micros"], 7)
        self.assertEqual(usage["uncertain_requests"], 1)
        self.assertEqual(usage["uncertain_reserved_cost_micros"], 50)


def run_record(scenario="s", category="correct_change", mode="deterministic", repetition=1, wall=10.0,
               results=None, exit=0, false_acceptances=(), usage=None, met=True):
    return {"scenario": scenario, "category": category, "mode": mode, "repetition": repetition,
            "temperature": "cold" if repetition == 1 else "warm", "wall_seconds": wall, "exit": exit,
            "results": results or [], "false_acceptances": list(false_acceptances), "false_rejections": [],
            "usage": usage or {}, "coverage": {}, "run_reason": None,
            "expectation": {"met": met, "failures": [] if met else ["x"]}}


def result(obligation, decision, reason="r", **extra):
    return {"id": obligation, "decision": decision, "reason": reason, "elapsed_seconds": 1.0, **extra}


class AggregateTests(unittest.TestCase):
    def summarize(self, runs, complete=True, modes=("deterministic",)):
        return aggregate.summarize(runs, complete=complete, modes=list(modes),
                                   assisted_status={"status": "not_measured", "reason": "test"},
                                   soundness=corpus.SOUNDNESS, persistence=corpus.PERSISTENCE)

    def test_percentiles(self):
        self.assertEqual(aggregate.percentile([1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 0.95), 10)
        self.assertEqual(aggregate.percentile([3, 1, 2], 0.5), 2)
        self.assertIsNone(aggregate.percentile([], 0.5))

    def test_latency_assessment_uses_warm_deterministic_runs(self):
        runs = [run_record(repetition=1, wall=500.0), run_record(repetition=2, wall=30.0),
                run_record(repetition=2, wall=50.0, scenario="t"),
                run_record(repetition=2, wall=900.0, mode="assisted")]
        latency = aggregate.latency_summary(runs)
        self.assertEqual(latency["deterministic_warm"]["median_seconds"], 40.0)
        self.assertTrue(latency["assessment"]["met"])
        self.assertEqual(latency["deterministic_cold"]["count"], 1)

    def test_false_acceptance_blocks_release_and_is_listed(self):
        bad = run_record(category="forged_evidence", exit=0, met=False,
                         false_acceptances=[{"kind": "false_verified", "obligation": "p", "detail": "d"}])
        summary = self.summarize([run_record(), bad])
        self.assertTrue(summary["release"]["blocked"])
        self.assertEqual(summary["release"]["false_acceptances_in_soundness_scenarios"], 1)
        self.assertEqual(len(summary["false_acceptances"]), 1)
        text = aggregate.markdown(evaluation(summary))
        self.assertIn("BLOCKED", text)
        self.assertIn("false_verified", text)

    def test_paid_assistance_requires_measured_utility(self):
        summary = self.summarize([run_record()])
        self.assertFalse(summary["default_paid_assistance"]["eligible_for_default"])
        self.assertIn("assistance was not measured on this corpus", summary["default_paid_assistance"]["reasons"])

    def test_paid_assistance_eligibility_with_gain_and_known_cost(self):
        runs = [run_record(results=[result("p", "unproven")], exit=1),
                run_record(mode="assisted", results=[result("p", "verified", repaired_by="model")],
                           usage={"settled_cost_micros": 40, "model_calls": 1}),
                run_record(repetition=2, results=[result("p", "unproven")], exit=1),
                run_record(mode="assisted", repetition=2, results=[result("p", "verified", repaired_by="model")],
                           usage={"settled_cost_micros": 40, "model_calls": 1})]
        summary = self.summarize(runs, modes=("deterministic", "assisted"))
        self.assertEqual(summary["assistance_utility"]["additional_verified"], 2)
        self.assertEqual(summary["assistance_utility"]["settled_cost_micros_per_additional_verified"], 40)
        self.assertTrue(summary["default_paid_assistance"]["eligible_for_default"])

    def test_unknown_cost_prevents_paid_default(self):
        runs = [run_record(results=[result("p", "unproven")], exit=1),
                run_record(mode="assisted", results=[result("p", "verified", repaired_by="model")],
                           usage={"settled_cost_micros": 40, "uncertain_requests": 1,
                                  "uncertain_reserved_cost_micros": 99})]
        summary = self.summarize(runs, modes=("deterministic", "assisted"))
        self.assertFalse(summary["modes"]["assisted"]["cost"]["cost_known"])
        self.assertIn("some model cost is unknown", summary["default_paid_assistance"]["reasons"])

    def test_model_nondeterminism_is_separate_from_deterministic_instability(self):
        runs = [run_record(results=[result("p", "verified")]),
                run_record(repetition=2, results=[result("p", "verified")]),
                run_record(mode="assisted", results=[result("p", "verified")]),
                run_record(mode="assisted", repetition=2, results=[result("p", "unproven")], exit=1)]
        stability = aggregate.stability(runs)
        self.assertEqual(stability["deterministic_instability"], [])
        self.assertEqual({item["obligation"] for item in stability["model_nondeterminism"]}, {"p", "<exit>"})


def evaluation(summary):
    return {"summary": summary, "corpus": {"corpus_sha256": "0" * 64, "frozen_at": "2026-11-01", "properties": 30,
                                           "packages": {"a": {}}, "scenarios_run": 1, "scenarios_total": 1},
            "repetitions": 2, "started_at": "now", "runs": [],
            "environment": {"verifier": {}, "cache": {"bundles_reused": 0, "bundles_built": 0, "build_seconds": 0.0,
                                                      "note": ""}, "temperature_definition": ""}}


if __name__ == "__main__":
    unittest.main()
