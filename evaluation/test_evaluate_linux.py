"""End-to-end evaluation checks with the pinned verifier image and Docker.

Run with PROOFCI_TEST_PACKAGED=1. The assisted check uses a scripted provider
inside the real broker and verifier path; it makes no paid model request.
"""
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent / "portable"))

import assist  # noqa: E402
from broker import Broker, Limits  # noqa: E402
import evaluation_corpus as corpus  # noqa: E402
import evaluate  # noqa: E402

CACHE = Path(os.environ.get("PROOFCI_EVALUATION_CACHE", Path.home() / ".cache" / "proofci-evaluation"))


class ScriptedProvider:
    available = True

    def __init__(self, bodies):
        self.bodies = bodies

    def __call__(self, request, max_output_tokens):
        return {"body": self.bodies.get(request["contract"], "rfl"), "input_tokens": 200, "output_tokens": 40}


@unittest.skipUnless(os.environ.get("PROOFCI_TEST_PACKAGED"), "requires the pinned local image and Docker")
class EvaluationLinuxTests(unittest.TestCase):
    def test_cli_subset_reports_rejections_without_false_acceptance(self):
        with tempfile.TemporaryDirectory(prefix="proofci-evaluation-test-") as temp:
            output = Path(temp) / "out"
            command = [sys.executable, str(HERE / "evaluate.py"), "run", "--mode", "deterministic",
                       "--repetitions", "1", "--output", str(output), "--cache", str(CACHE),
                       "--scenario", "forged-candidate-digest", "--scenario", "source-substitution-unsupported-candidate",
                       "--scenario", "invalid-submission-uncommitted"]
            completed = subprocess.run(command, capture_output=True, text=True, timeout=1800)
            self.assertEqual(completed.returncode, 0, completed.stderr)
            evaluation = json.loads((output / "evaluation.json").read_text())
            self.assertEqual(evaluation["summary"]["release"]["false_acceptances"], 0)
            self.assertFalse(evaluation["summary"]["release"]["complete_corpus"])
            self.assertEqual({run["exit"] for run in evaluation["runs"]}, {1, 2})
            self.assertTrue((output / "evaluation.md").read_text().startswith("# ProofCI evaluation"))

    def test_assisted_repair_is_measured_and_cannot_accept_false_properties(self):
        packages, scenarios = corpus.load()
        specs = {s["id"]: s for s in scenarios}
        obsolete = copy.deepcopy(specs["arithmetic-obsolete-proofs"])
        obsolete["properties"] = ["fee-definition", "fee-four-items"]
        forged = specs["forged-candidate-digest"]
        point = next(p for p in packages["arithmetic"]["properties"] if p["id"] == "fee-four-items")
        bodies = {corpus.contract_bytes(point["contract"]).decode(): evaluate.positive_bodies(point["contract"])[1]}
        state_contract = next(p for p in packages["state"]["properties"] if p["id"] == "step-from-five")["contract"]
        bodies[corpus.contract_bytes(state_contract).decode()] = "exact Eq.ndrec (motive := fun y => target y = 15) rfl (Eq.symm h)"
        cache = evaluate.EvidenceCache(CACHE, evaluate.IMAGE_ID)
        scenarios = [evaluate.Scenario(obsolete, packages), evaluate.Scenario(forged, packages)]
        cache.ensure([job for s in scenarios for job in s.jobs()])

        def runner(*, envelope_path, baseline_path, snapshot, report_path, artifacts, config):
            limits = Limits(context_bytes=32768, input_tokens=100000, output_tokens=5000, cost_micros=1000000,
                            input_micros_per_million=150000, output_micros_per_million=600000,
                            max_output_per_call=1000)
            broker = Broker(run_id=config["run_id"], repository=config["repository"], private=False,
                            consent=lambda repository: True, authorize=lambda *args: True, limits=limits,
                            provider=ScriptedProvider(bodies), run_deadline=time.monotonic() + 900)
            return assist.run(envelope_path=envelope_path, baseline_path=baseline_path, snapshot=snapshot,
                              report_path=report_path, artifacts=artifacts, broker=broker)

        with tempfile.TemporaryDirectory(prefix="proofci-evaluation-assisted-") as temp:
            stores = evaluate.PersistenceStore(Path(temp))
            profile = {"model": "scripted", "limits": {}, "authorized": True}
            deterministic = evaluate.run_scenario(scenarios[0], "deterministic", 1, cache, Path(temp), stores, None, False)
            assisted = evaluate.run_scenario(scenarios[0], "assisted", 1, cache, Path(temp), stores, profile, False,
                                             assisted_runner=runner)
            decisions = {r["id"]: (r["decision"], r["repaired_by"]) for r in deterministic["results"]}
            self.assertEqual(decisions["fee-definition"], ("verified", "fixed_tactic"))
            self.assertEqual(decisions["fee-four-items"][0], "unproven")
            repaired = {r["id"]: (r["decision"], r["repaired_by"]) for r in assisted["results"]}
            self.assertEqual(repaired["fee-four-items"], ("verified", "model"))
            self.assertEqual(assisted["exit"], 0)
            self.assertGreater(assisted["usage"]["settled_cost_micros"], 0)
            self.assertEqual(assisted["false_acceptances"], [])
            # A model proof for the old target cannot verify the defective one.
            hostile = evaluate.run_scenario(scenarios[1], "assisted", 1, cache, Path(temp), stores, profile, False,
                                            assisted_runner=runner)
            self.assertEqual(hostile["false_acceptances"], [])
            self.assertEqual(hostile["results"][0]["decision"], "unproven")
            self.assertEqual(hostile["results"][0]["repair_reason"], "attempts_exhausted")
            self.assertEqual(hostile["usage"]["model_calls"], 5)


if __name__ == "__main__":
    unittest.main()
