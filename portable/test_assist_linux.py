"""Exercise assisted verification through the pinned Linux image."""
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import unittest

import assist
import proofci
from broker import Broker, Limits

FIXTURES = Path(__file__).resolve().parent.parent / "experiments/source-binding/fixtures"


def repair_provider(request, maximum):
    return {"body": "exact Nat.rec (motive := fun n => target n = n) rfl (fun n ih => congrArg Nat.succ ih) x",
            "input_tokens": 40, "output_tokens": 8}


def should_not_run(request, maximum):
    raise AssertionError("model must not run")


@unittest.skipUnless(os.environ.get("PROOFCI_TEST_PACKAGED"), "requires the pinned local image and Docker")
class AssistedLinuxTests(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="proofci-assist-test-")
        self.addCleanup(temporary.cleanup)
        self.root = Path(temporary.name)
        self.snapshot = self.root / "snapshot"
        self.baseline = self.root / "protected"
        self.artifacts = self.root / "artifacts"
        self.snapshot.mkdir()
        self.baseline.mkdir()
        self.artifacts.mkdir()
        (self.snapshot / "candidate.lean").write_text("def target (x : Nat) : Nat := 0 + x\n")
        (self.baseline / "contract.json").write_text('{"rhs":"x"}')
        (self.baseline / "reflexive.json").write_text('{"rhs":"0 + x"}')
        shutil.copytree(FIXTURES / "verified", self.snapshot / "evidence")
        def git(*args):
            return subprocess.check_output(["git", "-C", str(self.snapshot), *args], text=True).strip()
        git("init", "-q")
        git("config", "user.name", "ProofCI")
        git("config", "user.email", "proofci@example.invalid")
        git("remote", "add", "origin", "https://example.invalid/fixture.git")
        git("add", ".")
        git("commit", "-qm", "obsolete proof")
        head = git("rev-parse", "HEAD")
        sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
        baseline = {"version": 1, "candidate": "candidate.lean", "obligations": [
            {"id": "zero_add", "policy": "required", "contract": "contract.json",
             "contract_sha256": sha(self.baseline / "contract.json"), "evidence": "evidence"},
            {"id": "reflexive", "policy": "advisory", "contract": "reflexive.json",
             "contract_sha256": sha(self.baseline / "reflexive.json"), "evidence": "missing"}]}
        (self.baseline / "baseline.json").write_text(json.dumps(baseline))
        envelope = {"version": 1, "repository": "https://example.invalid/fixture.git", "head": head, "base": head,
            "candidate_sha256": sha(self.snapshot / "candidate.lean"), "baseline_sha256": sha(self.baseline / "baseline.json"),
            "dependency": sha(proofci.VALIDATOR / "core-dependencies.json"), "toolchain": proofci.TOOLCHAIN_SHA256,
            "trust_policy": proofci.policy_digest(), "resource_policy": {"timeout_seconds": 180, "cpu_seconds": 180,
            "memory_bytes": 2147483648, "file_bytes": 2147483648, "processes": 256}}
        (self.root / "envelope.json").write_text(json.dumps(envelope))

    def test_repair_requires_independent_acceptance(self):
        kwargs = dict(envelope_path=self.root / "envelope.json", baseline_path=self.baseline / "baseline.json",
                      snapshot=self.snapshot, report_path=self.root / "report.json", artifacts=self.artifacts)
        self.assertEqual(assist.run(**kwargs), 1)
        before = json.loads((self.root / "report.json").read_text())
        self.assertEqual(before["results"][0]["decision"], "unproven")
        self.assertEqual(before["results"][1]["decision"], "verified")
        self.assertEqual(before["usage"]["model_calls"], 0)
        broker = Broker(run_id="fixture-run", repository="https://example.invalid/fixture.git", private=True,
                        consent=lambda repository: True, authorize=lambda repository, run, obligation, candidate, contract, deadline: True,
                        limits=Limits(32768, 100000, 1000, 100000, 1000000, 1000000, 100),
                        provider=repair_provider, run_deadline=time.monotonic() + 180)
        self.assertEqual(assist.run(**kwargs, broker=broker), 0)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(report["results"][0]["decision"], "verified")
        self.assertEqual(report["results"][1]["decision"], "verified")
        self.assertEqual(report["usage"]["model_calls"], 1)
        self.assertTrue((self.artifacts / report["results"][0]["generated_artifact"] / "manifest.json").is_file())
        self.assertTrue((self.artifacts / report["usage"]["requests"][-1]["artifact"]).is_file())
        journal = (self.artifacts / report["usage"]["journal"]).read_text().splitlines()
        self.assertEqual([json.loads(line)["state"] for line in journal], ["reserved", "settled"])
        archive = self.root / "repair.tar"
        exported = subprocess.run([sys.executable, str(Path(assist.__file__).with_name("replay.py")), "export",
            "--envelope", str(self.root / "envelope.json"), "--baseline", str(self.baseline / "baseline.json"),
            "--snapshot", str(self.snapshot), "--report", str(self.root / "report.json"), "--output", str(archive)],
            capture_output=True, text=True)
        self.assertEqual(exported.returncode, 0, exported.stderr)
        replay_path = self.root / "replayed.json"
        replayed = subprocess.run([sys.executable, str(Path(assist.__file__).with_name("replay.py")), "replay",
            "--bundle", str(archive), "--sha256", exported.stdout.strip().removeprefix("sha256:"),
            "--output", str(replay_path)], capture_output=True, text=True)
        self.assertEqual(replayed.returncode, 0, replayed.stderr + replay_path.read_text())
        self.assertEqual(json.loads(replay_path.read_text())["status"], "reproduced")

    def test_deterministic_proof_avoids_model_request(self):
        shutil.rmtree(self.snapshot / "evidence")
        (self.snapshot / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 1\n")
        shutil.copy(FIXTURES / "conditional-verified-contract.json", self.baseline / "contract.json")
        def git(*args):
            return subprocess.check_output(["git", "-C", str(self.snapshot), *args], text=True).strip()
        git("add", "-A")
        git("commit", "-qm", "missing proof")
        sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
        baseline_path = self.baseline / "baseline.json"
        baseline = json.loads(baseline_path.read_text())
        baseline["obligations"] = baseline["obligations"][:1]
        baseline["obligations"][0]["contract_sha256"] = sha(self.baseline / "contract.json")
        baseline_path.write_text(json.dumps(baseline))
        envelope_path = self.root / "envelope.json"
        envelope = json.loads(envelope_path.read_text())
        envelope["head"] = git("rev-parse", "HEAD")
        envelope["candidate_sha256"] = sha(self.snapshot / "candidate.lean")
        envelope["baseline_sha256"] = sha(baseline_path)
        envelope_path.write_text(json.dumps(envelope))
        broker = Broker(run_id="deterministic", repository=envelope["repository"], private=True,
                        consent=lambda repository: True,
                        authorize=lambda repository, run, obligation, candidate, contract, deadline: True,
                        limits=Limits(32768, 100000, 1000, 100000, 1000000, 1000000, 100),
                        provider=should_not_run, run_deadline=time.monotonic() + 180)
        status = assist.run(envelope_path=envelope_path, baseline_path=baseline_path, snapshot=self.snapshot,
                            report_path=self.root / "report.json", artifacts=self.artifacts, broker=broker)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(status, 0, report)
        self.assertEqual(report["usage"]["model_calls"], 0)
        self.assertEqual(report["results"][0]["decision"], "verified")
        config = {"repository": envelope["repository"], "run_id": "denied-deterministic", "head": envelope["head"],
                  "baseline_sha256": envelope["baseline_sha256"], "authorized": False, "model": "gpt-4o-mini",
                  "limits": {"context_bytes": 32768, "input_tokens": 100000, "output_tokens": 1000,
                             "cost_micros": 100000, "input_micros_per_million": 1000000,
                             "output_micros_per_million": 1000000, "max_output_per_call": 100}}
        config_path = self.root / "denied.json"
        config_path.write_text(json.dumps(config))
        environment = dict(os.environ)
        environment.pop("PROOFCI_OPENAI_API_KEY", None)
        status = subprocess.run([sys.executable, str(Path(assist.__file__)), "--envelope", str(envelope_path),
            "--baseline", str(baseline_path), "--snapshot", str(self.snapshot),
            "--report", str(self.root / "denied-report.json"), "--artifacts", str(self.artifacts),
            "--model-config", str(config_path)], env=environment, check=False).returncode
        denied_report = json.loads((self.root / "denied-report.json").read_text())
        self.assertEqual(status, 0, denied_report)
        self.assertEqual(denied_report["usage"]["model_calls"], 0)

    def test_cli_private_source_is_denied_by_default(self):
        envelope = json.loads((self.root / "envelope.json").read_text())
        config = {"repository": envelope["repository"], "run_id": "private-test", "head": envelope["head"],
                  "baseline_sha256": envelope["baseline_sha256"], "authorized": True, "model": "gpt-4o-mini",
                  "limits": {"context_bytes": 32768, "input_tokens": 100000, "output_tokens": 1000,
                             "cost_micros": 100000, "input_micros_per_million": 1000000,
                             "output_micros_per_million": 1000000, "max_output_per_call": 100}}
        config_path = self.root / "model.json"
        config_path.write_text(json.dumps(config))
        env = dict(os.environ)
        env.pop("PROOFCI_OPENAI_API_KEY", None)
        status = subprocess.run([sys.executable, str(Path(assist.__file__)), "--envelope", str(self.root / "envelope.json"),
            "--baseline", str(self.baseline / "baseline.json"), "--snapshot", str(self.snapshot),
            "--report", str(self.root / "report.json"), "--artifacts", str(self.artifacts),
            "--model-config", str(config_path)], env=env, check=False).returncode
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(status, 1, report)
        self.assertEqual(report["usage"]["model_calls"], 0)
        self.assertEqual(report["results"][0]["repair_reason"], "not_authorized")

    def test_checked_violation_is_not_replaced_by_repair(self):
        shutil.rmtree(self.snapshot / "evidence")
        shutil.copy(FIXTURES / "candidate.lean", self.snapshot / "candidate.lean")
        shutil.copy(FIXTURES / "conditional-contract.json", self.baseline / "contract.json")
        shutil.copytree(FIXTURES / "conditional", self.snapshot / "refutation")
        def git(*args):
            return subprocess.check_output(["git", "-C", str(self.snapshot), *args], text=True).strip()
        git("add", "-A")
        git("commit", "-qm", "checked violation")
        sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
        baseline_path = self.baseline / "baseline.json"
        baseline = json.loads(baseline_path.read_text())
        baseline["obligations"] = baseline["obligations"][:1]
        baseline["obligations"][0]["contract_sha256"] = sha(self.baseline / "contract.json")
        baseline["obligations"][0]["refutation"] = "refutation"
        baseline_path.write_text(json.dumps(baseline))
        envelope_path = self.root / "envelope.json"
        envelope = json.loads(envelope_path.read_text())
        envelope["head"] = git("rev-parse", "HEAD")
        envelope["candidate_sha256"] = sha(self.snapshot / "candidate.lean")
        envelope["baseline_sha256"] = sha(baseline_path)
        envelope_path.write_text(json.dumps(envelope))
        broker = Broker(run_id="violation", repository=envelope["repository"], private=True,
                        consent=lambda repository: True,
                        authorize=lambda repository, run, obligation, candidate, contract, deadline: True,
                        limits=Limits(32768, 100000, 1000, 100000, 1000000, 1000000, 100),
                        provider=should_not_run, run_deadline=time.monotonic() + 180)
        status = assist.run(envelope_path=envelope_path, baseline_path=baseline_path, snapshot=self.snapshot,
                            report_path=self.root / "report.json", artifacts=self.artifacts, broker=broker)
        report = json.loads((self.root / "report.json").read_text())
        self.assertEqual(status, 1, report)
        self.assertEqual(report["results"][0]["decision"], "violated")
        self.assertEqual(report["property_counts"]["violated"], 1)
        self.assertEqual(report["usage"]["model_calls"], 0)


if __name__ == "__main__":
    unittest.main()
