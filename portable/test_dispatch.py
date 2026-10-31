import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import dispatch
from test_proofci import CLITest


class DispatchTests(CLITest):
    def _blocked_report(self, envelope):
        results = [{"id": "one", "policy": "required", "evidence": "missing",
                    "decision": "unproven", "reason": "missing_evidence"},
                   {"id": "two", "policy": "advisory", "evidence": "missing2",
                    "decision": "unproven", "reason": "missing_evidence"}]
        return {"version": 1, "status": "blocked", "envelope": envelope,
                "results": results, "property_counts": {"verified": 0, "violated": 0, "unproven": 2}}

    def _forged_report(self, envelope):
        results = []
        contract_sha256 = hashlib.sha256((self.root / "contract.json").read_bytes()).hexdigest()
        for item in (("one", "required", "missing"), ("two", "advisory", "missing2")):
            results.append({"id": item[0], "policy": item[1], "evidence": item[2],
                            "decision": "verified", "reason": "worker says so",
                            "validation": {"decision": "verified",
                                "candidate_sha256": envelope["candidate_sha256"],
                                "contract_sha256": contract_sha256}})
        return {"version": 1, "status": "passed", "envelope": envelope,
                "results": results, "property_counts": {"verified": 2, "violated": 0, "unproven": 0}}

    def test_final_validation_rejects_a_forged_worker_pass(self):
        envelope = json.loads((self.root / "envelope.json").read_text())
        phases = []

        def launcher(command, _deadline):
            phase = command[command.index("--phase") + 1]
            phases.append(phase)
            if phase == "final-validation":
                self.assertIn("--validator-only", command)
            report_path = Path(command[command.index("--report") + 1])
            value = self._forged_report(envelope) if phase == "worker" else self._blocked_report(envelope)
            report_path.write_text(json.dumps(value))
            return 0 if phase == "worker" else 1

        status = dispatch.run(envelope_path=self.root / "envelope.json",
                              baseline_path=self.root / "baseline.json", snapshot=self.snapshot,
                              report_path=self.root / "dispatch-report.json", launcher=launcher)
        self.assertEqual(status, 1)
        self.assertEqual(phases, ["worker", "final-validation"])
        result = json.loads((self.root / "dispatch-report.json").read_text())
        self.assertEqual(result["status"], "blocked")
        self.assertEqual(result["results"][0]["decision"], "unproven")
        self.assertEqual(result["dispatch"]["worker_status"], 0)
        self.assertEqual(result["dispatch"]["final_status"], 1)

    def test_dependency_and_raw_artifact_handoff_are_allowlisted(self):
        envelope = json.loads((self.root / "envelope.json").read_text())
        dependency_temporary = tempfile.TemporaryDirectory(prefix="proofci-dependency-metadata-")
        self.addCleanup(dependency_temporary.cleanup)
        metadata_root = Path(dependency_temporary.name)
        cache = metadata_root / "cache"
        cache.mkdir()
        data = b"approved dependency"
        checksum = hashlib.sha256(data).hexdigest()
        (cache / checksum).write_bytes(data)
        manifest = metadata_root / "dependencies.json"
        manifest.write_text(json.dumps({"version": 1, "dependencies": [{"name": "core.bin",
            "sha256": checksum, "size_bytes": len(data)}]}))
        artifact_temporary = tempfile.TemporaryDirectory(prefix="proofci-worker-artifacts-")
        self.addCleanup(artifact_temporary.cleanup)
        artifacts = Path(artifact_temporary.name)
        artifact = b"raw worker output"
        (artifacts / "solution.lean").write_bytes(artifact)
        manifest_temporary = tempfile.TemporaryDirectory(prefix="proofci-artifact-manifest-")
        self.addCleanup(manifest_temporary.cleanup)
        artifact_manifest = Path(manifest_temporary.name) / "artifact-manifest.json"
        artifact_manifest.write_text(json.dumps({"version": 1, "files": {
            "solution.lean": hashlib.sha256(artifact).hexdigest()}}))

        def launcher(command, _deadline):
            report_path = Path(command[command.index("--report") + 1])
            report_path.write_text(json.dumps(self._blocked_report(envelope)))
            return 1

        status = dispatch.run(envelope_path=self.root / "envelope.json",
                              baseline_path=self.root / "baseline.json", snapshot=self.snapshot,
                              report_path=self.root / "dispatch-report.json",
                              dependency_manifest=manifest, dependency_cache=cache,
                              artifacts=artifacts, artifact_manifest=artifact_manifest,
                              launcher=launcher)
        self.assertEqual(status, 1)
        result = json.loads((self.root / "dispatch-report.json").read_text())
        self.assertEqual(result["worker_artifacts"]["files"], {
            "solution.lean": hashlib.sha256(artifact).hexdigest()})
        self.assertEqual(result["dispatch"]["dependencies"]["dependencies"][0]["sha256"], checksum)


if __name__ == "__main__":
    unittest.main()
