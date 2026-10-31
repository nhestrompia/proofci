from contextlib import closing
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).parent))
import baselines


def manifest():
    return {"version": 1, "candidate": "candidate.lean", "contracts": [{
        "id": "increment", "explanation": "Adds one", "owner": "maintainer",
        "formal_statement": "x + 1", "assumptions": [], "specification_closure": [],
        "implementation_bindings": ["target"], "policy": "required", "evidence": "evidence"}]}


class BaselineTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.snapshot = self.root / "repo"
        self.snapshot.mkdir()
        self.git("init", "-q")
        self.git("config", "user.email", "a@example.invalid")
        self.git("config", "user.name", "A")
        self.git("remote", "add", "origin", "repo")
        (self.snapshot / "candidate.lean").write_text("def target (x : Nat) : Nat := x + 1\n")
        self.data = baselines.encoded(manifest())
        (self.snapshot / "contracts.json").write_bytes(self.data)
        self.git("add", ".")
        self.git("commit", "-qm", "initial")
        self.head = self.git("rev-parse", "HEAD")
        (self.root / "envelope.json").write_text(json.dumps({"repository": "repo", "head": self.head}))
        self.store = self.root / "store.db"
        self.report = self.root / "report.json"

    def git(self, *args):
        return subprocess.check_output(["git", "-C", str(self.snapshot), *args], text=True).strip()

    def args(self, command):
        return ["baselines", command, "--store", str(self.store), "--snapshot", str(self.snapshot),
                "--envelope", str(self.root / "envelope.json"), "--report", str(self.report)]

    def activate(self, approver="alice"):
        args = self.args("activate") + ["--manifest-path", "contracts.json", "--reviewed-sha256", baselines.sha(self.data), "--approver", approver]
        with patch.object(sys, "argv", args):
            return baselines.main()

    def success(self, snapshot, envelope, contract, report):
        with tempfile.TemporaryDirectory() as temp:
            digest = baselines.materialize(contract, Path(temp))
        result = {"version": 1, "status": "passed", "results": [{"id": "increment", "decision": "verified"}]}
        report.write_bytes(baselines.encoded(result))
        return 0, result, digest, {"repository": "repo", "head": self.head}

    def test_activation_failure_keeps_previous_baseline(self):
        with patch.object(baselines, "invoke", side_effect=self.success):
            self.assertEqual(self.activate(), 0)
        with closing(baselines.open_store(self.store)) as db:
            before = baselines.lookup(db)["digest"]
        with patch.object(baselines, "invoke", return_value=(1, {}, "", {})):
            self.assertEqual(self.activate(), 1)
        with closing(baselines.open_store(self.store)) as db:
            self.assertEqual(baselines.lookup(db)["digest"], before)

    def test_changed_or_removed_guarantee_blocks_and_keeps_old_obligation(self):
        with patch.object(baselines, "invoke", side_effect=self.success):
            self.assertEqual(self.activate(), 0)
            changed = manifest()
            changed["contracts"][0]["policy"] = "advisory"
            (self.snapshot / "contracts.json").write_bytes(baselines.encoded(changed))
            self.git("add", ".")
            self.git("commit", "-qm", "weaken")
            with patch.object(sys, "argv", self.args("run")):
                self.assertEqual(baselines.main(), 1)
            report = json.loads(self.report.read_bytes())
            self.assertEqual(report["status"], "blocked")
            self.assertEqual(report["proposed_guarantee_changes"][0]["fields"], ["policy"])
            self.assertEqual(report["results"][0]["id"], "increment")

    def test_replacement_requires_migration_and_lookup_is_immutable(self):
        with patch.object(baselines, "invoke", side_effect=self.success):
            self.assertEqual(self.activate(), 0)
            old = baselines.sha(self.data)
            changed = manifest()
            changed["contracts"][0]["formal_statement"] = "x + 2"
            self.data = baselines.encoded(changed)
            (self.snapshot / "contracts.json").write_bytes(self.data)
            self.git("add", ".")
            self.git("commit", "-qm", "proposal")
            self.assertEqual(self.activate(), 2)
            with closing(baselines.open_store(self.store)) as db:
                self.assertEqual(baselines.lookup(db)["digest"], old)
                self.assertEqual(baselines.lookup(db, old)["manifest"], baselines.encoded(manifest()))

    def test_proposals_record_deletion_rename_and_specification_changes(self):
        original = manifest()
        for field, value in (("id", "renamed"), ("formal_statement", "x + 2"),
                             ("assumptions", ["x > 0"]), ("specification_closure", ["helper changed"]),
                             ("implementation_bindings", ["other"])):
            candidate = manifest()
            candidate["contracts"][0][field] = value
            parsed = baselines.parse_manifest(baselines.encoded(candidate), supported=False)
            self.assertTrue(baselines.changes(original, parsed), field)
        removed = {"version": 1, "candidate": "candidate.lean", "contracts": []}
        self.assertEqual(baselines.changes(original, removed), [{"id": "increment", "kind": "removed"}])

    def test_unsupported_semantics_cannot_activate(self):
        item = manifest()
        item["contracts"][0]["assumptions"] = ["x > 0"]
        with self.assertRaisesRegex(ValueError, "unsupported"):
            baselines.parse_manifest(baselines.encoded(item))

    def test_real_cli_failure_cannot_activate(self):
        self.assertEqual(self.activate(), 2)
        with closing(baselines.open_store(self.store)) as db:
            with self.assertRaisesRegex(ValueError, "not found"):
                baselines.lookup(db)


if __name__ == "__main__":
    unittest.main()
