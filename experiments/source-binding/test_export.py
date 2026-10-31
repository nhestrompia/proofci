import json
from pathlib import Path
import unittest

import binding


class ExportAdmissionTests(unittest.TestCase):
    def setUp(self):
        self.export = Path(__file__).with_name("evidence").joinpath("base-definition.ndjson").read_bytes()

    def test_pinned_example_is_admitted(self):
        self.assertIn("def target", binding.check_export(self.export, False))

    def test_unknown_mixed_record_fails_closed(self):
        malformed = self.export + b'{"ie":0,"future_declaration":{"name":"Evil"}}\n'
        with self.assertRaises(ValueError):
            binding.check_export(malformed, False)

    def test_unapproved_axiom_fails_closed(self):
        records = self.export.splitlines()
        records.append(json.dumps({"axiom": {"name": 108}}).encode())
        with self.assertRaises(ValueError):
            binding.check_export(b"\n".join(records) + b"\n", False)

    def test_missing_target_fails_closed(self):
        records = [line for line in self.export.splitlines() if "def" not in json.loads(line)]
        with self.assertRaises(ValueError):
            binding.check_export(b"\n".join(records) + b"\n", False)


if __name__ == "__main__":
    unittest.main()
