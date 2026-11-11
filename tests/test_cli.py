"""`proofci check` keeps its verdict even when the report can't be written."""

import io
import sys
import tempfile
import unittest
from contextlib import redirect_stderr, redirect_stdout
from pathlib import Path
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import cli  # noqa: E402


class FakeReport:
    passed = True
    outcomes = []

    def to_json(self):
        return {"passed": True}


class ReportWriteTests(unittest.TestCase):
    def run_check(self, *extra):
        out, err = io.StringIO(), io.StringIO()
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(cli.check_mod, "check", return_value=FakeReport()), \
                mock.patch.object(cli, "markdown", return_value="## ProofCI\n"), \
                redirect_stdout(out), redirect_stderr(err):
            status = cli.main(["check", "--base", tmp, "--head", tmp, *extra])
        return status, out.getvalue(), err.getvalue()

    def test_a_report_that_cannot_be_written_is_explained(self):
        status, out, err = self.run_check("--report", "/nonexistent-host-path/report.json")
        self.assertEqual(status, 2)
        self.assertIn("## ProofCI", out)  # the verdict is still printed
        self.assertIn("could not write /nonexistent-host-path/report.json", err)
        self.assertIn("mounted directory", err)

    def test_a_writable_report_is_written(self):
        with tempfile.TemporaryDirectory() as tmp:
            status, _, _ = self.run_check("--report", str(Path(tmp) / "r.json"))
            self.assertEqual(status, 0)
            self.assertTrue((Path(tmp) / "r.json").is_file())


if __name__ == "__main__":
    unittest.main()
