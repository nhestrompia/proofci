import contextlib
import io
import json
import tempfile
import unittest
from pathlib import Path

from proofci import gaps


def write_log(directory, entries):
    path = Path(directory) / "gaps.jsonl"
    path.write_text("".join(json.dumps(e) + "\n" for e in entries))
    return path


class GapsTest(unittest.TestCase):
    def test_ranks_by_minutes_then_count(self):
        with tempfile.TemporaryDirectory() as tmp:
            Path(tmp + "/a").mkdir()
            Path(tmp + "/b").mkdir()
            a = write_log(tmp + "/a", [
                {"function": "x.ts::f", "construct": "typeof guard", "minutes": 10, "resolved": True},
                {"function": "x.ts::g", "construct": "typeof guard", "minutes": 5, "resolved": False},
                {"function": "y.ts::h", "construct": "Date", "minutes": 30, "resolved": True},
            ])
            b = write_log(tmp + "/b", [
                {"function": "z.ts::i", "construct": "typeof guard", "minutes": 3, "resolved": True},
            ])
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = gaps.run([a, b])
            self.assertEqual(code, 0)
            table = out.getvalue()
            self.assertIn("| Construct | Hits | Unresolved | Minutes |", table)
            rows = table.splitlines()
            self.assertLess(rows.index("| Date | 1 | 0 | 30 | y.ts::h |"),
                            rows.index("| typeof guard | 3 | 1 | 18 | x.ts::f, x.ts::g, z.ts::i |"))

    def test_missing_file_errors(self):
        err = io.StringIO()
        with contextlib.redirect_stderr(err):
            code = gaps.run([Path("/nonexistent/gaps.jsonl")])
        self.assertEqual(code, 2)
        self.assertIn("no gap logs", err.getvalue())

    def test_pipes_and_unicode_separators(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "gaps.jsonl"
            path.write_text(
                json.dumps({"function": "x.ts::f", "construct": "T | null",
                            "refusal": "line one line two", "minutes": 4,
                            "resolved": True}) + "\n")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = gaps.run([path])
            self.assertEqual(code, 0)
            row = next(l for l in out.getvalue().splitlines() if "T \\| null" in l)
            self.assertEqual(row.count("|") - row.count("\\|"), 6)

    def test_bad_line_errors(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "gaps.jsonl"
            path.write_text("{not json}\n")
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                code = gaps.run([path])
            self.assertEqual(code, 2)
            self.assertIn("gaps.jsonl:1", err.getvalue())


if __name__ == "__main__":
    unittest.main()
