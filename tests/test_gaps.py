import contextlib
import io
import json
import re
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
            self.assertIn("| Construct | Repos | Hits | Unresolved | Minutes |", table)
            rows = table.splitlines()
            self.assertLess(rows.index("| Date | 1 | 1 | 0 | 30 | y.ts::h |"),
                            rows.index("| typeof guard | 2 | 3 | 1 | 18 | x.ts::f, x.ts::g, z.ts::i |"))

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
                            "refusal": "line one line two", "minutes": 4,
                            "resolved": True}) + "\n")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = gaps.run([path])
            self.assertEqual(code, 0)
            row = next(l for l in out.getvalue().splitlines() if "T \\| null" in l)
            self.assertEqual(row.count("|") - row.count("\\|"), 7)

    def test_groups_normalized_and_by_code(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = write_log(tmp, [
                {"function": "a.ts::f", "construct": "Typeof  Guard", "minutes": 2, "resolved": True},
                {"function": "a.ts::g", "construct": "typeof guard", "minutes": 3, "resolved": True},
                {"function": "b.ts::h", "construct": "Date type", "code": "type-any", "minutes": 5, "resolved": True},
                {"function": "b.ts::i", "construct": "Date", "code": "type-any", "minutes": 1, "resolved": True},
            ])
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                code = gaps.run([path], as_json=True)
            self.assertEqual(code, 0)
            rows = json.loads(out.getvalue())["rows"]
            self.assertEqual(len(rows), 2)
            coded = next(r for r in rows if r["key"] == "code:type-any")
            self.assertEqual(coded["count"], 2)
            self.assertEqual(coded["construct"], "type-any")
            normalized = next(r for r in rows if r["key"] == "construct:typeof guard")
            self.assertEqual(normalized["count"], 2)
            self.assertEqual(normalized["minutes"], 5)

    def test_other_empty_and_invented_codes_group_by_construct(self):
        """`other`, empty and agent-invented codes must not merge into one row
        named after the first entry's construct."""
        with tempfile.TemporaryDirectory() as tmp:
            path = write_log(tmp, [
                {"function": "a::f", "construct": "indexed read operand", "code": "other", "minutes": 10},
                {"function": "a::g", "construct": "whitespace split", "code": "", "minutes": 5},
                {"function": "a::h", "construct": "out of memory", "code": "node-oom", "minutes": 8},
                {"function": "a::i", "construct": "out of memory", "code": "env-dropped", "minutes": 7},
                {"function": "a::j", "construct": "typed hole", "code": "proof_step", "minutes": 4},
            ])
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(gaps.run([path], as_json=True), 0)
            rows = json.loads(out.getvalue())["rows"]
            keys = {r["key"] for r in rows}
            self.assertEqual(keys, {"construct:indexed read operand", "construct:whitespace split",
                                    "construct:out of memory", "construct:typed hole"})
            oom = next(r for r in rows if r["key"] == "construct:out of memory")
            self.assertEqual((oom["count"], oom["minutes"]), (2, 15))

    def test_gap_codes_group_by_code(self):
        with tempfile.TemporaryDirectory() as tmp:
            Path(tmp + "/repo-a").mkdir()
            a = write_log(tmp + "/repo-a", [
                {"function": "*", "construct": "docker volume root-owned",
                 "code": "setup-env", "minutes": 10},
            ])
            Path(tmp + "/repo-b/proofci").mkdir(parents=True)
            b = write_log(tmp + "/repo-b/proofci", [
                {"function": "*", "construct": "volume permissions",
                 "code": "setup-env", "minutes": 4},
            ])
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(gaps.run([a, b], as_json=True), 0)
            rows = json.loads(out.getvalue())["rows"]
            self.assertEqual(len(rows), 1)
            self.assertEqual(rows[0]["key"], "code:setup-env")
            self.assertEqual(rows[0]["minutes"], 14)
            self.assertEqual(rows[0]["repos"], ["repo-a", "repo-b"])

    def test_named_log_files_name_their_own_repo(self):
        with tempfile.TemporaryDirectory() as tmp:
            a = Path(tmp) / "t3code.jsonl"
            b = Path(tmp) / "calcom.jsonl"
            for path in (a, b):
                path.write_text(json.dumps({"function": "*", "construct": "x",
                                            "code": "setup-env", "minutes": 1}) + "\n")
            out = io.StringIO()
            with contextlib.redirect_stdout(out):
                self.assertEqual(gaps.run([a, b], as_json=True), 0)
            rows = json.loads(out.getvalue())["rows"]
            self.assertEqual(rows[0]["repos"], ["calcom", "t3code"])

    def test_bad_line_errors(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "gaps.jsonl"
            path.write_text("{not json}\n")
            err = io.StringIO()
            with contextlib.redirect_stderr(err):
                code = gaps.run([path])
            self.assertEqual(code, 2)
            self.assertIn("gaps.jsonl:1", err.getvalue())

    def test_hints_mjs_codes_are_known(self):
        """Every code `typescript/hints.mjs` can emit is a known refusal code
        (or matches a refusal prefix), so REFUSAL_CODES can't silently drift."""
        hints = (Path(__file__).resolve().parents[1] / "typescript" / "hints.mjs").read_text()
        body = hints.split("export function refusalCode", 1)[1].split("\nfunction ", 1)[0]
        codes = set(re.findall(r'"([a-z][a-z0-9-]+)"', body))
        table = hints.split("FIXED_STRING_CODES = [", 1)[1].split("\n];", 1)[0]
        codes |= set(re.findall(r',\s*"([a-z0-9-]+)"', table))
        named = re.search(r"NAMED_TYPES = new Set\(\[([^\]]+)\]", hints).group(1)
        codes |= {"type-" + s.strip().strip('"') for s in named.split(",") if s.strip()}

        def known(code):
            return (code in gaps.REFUSAL_CODES or code == "other"
                    or code.rstrip("-") in gaps.REFUSAL_PREFIXES
                    or any(code.startswith(p) for p in gaps.REFUSAL_PREFIXES))

        self.assertEqual([c for c in sorted(codes) if not known(c)], [])

    def test_every_gap_code_is_documented_in_the_skill(self):
        skill = (Path(__file__).resolve().parents[1] / "docs/skills/proofci/SKILL.md").read_text()
        for code in gaps.GAP_CODES:
            self.assertIn(f"`{code}`", skill)


if __name__ == "__main__":
    unittest.main()
