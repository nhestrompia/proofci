import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from proofci import check, summary, typescript  # noqa: E402

REASON = "a.ts:3: the type `any` is not supported yet"
HINT = "write the type the value really has"


def unsupported(function, guarantee, failure):
    o = check.Outcome("t", guarantee, function, guarantee, True, check.UNSUPPORTED)
    o.reason, o.hint = typescript.split_hint(failure)
    return o


class HintTests(unittest.TestCase):
    def test_split_hint(self):
        self.assertEqual(typescript.split_hint(f"{REASON}\nHow to fix: {HINT}"), (REASON, HINT))
        self.assertEqual(typescript.split_hint(REASON), (REASON, None))

    def test_a_note_goes_before_the_hint(self):
        reason = typescript.with_note(f"{REASON}\nHow to fix: {HINT}", "add the package to the lockfile")
        self.assertEqual(typescript.split_hint(reason), (REASON + "\nadd the package to the lockfile", HINT))
        self.assertEqual(typescript.with_note(REASON, "note"), REASON + "\nnote")

    def test_report_json_has_the_hint(self):
        report = check.Report(outcomes=[unsupported("a.ts::f", "g", f"{REASON}\nHow to fix: {HINT}")], language="typescript")
        g = report.to_json()["guarantees"][0]
        self.assertEqual((g["status"], g["reason"], g["hint"]), ("unsupported", REASON, HINT))

    def test_summary_shows_the_hint_under_the_reason(self):
        report = check.Report(outcomes=[unsupported("a.ts::f", "g", f"{REASON}\nHow to fix: {HINT}")], language="typescript")
        text = summary.markdown(report.to_json())
        self.assertIn(f"```\n{REASON}\n```\n\n**How to fix:** {HINT}", text)

    def test_summary_shows_each_guarantee_its_hint(self):
        other = "a.ts:9: `Math.sign` is not supported"
        report = check.Report(outcomes=[
            unsupported("a.ts::f", "g", f"{REASON}\nHow to fix: {HINT}"),
            unsupported("a.ts::h", "k", f"{other}\nHow to fix: compare with 0"),
            check.Outcome("t", "v", "a.ts::v", "v", True, check.VERIFIED)], language="typescript")
        text = summary.markdown(report.to_json())
        self.assertIn(f"<code>t/g</code>: unsupported</summary>\n\n```\n{REASON}\n```\n\n**How to fix:** {HINT}\n\n</details>", text)
        self.assertIn(f"```\n{other}\n```\n\n**How to fix:** compare with 0", text)

    def test_reasons_without_a_hint_render_as_before(self):
        o = check.Outcome("t", "g", "m::f", "g", True, check.UNPROVEN, reason="the proof does not check")
        text = summary.markdown(check.Report(outcomes=[o]).to_json())
        self.assertIn("```\nthe proof does not check\n```", text)
        self.assertNotIn("How to fix", text)


if __name__ == "__main__":
    unittest.main()
