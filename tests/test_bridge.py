"""Status of a TypeScript function's bridge: classification of Lean's verdict, the
`require_bridge` policy, and how the report words each status. No toolchain needed:
Lean and the sandbox are replaced with canned output."""

import sys
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import bridge, check, manifest, summary  # noqa: E402

OK = "'src_ledger_transfer_bridge' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
NO_AXIOMS = "'src_ledger_transfer_bridge' does not depend on any axioms\n"
STUCK = "/work/B0.lean:97:2: error: STUCK\ncase hf.refine_2.he\nh : Heap\n"
TWO = ["src_a_f_bridge", "src_a_g_bridge"]


class ClassifyTests(unittest.TestCase):
    def classify(self, status, output, timed_out=False, theorems=("src_ledger_transfer_bridge",)):
        return bridge.classify(status, output, timed_out, list(theorems), 120)

    def test_proved_needs_a_clean_exit_and_standard_axioms(self):
        self.assertEqual(self.classify(0, OK), (bridge.PROVED, ""))
        self.assertEqual(self.classify(0, NO_AXIOMS), (bridge.PROVED, ""))
        # warnings about unused variables are not a problem
        self.assertEqual(self.classify(0, "B0.lean:65:60: warning: Variable name `s` is not explicitly referenced.\n" + OK)[0],
                         bridge.PROVED)

    def test_every_theorem_must_report(self):
        both = "'src_a_f_bridge' does not depend on any axioms\n'src_a_g_bridge' depends on axioms: [propext]\n"
        self.assertEqual(self.classify(0, both, theorems=TWO), (bridge.PROVED, ""))
        status, reason = self.classify(0, "'src_a_f_bridge' does not depend on any axioms\n", theorems=TWO)
        self.assertEqual(status, bridge.TESTED)
        self.assertIn("src_a_g_bridge", reason)

    def test_other_axioms_are_not_proved(self):
        for axiom in ("sorryAx", "Lean.ofReduceBool", "Classical.choice, myAxiom"):
            status, reason = self.classify(0, f"'src_ledger_transfer_bridge' depends on axioms: [propext, {axiom}]\n")
            self.assertEqual(status, bridge.TESTED, axiom)
            self.assertIn(axiom.split(", ")[-1], reason)

    def test_exit_zero_without_the_axiom_report_is_not_proved(self):
        self.assertEqual(self.classify(0, "")[0], bridge.TESTED)
        self.assertEqual(self.classify(0, OK, theorems=())[0], bridge.TESTED)

    def test_an_error_is_tested_even_if_a_report_follows(self):
        # `#print axioms` still prints for a theorem whose proof had an error.
        self.assertEqual(self.classify(1, STUCK + OK)[0], bridge.TESTED)

    def test_a_tactic_giving_up_and_a_wrong_view_look_the_same_and_are_never_proved_or_failed(self):
        stuck = self.classify(1, STUCK)
        shape = self.classify(1, "B0.lean:137:2: error: Tactic `introN` failed: There are no additional binders\n")
        for status, reason in (stuck, shape):
            self.assertEqual(status, bridge.TESTED)
            self.assertIn("did not check", reason)
        self.assertIn("STUCK", stuck[1])

    def test_timeouts_and_memory(self):
        self.assertEqual(self.classify(124, "", timed_out=True), (bridge.TESTED, "the bridge proof did not finish in 120 seconds"))
        self.assertIn("memory", self.classify(137, "")[1])

    def test_nothing_is_ever_failed_from_lean_output(self):
        for status in (0, 1, 2, 124, 137):
            for output in ("", STUCK, OK, "error: unsolved goals\n⊢ False\n", "declaration uses 'sorry'"):
                self.assertNotEqual(self.classify(status, output)[0], bridge.FAILED)

    def test_reason_is_short_and_plain(self):
        _, reason = self.classify(1, "\x1b[31m/w/B0.lean:1:0: error: " + "x" * 2000 + "\x1b[0m\n")
        self.assertLess(len(reason), 600)
        self.assertNotIn("\x1b", reason)


class SettingsTests(unittest.TestCase):
    def test_defaults_and_overrides(self):
        with mock.patch.dict("os.environ", {}, clear=False) as env:
            for name in ("PROOFCI_BRIDGE_TIMEOUT", "PROOFCI_BRIDGE_BUDGET", "PROOFCI_BRIDGE_JOBS"):
                env.pop(name, None)
            timeout, budget, jobs = bridge.settings()
            self.assertEqual((timeout, budget), (120, 900))
            self.assertTrue(1 <= jobs <= 4)
            self.assertEqual(bridge.settings(timeout=30, budget=60, jobs=2), (30, 60, 2))
            self.assertEqual(bridge.settings(jobs=99)[2], 4, "never more than four Lean processes")
            env["PROOFCI_BRIDGE_TIMEOUT"] = "45"
            self.assertEqual(bridge.settings()[0], 45)
            env["PROOFCI_BRIDGE_TIMEOUT"] = "soon"
            self.assertEqual(bridge.settings()[0], 120)


def fake_extraction(effects=None, assumed=None):
    return SimpleNamespace(effects=effects or {}, assumed=assumed or {}, assumptions={}, effect_entries=[],
                           lean_file=Path("/x/Y.lean"), checkout=Path("/c"), policy=Path("/p"), root=Path("/c"), binds=[])


class RunTests(unittest.TestCase):
    """`bridge.run` with the generator and Lean replaced."""

    def run_with(self, functions, extraction=None, files=None, verdicts=None, **limits):
        files = files if files is not None else {f: f"B{i}.lean" for i, f in enumerate(functions)}
        verdicts = verdicts or {}
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(bridge, "available", return_value=True), \
                mock.patch.object(bridge, "generate", return_value=(files, {f: "no encoding" for f in functions if f not in files})), \
                mock.patch.object(bridge, "check_one", side_effect=lambda path, timeout: verdicts.get(path.name, (bridge.PROVED, "", 0.5))):
            return bridge.run(extraction or fake_extraction(), Path(tmp), functions, **limits)

    def test_each_function_gets_a_status(self):
        got = self.run_with(["a.ts::f", "a.ts::g", "a.ts::h"], verdicts={"B1.lean": (bridge.TESTED, "did not check", 1.0)},
                            files={"a.ts::f": "B0.lean", "a.ts::g": "B1.lean"})
        self.assertEqual({k: v.status for k, v in got.items()},
                         {"a.ts::f": bridge.PROVED, "a.ts::g": bridge.TESTED, "a.ts::h": bridge.TESTED})
        self.assertEqual(got["a.ts::h"].reason, "no encoding")

    def test_async_has_no_bridge_yet(self):
        got = self.run_with(["a.ts::f"], extraction=fake_extraction(effects={"a.ts::f": ["getLink"]}))
        self.assertEqual((got["a.ts::f"].status, got["a.ts::f"].reason), (bridge.TESTED, "no bridge for async code yet"))

    def test_assumed_call_has_no_bridge(self):
        got = self.run_with(["a.ts::f"], extraction=fake_extraction(assumed={"a.ts::f": ["slug::slug"]}))
        self.assertEqual(got["a.ts::f"].status, bridge.TESTED)
        self.assertIn("slug::slug", got["a.ts::f"].reason)

    def test_a_crash_while_checking_is_tested_not_proved(self):
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(bridge, "available", return_value=True), \
                mock.patch.object(bridge, "generate", return_value=({"a.ts::f": "B0.lean"}, {})), \
                mock.patch.object(bridge, "check_one", side_effect=OSError("disk full")):
            got = bridge.run(fake_extraction(), Path(tmp), ["a.ts::f"])
        self.assertEqual(got["a.ts::f"].status, bridge.TESTED)
        self.assertIn("disk full", got["a.ts::f"].reason)

    def test_missing_toolchain_is_tested_not_proved(self):
        with tempfile.TemporaryDirectory() as tmp, mock.patch.object(bridge, "available", return_value=False):
            got = bridge.run(fake_extraction(), Path(tmp), ["a.ts::f"])
        self.assertEqual(got["a.ts::f"].status, bridge.TESTED)
        self.assertIn("not installed", got["a.ts::f"].reason)

    def test_the_total_budget_is_enforced(self):
        # With no time left, nothing is started and nothing is claimed.
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(bridge, "available", return_value=True), \
                mock.patch.object(bridge, "generate", return_value=({"a.ts::f": "B0.lean"}, {})), \
                mock.patch.object(bridge, "check_one") as check_one, \
                mock.patch.object(bridge.time, "monotonic", side_effect=[0] + [1000] * 20):
            got = bridge.run(fake_extraction(), Path(tmp), ["a.ts::f"], budget=5)
        check_one.assert_not_called()
        self.assertEqual(got["a.ts::f"].status, bridge.TESTED)
        self.assertIn("budget", got["a.ts::f"].reason)

    def test_the_per_function_limit_reaches_lean(self):
        seen = []
        with tempfile.TemporaryDirectory() as tmp, \
                mock.patch.object(bridge, "available", return_value=True), \
                mock.patch.object(bridge, "generate", return_value=({"a.ts::f": "B0.lean"}, {})), \
                mock.patch.object(bridge, "check_one", side_effect=lambda p, t: seen.append(t) or (bridge.PROVED, "", 0.1)):
            bridge.run(fake_extraction(), Path(tmp), ["a.ts::f"], timeout=17, budget=500)
        self.assertEqual(seen, [17])


MANIFEST = b"""
version: 1
language: typescript
targets:
  - id: fees
    function: src/fees.ts::calculateFee
    guarantees:
      - id: capped
        theorem: fee_capped
  - id: totals
    function: src/fees.ts::sum
    guarantees:
      - id: exact
        theorem: sum_exact
"""


class PolicyTests(unittest.TestCase):
    def test_default_is_off(self):
        m = manifest.parse(MANIFEST)
        self.assertIs(m.require_bridge, False)
        self.assertFalse(m.bridge_required("src/fees.ts::sum"))

    def test_all_or_some_functions(self):
        everything = manifest.parse(MANIFEST + b"require_bridge: true\n")
        self.assertTrue(everything.bridge_required("src/fees.ts::sum"))
        some = manifest.parse(MANIFEST + b"require_bridge:\n  - src/fees.ts::sum\n")
        self.assertTrue(some.bridge_required("src/fees.ts::sum"))
        self.assertFalse(some.bridge_required("src/fees.ts::calculateFee"))

    def test_rejects_nonsense(self):
        for text in (b"require_bridge: sometimes\n", b"require_bridge: []\n", b"require_bridge: [3]\n",
                     b"require_bridge: [src/fees.ts::nothere]\n"):
            with self.assertRaises(manifest.ManifestError, msg=text):
                manifest.parse(MANIFEST + text)
        with self.assertRaises(manifest.ManifestError):
            manifest.parse(b"version: 1\nrequire_bridge: true\ntargets:\n  - id: a\n    function: m::f\n"
                           b"    guarantees:\n      - id: b\n        theorem: t\n")

    def test_changing_it_is_a_policy_change(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "proofci").mkdir()
            (root / "proofci" / "Contract.lean").write_text("")
            base = manifest.parse(MANIFEST + b"require_bridge: true\n")
            for text, expected in ((MANIFEST, True), (MANIFEST + b"require_bridge: [src/fees.ts::sum]\n", True),
                                   (MANIFEST + b"require_bridge: true\n", False)):
                changes = check.policy_changes(root, base, root, manifest.parse(text))
                self.assertEqual(any("require_bridge" in c for c in changes), expected, text)


def outcome(function, theorem):
    return check.Outcome("t", theorem, function, theorem, True, check.ERROR)


class BlockingTests(unittest.TestCase):
    """What `check._bridge` does with the statuses."""

    def blocked(self, statuses, required):
        report = check.Report(outcomes=[outcome("a.ts::f", "tf"), outcome("a.ts::g", "tg")])
        active = SimpleNamespace(bridge_required=lambda f: required is True or f in (required or ()))
        results = {f: bridge.FunctionStatus(f, s, r) for f, (s, r) in statuses.items()}
        with mock.patch.object(bridge, "run", return_value=results):
            check._bridge(report, fake_extraction(), active, Path("/w"), list(statuses), None, None)
        return report

    def test_tested_passes_by_default_and_says_so(self):
        report = self.blocked({"a.ts::f": (bridge.PROVED, ""), "a.ts::g": (bridge.TESTED, "no bridge for async code yet")}, False)
        self.assertEqual([o.status for o in report.outcomes], [check.ERROR, check.ERROR], "left for the proofs to judge")
        self.assertEqual([o.bridge for o in report.outcomes], [bridge.PROVED, bridge.TESTED])
        self.assertEqual(report.functions[1].guarantees, ["t/tg"])

    def test_require_bridge_blocks_tested(self):
        report = self.blocked({"a.ts::f": (bridge.PROVED, ""), "a.ts::g": (bridge.TESTED, "no bridge for async code yet")}, True)
        self.assertEqual([o.status for o in report.outcomes], [check.ERROR, check.UNSUPPORTED])
        self.assertIn("require_bridge", report.outcomes[1].reason)
        self.assertIn("no bridge for async code yet", report.outcomes[1].reason)

    def test_require_bridge_for_listed_functions_only(self):
        report = self.blocked({"a.ts::f": (bridge.TESTED, "x"), "a.ts::g": (bridge.TESTED, "x")}, ["a.ts::f"])
        self.assertEqual([o.status for o in report.outcomes], [check.UNSUPPORTED, check.ERROR])

    def test_a_failed_function_blocks_whatever_the_policy(self):
        report = self.blocked({"a.ts::f": (bridge.FAILED, "disagrees with Node"), "a.ts::g": (bridge.PROVED, "")}, False)
        self.assertEqual([o.status for o in report.outcomes], [check.UNSUPPORTED, check.ERROR])

    def test_report_json_counts(self):
        report = self.blocked({"a.ts::f": (bridge.PROVED, ""), "a.ts::g": (bridge.TESTED, "x")}, False)
        data = report.to_json()
        self.assertEqual(data["bridge_summary"], {"proved": 1, "tested": 1, "failed": 0})
        self.assertEqual([f["function"] for f in data["functions"]], ["a.ts::f", "a.ts::g"])
        self.assertEqual(data["guarantees"][1]["bridge"], "tested")


class SummaryTests(unittest.TestCase):
    def render(self, functions):
        report = check.Report(outcomes=[outcome("a.ts::f", "tf")], language="typescript")
        report.functions = [bridge.FunctionStatus(f, s, r, 1.5) for f, s, r in functions]
        check._attach(report)
        return summary.markdown(report.to_json())

    def test_every_function_is_listed_with_status_reason_and_counts(self):
        text = self.render([("a.ts::f", bridge.PROVED, ""), ("a.ts::g", bridge.TESTED, "no bridge for async code yet"),
                            ("a.ts::h", bridge.FAILED, "disagrees with Node | really")])
        self.assertIn("1 proved, 1 tested but not proved, 1 failed, of 3 functions", text)
        self.assertIn("`a.ts::g` | tested, not proved | no bridge for async code yet", text)
        self.assertIn("`a.ts::f` | proved", text)
        self.assertIn("tested on generated inputs but not proved", text)
        self.assertIn("disagrees with Node \\| really", text, "a pipe must not break the table")

    def test_all_proved_has_no_caveat(self):
        text = self.render([("a.ts::f", bridge.PROVED, "")])
        self.assertIn("1 proved, 0 tested but not proved, 0 failed, of 1 function.", text)
        self.assertNotIn("**Tested, not proved**", text)

    def test_rust_reports_have_no_function_section(self):
        report = check.Report(outcomes=[outcome("m::f", "t")])
        self.assertNotIn("Does the Lean view", summary.markdown(report.to_json()))


if __name__ == "__main__":
    unittest.main()
