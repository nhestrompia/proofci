"""Regression tests for the report-trust fixes: example-scope labelling,
uncalled/non-exported targets, Node infrastructure-failure wording, the
per-theorem hypothesis-witness check, and the one-line verdict."""

import json
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from proofci import check as check_mod, lean, sandbox, summary, typescript
from proofci.check import Outcome, Report, VERIFIED


class UncalledTests(unittest.TestCase):
    """`uncalled` flags a target no other source file imports or calls."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)

    def tearDown(self):
        self.tmp.cleanup()

    def write(self, rel, text):
        path = self.root / rel
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)

    def uncalled(self, *functions):
        return typescript.uncalled(self.root, "", list(functions))

    def test_flags_only_the_dead_target(self):
        self.write("src/dead.ts", "export function dead() { return 1; }\n")
        self.write("src/live.ts", "export function live() { return 2; }\n")
        self.write("src/app.ts", "import { live } from './live.js';\nconsole.log(live());\n")
        self.assertEqual(self.uncalled("src/dead.ts::dead", "src/live.ts::live"), ["src/dead.ts::dead"])

    def test_reexport_relay_counts(self):
        self.write("src/live.ts", "export function live() { return 2; }\n")
        self.write("src/index.ts", "export { live } from './live.js';\n")
        self.write("src/app.ts", "import { live } from './index';\n")
        self.assertEqual(self.uncalled("src/live.ts::live"), [])

    def test_star_reexport_counts(self):
        self.write("src/live.ts", "export function live() { return 2; }\n")
        self.write("src/index.ts", "export * from './live';\n")
        self.write("src/app.ts", "import { live } from './index';\n")
        self.assertEqual(self.uncalled("src/live.ts::live"), [])

    def test_namespace_use_counts(self):
        self.write("src/live.ts", "export function live() { return 2; }\n")
        self.write("src/app.ts", "import * as L from './live';\nconsole.log(L.live());\n")
        self.assertEqual(self.uncalled("src/live.ts::live"), [])

    def test_a_test_file_is_no_caller(self):
        self.write("src/dead.ts", "export function dead() { return 1; }\n")
        self.write("src/dead.test.ts", "import { dead } from './dead';\n")
        self.write("tests/use.ts", "import { dead } from '../src/dead';\n")
        self.assertEqual(self.uncalled("src/dead.ts::dead"), ["src/dead.ts::dead"])

    def test_import_by_package_name_counts(self):
        self.write("packages/lib/package.json", '{"name": "@acme/lib"}\n')
        self.write("packages/lib/src/index.ts", "export { live } from './live';\n")
        self.write("packages/lib/src/live.ts", "export function live() { return 2; }\n")
        self.write("packages/app/src/app.ts", "import { live } from '@acme/lib';\n")
        self.assertEqual(self.uncalled("packages/lib/src/live.ts::live"), [])

    def test_an_unresolvable_alias_is_no_caller_but_also_no_proof_of_death(self):
        # `@/x` (a tsconfig path alias) can't be resolved here; conservative.
        self.write("src/live.ts", "export function live() { return 2; }\n")
        self.write("src/app.ts", "import { live } from '@/live';\n")
        self.assertEqual(self.uncalled("src/live.ts::live"), ["src/live.ts::live"])

    def test_default_import_counts(self):
        self.write("src/live.ts", "export default function live() { return 2; }\n")
        self.write("src/app.ts", "import live from './live';\n")
        self.assertEqual(self.uncalled("src/live.ts::live"), [])

    def test_side_effect_import_counts(self):
        self.write("src/live.ts", "export function live() { return 2; }\n")
        self.write("src/app.ts", "import './live';\n")
        self.assertEqual(self.uncalled("src/live.ts::live"), [])

    def test_a_non_object_package_json_is_ignored(self):
        self.write("src/live.ts", "export function live() { return 2; }\n")
        self.write("tools/package.json", "[]\n")
        self.assertEqual(self.uncalled("src/live.ts::live"), ["src/live.ts::live"])

    def test_a_same_file_caller_counts(self):
        # The original delegating to an extracted core in the same file.
        self.write("src/schedule.ts",
                   "export function isSlotEquivalentCore(a, b) { return a - b === 0; }\n"
                   "export function isSlotEquivalent(a, b) { return isSlotEquivalentCore(a, b); }\n")
        self.assertEqual(self.uncalled("src/schedule.ts::isSlotEquivalentCore"), [])

    def test_a_use_on_the_declaration_line_of_another_function_counts(self):
        self.write("src/helper.ts",
                   "function helper(x) { return x - x; }\n"
                   "export function useHelper(x) { return helper(x); }\n")
        self.assertEqual(self.uncalled("src/helper.ts::helper"), [])

    def test_a_package_entry_point_is_shipped(self):
        self.write("src/main.ts", "export function live() { return 2; }\n")
        self.write("package.json", '{"name": "lib", "main": "./src/main.ts"}\n')
        self.assertEqual(self.uncalled("src/main.ts::live"), [])

    def test_the_src_index_barrel_is_shipped(self):
        self.write("src/index.ts", "export function live() { return 2; }\n")
        self.assertEqual(self.uncalled("src/index.ts::live"), [])

    def test_a_recursive_call_is_not_a_use(self):
        self.write("src/dead.ts", "export function dead() { return dead(); }\n")
        self.assertEqual(self.uncalled("src/dead.ts::dead"), ["src/dead.ts::dead"])

    def test_a_nested_index_file_is_no_entry_point(self):
        self.write("src/experimental/index.ts", "export function live() { return 2; }\n")
        self.assertEqual(self.uncalled("src/experimental/index.ts::live"),
                         ["src/experimental/index.ts::live"])

    def test_a_package_root_index_is_shipped(self):
        self.write("pkg/package.json", '{"name": "lib"}\n')
        self.write("pkg/index.ts", "export function live() { return 2; }\n")
        self.assertEqual(self.uncalled("pkg/index.ts::live"), [])

    def test_a_brace_in_a_string_does_not_hide_the_caller(self):
        self.write("src/fmt.ts",
                   "export function open() { return \"{\"; }\n"
                   "export function use() { return open() + \"}\"; }\n")
        self.assertEqual(self.uncalled("src/fmt.ts::open"), [])

    def test_an_arrow_name_starting_with_class_counts_its_callers(self):
        self.write("src/classify.ts",
                   "const classify = (x) => x;\n"
                   "export function use(x) { return classify(x); }\n")
        self.assertEqual(self.uncalled("src/classify.ts::classify"), [])

    def test_a_caller_on_the_declaration_line_of_another_arrow_counts(self):
        self.write("src/helpers.ts",
                   "const first = () => target();\n"
                   "const target = () => 0;\n")
        self.assertEqual(self.uncalled("src/helpers.ts::target"), [])

    def test_a_comment_naming_the_function_is_no_declaration(self):
        self.write("src/f.ts",
                   "// forwards through function f defined below\n"
                   "export function use() { return f(); }\n"
                   "export function f() { return 0; }\n")
        self.assertEqual(self.uncalled("src/f.ts::f"), [])

    def test_a_regex_with_a_quote_does_not_hide_the_caller(self):
        self.write("src/g.ts",
                   "export function g() { return /can't/.test(\"x\"); }\n"
                   "export function use() { return g(); }\n")
        self.assertEqual(self.uncalled("src/g.ts::g"), [])

    def test_a_name_inside_a_string_is_no_use(self):
        self.write("src/dead.ts", "export const dead = () => \"dead\";\n")
        self.assertEqual(self.uncalled("src/dead.ts::dead"), ["src/dead.ts::dead"])

    def test_a_self_call_inside_a_template_is_still_dead(self):
        self.write("src/log.ts",
                   "export function dead() { return `hit ${dead()}`; }\n")
        self.assertEqual(self.uncalled("src/log.ts::dead"), ["src/log.ts::dead"])

    def test_an_interpolated_call_counts(self):
        self.write("src/log.ts",
                   "export function tag(x) { return `hit ${x}`; }\n"
                   "export function use() { return tag(dead()); }\n"
                   "export function dead() { return 0; }\n")
        self.assertEqual(self.uncalled("src/log.ts::dead"), [])

    def test_division_after_postfix_operators_is_no_regex(self):
        self.write("src/c.ts",
                   "export function half(x) { return x / 2; }\n"
                   "export function use(n) { n++; return half(n) / n; }\n")
        self.assertEqual(self.uncalled("src/c.ts::half"), [])

    def test_a_slash_inside_a_regex_class_does_not_end_it(self):
        self.write("src/r.ts",
                   "export function r(s) { return /[/']/.test(s); }\n"
                   "export function use() { return r('a'); }\n")
        self.assertEqual(self.uncalled("src/r.ts::r"), [])

    def test_a_jsx_apostrophe_is_no_string(self):
        self.write("src/page.tsx",
                   "export function label() { return \"ok\"; }\n"
                   "export function P() { return <p>don't {label()}</p>; }\n")
        self.assertEqual(self.uncalled("src/page.tsx::label"), [])

    def test_a_root_index_with_another_entry_is_no_default(self):
        self.write("pkg/package.json", '{"name": "lib", "main": "./lib/m.js"}\n')
        self.write("pkg/index.ts", "export function dead() { return 0; }\n")
        self.assertEqual(self.uncalled("pkg/index.ts::dead"), ["pkg/index.ts::dead"])

    def test_a_main_without_dot_slash_is_an_entry(self):
        self.write("pkg/package.json", '{"name": "lib", "main": "index.js"}\n')
        self.write("pkg/index.ts", "export function live() { return 2; }\n")
        self.assertEqual(self.uncalled("pkg/index.ts::live"), [])

    def test_a_string_after_a_block_comment_opens(self):
        self.write("src/s.ts",
                   "export function dead() { return 0; }\n"
                   "export function use() { /* c */ return 'q' + dead(); }\n")
        self.assertEqual(self.uncalled("src/s.ts::dead"), [])

    def test_a_variable_named_from_divides(self):
        self.write("src/sc.ts",
                   "export function scale(x) { return x * 2; }\n"
                   "export function use(from) { return from / scale(2); }\n")
        self.assertEqual(self.uncalled("src/sc.ts::scale"), [])

    def test_a_negated_regex_is_no_use(self):
        self.write("src/dead.ts",
                   "export function dead() { return 0; }\n"
                   "export function use(x) { return !/dead/.test(x); }\n")
        self.assertEqual(self.uncalled("src/dead.ts::dead"), ["src/dead.ts::dead"])

    def test_division_after_a_unary_string_is_no_regex(self):
        self.write("src/sc.ts",
                   "export function scale(x) { return x * 2; }\n"
                   "export function use() { return +\"12\" / scale(2); }\n")
        self.assertEqual(self.uncalled("src/sc.ts::scale"), [])

    def test_a_regex_inside_an_interpolation_is_no_use(self):
        self.write("src/dead.ts",
                   "export function dead() { return 0; }\n"
                   "export function use(x) { return `p${x}${/dead/.test(x)}`; }\n")
        self.assertEqual(self.uncalled("src/dead.ts::dead"), ["src/dead.ts::dead"])

    def test_a_non_null_property_divides(self):
        self.write("src/sc.ts",
                   "export function scale(x) { return x * 2; }\n"
                   "export function use(rates) { return rates.yield! / scale(2); }\n")
        self.assertEqual(self.uncalled("src/sc.ts::scale"), [])

    def test_a_types_entry_is_no_runtime_entry(self):
        self.write("pkg/package.json",
                   '{"name": "lib", "main": "./lib/m.js", "types": "./index.d.ts"}\n')
        self.write("pkg/index.ts", "export function dead() { return 0; }\n")
        self.assertEqual(self.uncalled("pkg/index.ts::dead"), ["pkg/index.ts::dead"])

    def test_a_url_template_is_no_comment(self):
        self.write("src/api.ts",
                   "export function dead() { return 0; }\n"
                   "export function use() { return `http://a.com${dead()}/p`; }\n")
        self.assertEqual(self.uncalled("src/api.ts::dead"), [])

    def test_a_url_template_with_a_self_call_stays_dead(self):
        self.write("src/api.ts",
                   "export function dead() { return `http://a.com${dead()}/p`; }\n")
        self.assertEqual(self.uncalled("src/api.ts::dead"), ["src/api.ts::dead"])

    def test_a_quote_inside_a_comment_hides_no_string(self):
        self.write("src/api.ts",
                   "export function dead() { return 0; }\n"
                   "export function use() { /* don't */ return 'dead'; }\n")
        self.assertEqual(self.uncalled("src/api.ts::dead"), ["src/api.ts::dead"])

    def test_an_authored_src_build_directory_counts(self):
        self.write("package.json", '{"name": "lib", "main": "./src/index.ts"}\n')
        self.write("src/live.ts", "export function live() { return 2; }\n")
        self.write("src/build/tools.ts", "import { live } from '../live';\nexport const x = live();\n")
        self.assertEqual(self.uncalled("src/live.ts::live"), [])

    def test_vendored_dot_directories_are_skipped_and_fast(self):
        import time
        for i in range(1500):
            self.write(f".repos/vendor/pkg/f{i}.ts", f"export function f{i}() {{ return {i}; }}\n")
        self.write("src/dead.ts", "export function dead() { return 0; }\n")
        started = time.monotonic()
        self.assertEqual(self.uncalled("src/dead.ts::dead"), ["src/dead.ts::dead"])
        self.assertLess(time.monotonic() - started, 10)


class FunctionWarningTests(unittest.TestCase):
    """`_function_warnings` explains why a target could not be exercised."""

    def test_nonexported_target(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "src").mkdir()
            (root / "src/helper.ts").write_text("function helper(x) { return x - x; }\n")
            extraction = SimpleNamespace(signatures={"src/helper.ts::helper": {"exported": False}})
            warned = check_mod._function_warnings(root, "", extraction, ["src/helper.ts::helper"], {})
            self.assertTrue(any("is not exported" in w for w in warned["src/helper.ts::helper"]))
            self.assertTrue(any("nothing in the repository calls" in w
                                for w in warned["src/helper.ts::helper"]))


class NodeFailureTests(unittest.TestCase):
    """`_node_failure` reports the crash, not a disagreement."""

    def result(self, status, output, timed_out=False):
        return sandbox.Result(status, output, timed_out)

    def test_oom(self):
        why = typescript._node_failure(self.result(134, "FATAL ERROR: Reached heap limit Allocation failed - JavaScript heap out of memory"))
        self.assertIn("out of memory", why)
        self.assertIn("heap out of memory", why)

    def test_exit_status(self):
        why = typescript._node_failure(self.result(1, "Error: not in this environment\n    at ..."))
        self.assertIn("exited with status 1", why)
        self.assertIn("not in this environment", why)

    def test_timed_out(self):
        why = typescript._node_failure(self.result(124, "", timed_out=True))
        self.assertIn("did not finish", why)

    def test_empty_output(self):
        why = typescript._node_failure(self.result(1, ""))
        self.assertIn("printed nothing", why)


class VacuityTests(unittest.TestCase):
    """A failing theorem is retried alone; the error is carried, not dropped."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.ws = lean.Workspace(Path(self.tmp.name), "Ledger")

    def tearDown(self):
        self.tmp.cleanup()

    def vacuity(self, outputs):
        """Run `vacuity` with `_lake` replaying the given outputs per call."""
        calls = []

        def fake_lake(ws, argv, timeout=300):
            calls.append(argv[-1])
            return outputs[len(calls) - 1]

        with patch.object(lean, "_lake", side_effect=fake_lake):
            verdicts, errors = lean.vacuity(self.ws, [("thm_a", [["one"]]), ("thm_b", [["two"]])])
        return verdicts, errors, calls

    def marker(self, i, result="satisfied"):
        return f"{lean.VACUITY_MARKER}{i} " + json.dumps({"result": result, "hypothesis": "h"}) + "\n"

    def test_one_bad_theorem_does_not_disable_the_check(self):
        # The batch reports only case 0; the per-theorem retry of thm_b judges it.
        verdicts, errors, calls = self.vacuity([
            sandbox.Result(0, self.marker(0)),
            sandbox.Result(0, self.marker(0)),
        ])
        self.assertEqual(verdicts, {"thm_a": [{"result": "satisfied", "hypothesis": "h"}],
                                  "thm_b": [{"result": "satisfied", "hypothesis": "h"}]})
        self.assertEqual(errors, {})
        self.assertEqual(calls, ["Vacuity.lean", "VacuitySingle.lean"])

    def test_the_lean_error_is_carried_and_named(self):
        verdicts, errors, _ = self.vacuity([
            sandbox.Result(1, "error: tactic failed\n"),
            sandbox.Result(1, "error: tactic failed\n"),
            sandbox.Result(1, "error: elaboration failed\n  deep error"),
        ])
        self.assertEqual(verdicts, {})
        self.assertIn("thm_a", errors)
        self.assertIn("thm_b", errors)
        self.assertIn("deep error", errors["thm_b"])

    def test_missing_marker_means_error(self):
        verdicts, errors, _ = self.vacuity([
            sandbox.Result(0, "nothing printed\n"),
            sandbox.Result(0, "still nothing\n"),
            sandbox.Result(0, "still nothing\n"),
        ])
        self.assertEqual(verdicts, {})
        self.assertEqual(sorted(errors), ["thm_a", "thm_b"])


class ScopeTests(unittest.TestCase):
    """`scope: "example"` blocks under `require_general`, warns otherwise."""

    def report(self, scope, general=False):
        report = Report(language="typescript", general_required=general)
        report.outcomes = [Outcome("t", "g", "src/x.ts::f", "thm", True, VERIFIED, scope=scope)]
        return report

    def test_example_scope_blocks_only_under_require_general(self):
        self.assertTrue(self.report("example", general=False).passed)
        self.assertFalse(self.report("example", general=True).passed)
        self.assertTrue(self.report(None, general=True).passed)

    def test_scope_serializes(self):
        data = self.report("example", general=True).to_json()
        self.assertEqual(data["guarantees"][0]["scope"], "example")
        self.assertTrue(data["require_general"])


class VerdictTests(unittest.TestCase):
    """The one-line verdict names the escape once — the strength note carries the detail."""

    def report(self):
        return {
            "passed": False, "language": "typescript", "policy_source": "base",
            "policy_changes": [], "require_strength": True,
            "guarantees": [
                {"target": "view", "guarantee": "denies", "function": "src/ledger.ts::canViewLink",
                 "theorem": "canViewLink_denies", "required": True, "status": "verified",
                 "reason": "", "strength": [
                     "`canViewLink_denies` still verifies with a planted defect in `src/ledger.ts::canViewLink`; "
                     "it would also pass if `canViewLink` always returned `false`"]}],
            "escapes": [{"guarantee": "view/denies", "theorem": "canViewLink_denies",
                         "function": "src/ledger.ts::canViewLink",
                         "accepts": ["`canViewLink` always returned `false`"], "defects": []}]}

    def test_the_escape_is_named_once(self):
        text = summary.markdown(self.report())
        self.assertEqual(text.count("always returned `false`"), 1)
        verdict = next(l for l in text.splitlines() if l.startswith("**Result: blocked**"))
        self.assertIn("`view/denies`", verdict)
        self.assertNotIn("it would also pass", verdict)

    def test_function_warnings_show_next_to_the_table(self):
        report = self.report() | {"functions": [
            {"function": "src/dead.ts::dead", "status": "proved", "reason": "", "seconds": 1.0,
             "warnings": ["nothing in the repository calls `dead`; these guarantees don't cover shipped code"]}]}
        text = summary.markdown(report)
        self.assertIn("nothing in the repository calls `dead`", text)

    def test_example_scope_is_labelled(self):
        report = self.report() | {"passed": True, "policy_changes": ["x"],
                                  "guarantees": [self.report()["guarantees"][0] | {"scope": "example"}]}
        text = summary.markdown(report)
        self.assertIn("checks one fixed input only", text)


if __name__ == "__main__":
    unittest.main()
