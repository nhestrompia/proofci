import itertools
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from proofci import check, lean, mutation, sandbox

VIEW = """\
import Foo

def calculateFee (amount rate : Js.Num) : Result Js.Num := do
  let fee ← if amount.val * rate.val ≤ 9007199254740991 then
    Result.ok (Js.min (Js.lit (amount.val * rate.val / 10000)) (Js.lit 500))
  else
    Result.ok (Js.lit 0)
  Result.ok fee

def transfer (a : Accounts) (amount : Js.Num) : Result (Option Accounts) := do
  if amount.val ≤ 0 || a.from.val < amount.val then
    Result.ok none
  else
    Result.ok (some { from := a.from.val - amount.val, to := a.to.val + amount.val })
"""


class PlantTest(unittest.TestCase):
    def test_mutants_stay_inside_the_named_def(self):
        mutants = mutation.plant(VIEW, "calculateFee")
        self.assertTrue(mutants)
        for kind, line, src, text in mutants:
            self.assertIn("≤ 9007199254740991", VIEW)
            self.assertNotEqual(text, VIEW)
            self.assertIn(src, text)
        # the sibling def is untouched by every mutant
        transfer_lines = VIEW.splitlines()[9:]
        for _, _, _, text in mutants:
            start = text.splitlines().index("def transfer (a : Accounts) (amount : Js.Num) : Result (Option Accounts) := do")
            self.assertEqual(text.splitlines()[start:], transfer_lines)

    def test_kinds_and_lines(self):
        mutants = mutation.plant(VIEW, "transfer")
        kinds = {kind for kind, _, _, _ in mutants}
        self.assertIn("le-to-lt", kinds)

    def test_unknown_function_gives_no_mutants(self):
        self.assertEqual(mutation.plant(VIEW, "missing"), [])

    def test_limit(self):
        # The limit caps line-level mutants; structural ones (result-shape,
        # filter, trivial implementations) are always appended.
        line_kinds = {k for k, _, _, _ in mutation.plant(VIEW, "transfer", limit=1)}
        self.assertLessEqual(len(line_kinds - {"trivial-constant", "trivial-fail"}), 1)


TS_VIEW = """\
import ProofciJs
open Aeneas Aeneas.Std Result

def src.api.filterSubset (user : User) (perms : (List Perm)) : Result (List Perm) := do
  let tmp1 ← Js.filter (fun (p : Perm) => do
    let tmp2 ← Js.has user.perms p.name
    Result.ok (decide (tmp2 = true))
  ) perms
  Result.ok tmp1

def src.api.active (phase : Phase) : Result Bool := do
  match phase.fromAge with
  | none =>
    Result.ok false
  | some tmp3 =>
    Result.ok (decide (tmp3.val ≤ 30))

def src.api.permit (auth : Auth) (id : Js.Str) : Proofci.Effects.Eff Bool := do
  if auth.user = none then
    Result.ok false
  else
    Result.ok true
"""


class TsPlantTest(unittest.TestCase):
    """Operators that hit TypeScript-generated Lean: `Js.*` calls, `decide`,
    `match`/`if` branches, `some _` results, list results."""

    def test_filter_that_drops_nothing(self):
        mutants = mutation.plant(TS_VIEW, "src.api.filterSubset")
        kinds = {k for k, _, _, _ in mutants}
        self.assertIn("filter-keeps-all", kinds)
        mutant = next(text for k, _, _, text in mutants if k == "filter-keeps-all")
        self.assertIn("let tmp1 ← Result.ok perms", mutant)

    def test_decide_if_and_option_operators(self):
        kinds = {k for k, _, _, _ in mutation.plant(TS_VIEW, "src.api.active", limit=30)}
        self.assertIn("negate-decide", kinds)

    def test_trivial_implementations_come_from_the_signature(self):
        mutants = mutation.plant(TS_VIEW, "src.api.filterSubset", limit=30)
        kinds = {k for k, _, _, _ in mutants}
        self.assertIn("trivial-arg", kinds)
        self.assertIn("trivial-constant", kinds)
        self.assertIn("trivial-fail", kinds)
        arg = next(text for k, _, _, text in mutants if k == "trivial-arg")
        # `perms` is the parameter of the result type `(List Perm)`
        self.assertIn("Result.ok perms", arg)
        self.assertIn("def src.api.filterSubset", arg)
        self.assertNotIn("Js.filter", arg)

    def test_trivial_constants_match_the_result_type(self):
        terms = {(k, src) for k, _, src, _ in mutation.plant(TS_VIEW, "src.api.active", limit=30)}
        self.assertIn(("trivial-constant", "true"), terms)
        self.assertIn(("trivial-constant", "false"), terms)
        texts = [t for k, _, _, t in mutation.plant(TS_VIEW, "src.api.active", limit=30)
                 if k == "trivial-constant"]
        self.assertIn("Result.ok true", texts[0])

    def test_trivial_constants_for_an_effect_result(self):
        terms = [(k, src, t) for k, _, src, t in
                 mutation.plant(TS_VIEW, "src.api.permit", limit=30) if k == "trivial-constant"]
        self.assertTrue(any("Proofci.Effects.Eff.pure false" in t for _, _, t in terms))
        self.assertIn(("trivial-constant", "false"), [(k, s) for k, s, _ in terms])

    def test_a_trivial_impl_identical_to_the_code_is_no_mutant(self):
        # The function already returns `perms` unchanged; the `-- src:` comment
        # the mutant drops must not make it count as a defect.
        view = ('def same (perms : (List Perm)) : Result (List Perm) := do\n'
                '  -- src:api.ts:2\n'
                '  Result.ok perms\n')
        kinds = {k for k, _, _, _ in mutation.plant(view, "same")}
        self.assertNotIn("trivial-arg", kinds)

    def test_describe_never_shows_generated_lean(self):
        banned = ("Js.", "Result.", "≠", "≤", "≥", "∧", "∨", "¬", " : ", "none", "some")
        srcs = {"num-literal": "Js.lit (21)", "int-literal": "(21 : Int)",
                "dbl-literal": "Js.Dbl.lit 0x15", "f64-op": "Core.F64.ceil",
                "filter-keeps-all": "let tmp1 ← Result.ok perms",
                "trivial-arg": "Result.ok perms"}
        originals = {"num-literal": "Js.lit (20)", "int-literal": "(20 : Int)",
                     "dbl-literal": "Js.Dbl.lit 0x14", "f64-op": "Core.F64.floor"}
        kinds = list(mutation.KINDS) + ["filter-keeps-all", "trivial-arg", "trivial-fail"]
        for kind in kinds:
            out = mutation.describe(kind, 4, srcs.get(kind, "x"), originals.get(kind, "x"),
                                    ts="src/x.ts:4")
            for word in banned:
                self.assertNotIn(word, out, f"{kind}: {out}")
        for constant in ("Result.ok (Js.lit (0))",
                         "Result.ok ([] : Js.Str)", 'Result.ok ""', "Result.ok []",
                         "Result.ok (0 : Int)", "Result.ok true", "Result.ok false",
                         "Result.ok none", "Proofci.Effects.Eff.pure false"):
            for sig in (None, {"result": {"nothing": "null"}}, {"result": {"nothing": "undefined"}}):
                out = mutation.describe("trivial-constant", 4, constant, "", ts="src/x.ts:4", sig=sig)
                for word in banned:
                    self.assertNotIn(word, out, f"{constant}: {out}")

    def test_describe_states_the_accepted_behaviour(self):
        self.assertEqual(mutation.describe("trivial-arg", 2, "Result.ok perms", ""),
                         "returned `perms` unchanged")
        self.assertEqual(mutation.describe("filter-keeps-all", 5, "let t ← Result.ok xs", ""),
                         "returned `xs` without filtering it")
        self.assertEqual(mutation.describe("js-add-to-sub", 3, "x", "y"),
                         "used `-` where the code uses `+`")

    def test_describe_names_the_typescript_source_not_the_lean_line(self):
        marks = mutation.source_map("-- src:src/lib/x.ts:12\ndef f := do\n  -- src:src/lib/x.ts:14\n  a\n  b\n")
        self.assertEqual(mutation.ts_at(marks, 4), "src/lib/x.ts:14")
        self.assertEqual(mutation.ts_at(marks, 2), "src/lib/x.ts:12")
        self.assertEqual(mutation.describe("negate-branch", 4, "if ¬(x) then", "if x then",
                                          ts=mutation.ts_at(marks, 4)),
                         "the `if` on src/lib/x.ts line 14 were negated")
        self.assertEqual(mutation.describe("num-literal", 4, "Js.lit (21)", "Js.lit (20)",
                                          ts=mutation.ts_at(marks, 4)),
                         "`20` on src/lib/x.ts line 14 were `21`")
        # No map: the operator change is described without any line number.
        self.assertEqual(mutation.describe("negate-branch", 4, "if ¬(x) then", "if x then"),
                         "the condition were negated")

    def test_src_comments_are_not_mutation_targets(self):
        text = "-- src:src/x.ts:12\ndef f (a : Js.Num) : Result Js.Num := do\n  -- src:src/x.ts:13\n  if a.val < 4 then\n    Result.ok a\n  else\n    Result.ok a\n"
        lines = text.splitlines(keepends=True)
        kinds = [k for k, line, src, _ in mutation.plant(text, "f")]
        self.assertTrue(all("src:" not in s for _, _, s, _ in mutation.plant(text, "f")))

    def run_check(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Model.lean").write_text(TS_VIEW)
            ws = SimpleNamespace(root=root, crate_module="Model")
            o = SimpleNamespace(function="f", theorem="t")
            seen = itertools.count()
            def fake_eval(ws, calls, text, timeout):
                return {0: "r0"} if next(seen) == 0 else {0: "r1"}
            with patch.object(mutation, "_eval_outputs", fake_eval), \
                 patch.object(lean, "clone", return_value=ws), \
                 patch.object(lean, "_lake", return_value=sandbox.Result(0, "", False)):
                return mutation.check(ws, root, TS_VIEW, {"f": [["x"]]},
                                      {"f": "src.api.filterSubset"}, 1, [o], [o])

    def test_check_planted_counts_per_function(self):
        _, planted = self.run_check()
        self.assertEqual(set(planted), {"f"})
        self.assertGreater(planted["f"], 0)

    def test_check_with_no_inputs_plants_nothing(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Model.lean").write_text(TS_VIEW)
            ws = SimpleNamespace(root=root, crate_module="Model")
            o = SimpleNamespace(function="f", theorem="t")
            escaped, planted = mutation.check(ws, root, TS_VIEW, {}, {"f": "src.api.filterSubset"},
                                              1, [o], [o])
        self.assertEqual(escaped, {})
        self.assertEqual(planted, {})

    def test_a_mutant_the_proof_build_rejects_is_not_an_escape(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Model.lean").write_text(TS_VIEW)
            (root / "Proofs.lean").write_text("theorem t := by\n  skip\n")
            ws = SimpleNamespace(root=root, crate_module="Model")
            o = SimpleNamespace(function="f", theorem="t")
            seen = itertools.count()
            def fake_eval(ws, calls, text, timeout):
                return {0: "r0"} if next(seen) == 0 else {0: "r1"}
            lake = sandbox.Result(1, "error: Proofs.lean:1:15: failed", False)
            with patch.object(mutation, "_eval_outputs", fake_eval), \
                 patch.object(lean, "clone", return_value=ws), \
                 patch.object(lean, "_lake", return_value=lake):
                escaped, _ = mutation.check(ws, root, TS_VIEW, {"f": [["x"]]},
                                            {"f": "src.api.filterSubset"}, 1, [o], [o])
        self.assertEqual(escaped, {})

    def test_escape_entries_describe_the_accepted_behaviour(self):
        escaped, _ = self.run_check()
        kinds = {m["kind"] for m in escaped["t"]}
        self.assertIn("trivial-arg", kinds)
        plains = {m["plain"] for m in escaped["t"]}
        self.assertIn("returned `perms` unchanged", plains)
        self.assertTrue(all(m["desc"] and m["plain"] for m in escaped["t"]))

    def test_a_rejected_mutant_does_not_hide_an_escape(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Model.lean").write_text(TS_VIEW)
            ws = SimpleNamespace(root=root, crate_module="Model")
            o = SimpleNamespace(function="f", theorem="t")
            seen = itertools.count()
            def fake_eval(ws, calls, text, timeout):
                return {0: "r0"} if next(seen) == 0 else {0: "r1"}
            calls = {"n": 0}
            def lake(ws, args, timeout=None):
                # every second mutant module is rejected by the theorem
                calls["n"] += 1
                return sandbox.Result(0 if calls["n"] % 2 else 1, "", False)
            with patch.object(mutation, "_eval_outputs", fake_eval), \
                 patch.object(lean, "clone", return_value=ws), \
                 patch.object(lean, "_lake", side_effect=lake):
                escaped, _ = mutation.check(ws, root, TS_VIEW, {"f": [["x"]]},
                                            {"f": "src.api.filterSubset"}, 1, [o], [o])
        self.assertIn("t", escaped)


class FailedDeclarationsTest(unittest.TestCase):
    def test_maps_error_lines_to_declarations(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Proofs.lean").write_text(
                "theorem a := by\n  skip\n\ntheorem b := by\n  sorry\n")
            failed = mutation._failed_declarations(root, "error: Proofs.lean:4:8: failed")
            self.assertEqual(failed, {"b"})

    def test_plain_lean_error_format_and_warnings(self):
        import tempfile
        from pathlib import Path
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Proofs.lean").write_text("theorem a := by\n  skip\n")
            self.assertEqual(
                mutation._failed_declarations(root, "Proofs.lean:2:2: error: failed"), {"a"})
            # warning diagnostics are not failures: nothing is attributed
            self.assertEqual(
                mutation._failed_declarations(root, "warning: Proofs.lean:1:4: sorry used"), set())


class UnknownMutantsTest(unittest.TestCase):
    """A mutant we cannot judge is dropped, never counted as an escape."""

    def run_check(self, evals, build, proofs=""):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Model.lean").write_text(VIEW)
            (root / "Proofs.lean").write_text(proofs)
            ws = SimpleNamespace(root=root, crate_module="Model")
            o = SimpleNamespace(function="f", theorem="t")
            seen = itertools.count()
            def fake_eval(ws, calls, text, timeout):
                return evals(next(seen))
            with patch.object(mutation, "_eval_outputs", fake_eval), \
                 patch.object(lean, "clone", return_value=ws), \
                 patch.object(lean, "_lake", return_value=build):
                return mutation.check(ws, root, VIEW, {"f": [["x"]]},
                                      {"f": "transfer"}, 1, [o], [o])

    def test_failed_mutant_eval_is_unknown_not_escape(self):
        escaped, _ = self.run_check(lambda i: {0: "r0"} if i == 0 else None,
                                    sandbox.Result(0, "", False))
        self.assertEqual(escaped, {})

    def test_unmapped_build_failure_is_unknown_not_escape(self):
        escaped, _ = self.run_check(lambda i: {0: "r0"} if i == 0 else {0: "r1"},
                                    sandbox.Result(1, "error: boom", False))
        self.assertEqual(escaped, {})

    def test_failure_of_another_guarantee_is_inconclusive_not_escape(self):
        """`other` is a verified theorem of a different function; its failure
        means the mutant's build was not clean, so it is judged inconclusive —
        not reported as an escape of the guarantees under test."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Model.lean").write_text(VIEW)
            (root / "Proofs.lean").write_text("theorem other := by\n  skip\n  skip\n  skip\n")
            ws = SimpleNamespace(root=root, crate_module="Model")
            o = SimpleNamespace(function="f", theorem="t")
            other = SimpleNamespace(function="g", theorem="other")
            seen = itertools.count()
            def fake_eval(ws, calls, text, timeout):
                return {0: "r0"} if next(seen) == 0 else {0: "r1"}
            with patch.object(mutation, "_eval_outputs", fake_eval), \
                 patch.object(lean, "clone", return_value=ws), \
                 patch.object(lean, "_lake", return_value=sandbox.Result(
                     1, "error: Proofs.lean:3:8: failed", False)):
                escaped, _ = mutation.check(ws, root, VIEW, {"f": [["x"]]},
                                            {"f": "transfer"}, 1, [o], [o, other])
        self.assertEqual(escaped, {})

    def test_broken_proof_helper_is_inconclusive_not_escape(self):
        """The failing `helper` is no guarantee's theorem — its module may never
        have been built, so the mutant is dropped rather than counted escaped."""
        escaped, _ = self.run_check(lambda i: {0: "r0"} if i == 0 else {0: "r1"},
                                    sandbox.Result(1, "error: Proofs.lean:3:8: failed", False),
                                    "theorem helper := by\n  skip\n  skip\n  skip\n")
        self.assertEqual(escaped, {})

    def test_an_unchanged_guarantee_that_rejects_suppresses_the_warning(self):
        """The suspect is `t`, but `peer` — an unchanged verified guarantee of
        the same function — rejects the mutant, so `t` does not warn."""
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Model.lean").write_text(VIEW)
            (root / "Proofs.lean").write_text("theorem peer := by\n  skip\n  skip\n  skip\n")
            ws = SimpleNamespace(root=root, crate_module="Model")
            suspect = SimpleNamespace(function="f", theorem="t")
            peer = SimpleNamespace(function="f", theorem="peer")
            seen = itertools.count()
            def fake_eval(ws, calls, text, timeout):
                return {0: "r0"} if next(seen) == 0 else {0: "r1"}
            with patch.object(mutation, "_eval_outputs", fake_eval), \
                 patch.object(lean, "clone", return_value=ws), \
                 patch.object(lean, "_lake", return_value=sandbox.Result(
                     1, "error: Proofs.lean:3:8: failed", False)):
                escaped, _ = mutation.check(ws, root, VIEW, {"f": [["x"]]},
                                            {"f": "transfer"}, 1, [suspect], [suspect, peer])
        self.assertEqual(escaped, {})


    def run_with_proofs(self, proofs, build, outcomes, candidates):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "Model.lean").write_text(VIEW)
            (root / "Proofs.lean").write_text(proofs)
            ws = SimpleNamespace(root=root, crate_module="Model")
            seen = itertools.count()
            def fake_eval(ws, calls, text, timeout):
                return {0: "r0"} if next(seen) == 0 else {0: "r1"}
            with patch.object(mutation, "_eval_outputs", fake_eval), \
                 patch.object(lean, "clone", return_value=ws), \
                 patch.object(lean, "_lake", return_value=build):
                return mutation.check(ws, root, VIEW, {"f": [["x"]]},
                                      {"f": "transfer"}, 1, candidates, outcomes)

    def test_namespaced_proof_failure_rejects(self):
        """A theorem inside `namespace Q` fails the mutant build; the qualified
        name must still match the manifest's `Q.peer`."""
        suspect = SimpleNamespace(function="f", theorem="t")
        peer = SimpleNamespace(function="f", theorem="Q.peer")
        escaped, _ = self.run_with_proofs(
            "namespace Q\ntheorem peer := by\n  skip\n  skip\nend Q\n",
            sandbox.Result(1, "error: Proofs.lean:3:8: failed", False),
            [suspect, peer], [suspect])
        self.assertEqual(escaped, {})

    def test_helper_plus_own_failure_still_rejects(self):
        """The build broke a helper AND the suspect's theorem: the rejection
        counts even though the helper makes part of it inconclusive."""
        suspect = SimpleNamespace(function="f", theorem="t")
        escaped, _ = self.run_with_proofs(
            "theorem helper := by\n  skip\n  skip\n  skip\n"
            "theorem t := by\n  skip\n  skip\n  skip\n",
            sandbox.Result(1, "error: Proofs.lean:3:8: failed\nerror: Proofs.lean:7:8: failed", False),
            [suspect], [suspect])
        self.assertEqual(escaped, {})


class SuspectsTest(unittest.TestCase):
    def test_first_adoption_sweeps_every_guarantee(self):
        # An empty base map (first adoption) makes every statement "new", so
        # all verified guarantees get the sweep — line mutants and the
        # trivial implementations — without PROOFCI_MUTATION_FULL.
        outcomes = [SimpleNamespace(theorem="t1"), SimpleNamespace(theorem="t2")]
        head = {"t1": {"statement": "s1"}, "t2": {"statement": "s2"}}
        self.assertEqual(check.mutation_suspects(outcomes, {}, head), outcomes)

    def test_unchanged_statements_are_not_swept(self):
        outcomes = [SimpleNamespace(theorem="t1"), SimpleNamespace(theorem="t2")]
        base = {"t1": {"statement": "same"}, "t2": {"statement": "same"}}
        head = {"t1": {"statement": "same"}, "t2": {"statement": "changed"}}
        self.assertEqual(check.mutation_suspects(outcomes, base, head), [outcomes[1]])


if __name__ == "__main__":
    unittest.main()
