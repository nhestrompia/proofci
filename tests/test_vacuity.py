import itertools
import tempfile
import unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch

from proofci import lean, mutation, sandbox

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
        transfer_lines = VIEW.splitlines()[10:]
        for _, _, _, text in mutants:
            self.assertEqual(text.splitlines()[10:], transfer_lines)

    def test_kinds_and_lines(self):
        mutants = mutation.plant(VIEW, "transfer")
        kinds = {kind for kind, _, _, _ in mutants}
        self.assertIn("le-to-lt", kinds)

    def test_unknown_function_gives_no_mutants(self):
        self.assertEqual(mutation.plant(VIEW, "missing"), [])

    def test_limit(self):
        self.assertLessEqual(len(mutation.plant(VIEW, "transfer", limit=1)), 1)


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

    def test_failure_of_another_guarantee_still_counts_as_escape(self):
        """`other` is a verified theorem of a different function; the mutant
        still escapes the guarantees under test."""
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
        self.assertIn("t", escaped)

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


if __name__ == "__main__":
    unittest.main()
