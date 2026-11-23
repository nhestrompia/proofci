import unittest

from proofci import mutation

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
        for kind, line, text in mutants:
            self.assertIn("≤ 9007199254740991", VIEW)
            self.assertNotEqual(text, VIEW)
        # the sibling def is untouched by every mutant
        transfer_lines = VIEW.splitlines()[10:]
        for _, _, text in mutants:
            self.assertEqual(text.splitlines()[10:], transfer_lines)

    def test_kinds_and_lines(self):
        mutants = mutation.plant(VIEW, "transfer")
        kinds = {kind for kind, _, _ in mutants}
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


if __name__ == "__main__":
    unittest.main()
