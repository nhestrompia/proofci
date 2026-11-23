import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from proofci import check, claims, summary  # noqa: E402

CONTRACT = """\
import TsBank
open Aeneas Aeneas.Std Result src.ledger

/-- The fee never exceeds the cap, and computing it stays in safe integers. -/
theorem fee_capped (amount rate : Js.Num) (h : amount.val * rate.val ≤ 9007199254740991)
    (h' : -9007199254740991 ≤ amount.val * rate.val) :
    calculateFee amount rate ⦃ fee => fee.val ≤ 500 ⦄ := by sorry

-- a plain comment is not a claim
theorem undocumented (a : Accounts) : transfer a 0 = ok (some a) := by sorry

/-- A label is a tag followed by at least one character, assuming `slug` succeeds. -/
theorem label_tagged (title : Js.Str)
    (slug_nonempty : ∃ s, Proofci.Assumed.slug_maker.slug title = ok s ∧ s ≠ []) :
    label title ⦃ r => r.head? = some 35 ∧ 2 ≤ r.length ⦄ := by sorry
"""


class ClaimTests(unittest.TestCase):
    def test_reads_the_doc_comment(self):
        found = claims.theorems(CONTRACT)
        self.assertEqual(found["fee_capped"]["claim"],
                         "The fee never exceeds the cap, and computing it stays in safe integers.")

    def test_plain_comments_are_not_claims(self):
        self.assertIsNone(claims.theorems(CONTRACT)["undocumented"]["claim"])

    def test_hypotheses_are_named_proposition_binders(self):
        found = claims.theorems(CONTRACT)
        self.assertEqual(found["fee_capped"]["hypotheses"],
                         ["h : amount.val * rate.val ≤ 9007199254740991",
                          "h' : -9007199254740991 ≤ amount.val * rate.val"])
        self.assertEqual(found["label_tagged"]["hypotheses"],
                         ["slug_nonempty : ∃ s, Proofci.Assumed.slug_maker.slug title = ok s ∧ s ≠ []"])

    def test_hypotheses_keep_binders_with_nested_parentheses(self):
        found = claims.theorems(
            "theorem t (xs : List Int) (h : ∀ x, x ∈ xs → f (g (h' x)) > 0)\n"
            "  (nolinks : ¬ ∃ a b, P (Q a (R b))) : True := by sorry")
        self.assertEqual(found["t"]["hypotheses"],
                         ["h : ∀ x, x ∈ xs → f (g (h' x)) > 0",
                          "nolinks : ¬ ∃ a b, P (Q a (R b))"])

    def test_hypotheses_ignore_comments_strings_and_instance_ascriptions(self):
        found = claims.theorems(
            'theorem t (n : Int) [Decidable (0 < n : Prop)] -- a lone ) here\n'
            '  (h : s ≠ "(") : True := by sorry')
        self.assertEqual(found["t"]["hypotheses"], ['h : s ≠ "("'])

    def test_hypotheses_survive_comment_markers_and_brackets_in_literals(self):
        found = claims.theorems(
            'theorem t (h : s ≠ "--") (k : c = \'(\') (m : c ≠ \']\')\n'
            "  (h' : s ≠ t) : True := by sorry")
        self.assertEqual(found["t"]["hypotheses"],
                         ['h : s ≠ "--"', "k : c = '('", "m : c ≠ ']'", "h' : s ≠ t"])

    def test_statement_is_the_signature_on_one_line(self):
        statement = claims.theorems(CONTRACT)["fee_capped"]["statement"]
        self.assertEqual(statement, "theorem fee_capped (amount rate : Js.Num) "
                                  "(h : amount.val * rate.val ≤ 9007199254740991) "
                                  "(h' : -9007199254740991 ≤ amount.val * rate.val) : "
                                  "calculateFee amount rate ⦃ fee => fee.val ≤ 500 ⦄")

    def test_attributes_between_doc_and_theorem(self):
        found = claims.theorems("/-- Sums keep order. -/\n@[simp]\ntheorem keeps_order : True := by sorry")
        self.assertEqual(found["keeps_order"]["claim"], "Sums keep order.")

    def test_summary_lists_claim_status_and_reliance(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", True, check.VERIFIED)
        info = claims.theorems(CONTRACT)["fee_capped"]
        o.claim, o.statement, o.hypotheses = info["claim"], info["statement"], info["hypotheses"]
        o.assumes = ["core::num::checked_add"]
        o.bridge = "tested"
        text = summary.markdown(check.Report(outcomes=[o], language="typescript").to_json())
        self.assertIn("`t/g` — **verified**: The fee never exceeds the cap", text)
        self.assertIn("it holds only when `h : amount.val * rate.val ≤ 9007199254740991`", text)
        self.assertIn("the trusted model of `core::num::checked_add`", text)
        self.assertIn("tested against Node but not proved", text)

    def test_summary_marks_a_missing_claim(self):
        o = check.Outcome("t", "g", "m::f", "undocumented", True, check.UNPROVEN)
        text = summary.markdown(check.Report(outcomes=[o]).to_json())
        self.assertIn("no `/--` doc comment", text)

    def test_namespaced_theorems_key_by_qualified_name(self):
        contract = ("namespace Fees\n\n/-- The fee is capped. -/\ntheorem capped : True := by sorry\n\n"
                    "end Fees\n\n/-- Free theorems. -/\ntheorem free_ok : True := by sorry\n")
        found = claims.theorems(contract)
        self.assertEqual(found["Fees.capped"]["claim"], "The fee is capped.")
        self.assertNotIn("capped", found)
        self.assertEqual(found["free_ok"]["claim"], "Free theorems.")

    def test_a_section_end_does_not_close_the_namespace(self):
        contract = ("namespace Fees\nsection Helpers\n/-- Helper lemma. -/\n"
                    "theorem helper : True := by sorry\nend Helpers\n"
                    "/-- The fee is capped. -/\ntheorem capped : True := by sorry\nend Fees\n")
        found = claims.theorems(contract)
        self.assertEqual(found["Fees.capped"]["claim"], "The fee is capped.")
        # `end Helpers` closes the section; the namespace keeps qualifying names
        self.assertEqual(found["Fees.helper"]["claim"], "Helper lemma.")

    def test_keywords_inside_comments_do_not_open_scopes(self):
        contract = ("/-\nnamespace Fake\n-/\n"
                    "/-- The fee is capped. -/\ntheorem capped : True := by sorry\n")
        found = claims.theorems(contract)
        self.assertIn("capped", found)
        self.assertNotIn("Fake.capped", found)

    def test_a_comment_between_doc_and_theorem_does_not_merge(self):
        contract = ("/-- Doc for a helper. -/\n"
                    "/- an ordinary block comment -/\n"
                    "theorem undocumented : True := by sorry\n")
        self.assertIsNone(claims.theorems(contract)["undocumented"]["claim"])

    def test_verdict_says_passed(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", True, check.VERIFIED)
        text = summary.markdown(check.Report(outcomes=[o]).to_json())
        self.assertIn("**Result: passed** — all 1 required guarantees verified.", text)

    def test_verdict_names_unverified_guarantees(self):
        ok = check.Outcome("t", "g", "m::f", "fee_capped", True, check.VERIFIED)
        bad = check.Outcome("t", "g2", "m::f", "undocumented", True, check.UNPROVEN)
        text = summary.markdown(check.Report(outcomes=[ok, bad]).to_json())
        self.assertIn("**Result: blocked** — 1 of 2 required guarantees not verified.", text)

    def test_verdict_names_a_pending_policy_change(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", True, check.VERIFIED)
        r = check.Report(outcomes=[o], policy_changes=["guarantee g added"])
        text = summary.markdown(r.to_json())
        self.assertIn("policy change waits for maintainer approval", text)

    def test_verdict_names_an_invalid_contract(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", True, check.VERIFIED)
        r = check.Report(outcomes=[o], policy_source="head", invalid_contract=True)
        text = summary.markdown(r.to_json())
        self.assertIn("missing `/--` doc comments", text)

    def test_verdict_names_missing_required_guarantees(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", False, check.VERIFIED)
        text = summary.markdown(check.Report(outcomes=[o]).to_json())
        self.assertIn("the policy lists no required guarantees", text)

    def test_verdict_combines_reasons(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", True, check.ERROR)
        r = check.Report(outcomes=[o], policy_changes=["g added"], invalid_contract=True)
        text = summary.markdown(r.to_json())
        self.assertIn("waits for maintainer approval; the approved contract is missing", text)
        self.assertIn("1 of 1 required guarantees not verified", text)

    def test_verdict_names_an_unaccepted_downgrade(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", True, check.VERIFIED)
        r = check.Report(outcomes=[o], downgrades=[
            {"function": "transfer", "was": "proved", "now": "tested", "accepted": False, "reason": ""}])
        text = summary.markdown(r.to_json())
        self.assertIn("`transfer` was proved on the base branch and is not now", text)

    def test_verdict_notes_stale_accepts(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", True, check.VERIFIED)
        r = check.Report(outcomes=[o], stale_accepts=["oldFn"])
        text = summary.markdown(r.to_json())
        self.assertIn("`accept_downgrades` lists `oldFn`, not a downgrade here", text)

    def test_summary_shows_the_claim_it_replaces(self):
        o = check.Outcome("t", "g", "m::f", "fee_capped", True, check.VERIFIED)
        o.claim = "The fee never exceeds the new cap."
        o.previous_claim = "The fee never exceeds the cap."
        text = summary.markdown(check.Report(outcomes=[o], policy_source="head").to_json())
        self.assertIn("before this change it claimed: The fee never exceeds the cap.", text)


if __name__ == "__main__":
    unittest.main()
