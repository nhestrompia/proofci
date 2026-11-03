import sys
import unittest
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from proofci import manifest  # noqa: E402
from proofci.check import lean_function, policy_changes  # noqa: E402

GOOD = b"""
version: 1
targets:
  - id: fees
    function: ledger::calculate_fee
    guarantees:
      - id: fee-capped
        theorem: fee_capped
      - id: advisory
        theorem: Ledger.advisory
        required: false
"""


class ManifestTests(unittest.TestCase):
    def test_defaults(self):
        m = manifest.parse(GOOD)
        self.assertEqual((m.crate, m.lean, m.contract, m.proofs),
                         (".", "proofci", "proofci/Contract.lean", "proofci/Proofs.lean"))
        self.assertEqual([(t.id, g.id, g.required) for t, g in m.guarantees()],
                         [("fees", "fee-capped", True), ("fees", "advisory", False)])

    def assertRejected(self, text, fragment):
        with self.assertRaises(manifest.ManifestError) as caught:
            manifest.parse(text)
        self.assertIn(fragment, str(caught.exception))

    def test_rejects_formulas_and_unknown_keys(self):
        self.assertRejected(GOOD.replace(b"theorem: fee_capped", b"ensure: result >= 0"), "unknown keys")
        self.assertRejected(GOOD + b"engine: lean4\n", "unknown keys")

    def test_rejects_duplicates_and_escapes(self):
        self.assertRejected(GOOD.replace(b"Ledger.advisory", b"fee_capped"), "used by two guarantees")
        self.assertRejected(GOOD.replace(b"id: advisory", b"id: fee-capped"), "duplicate guarantee")
        self.assertRejected(b"version: 1\nversion: 1\ntargets: []\n", "duplicate key")
        self.assertRejected(GOOD.replace(b"version: 1", b"version: 1\nlean: ../elsewhere"), "inside the repository")
        self.assertRejected(GOOD.replace(b"version: 1", b"version: 1\ncrate: /abs"), "inside the repository")

    def test_requires_a_required_guarantee(self):
        text = GOOD.replace(b"theorem: fee_capped", b"theorem: fee_capped\n        required: false")
        self.assertRejected(text, "at least one guarantee must be required")

    def test_rejects_bad_names(self):
        self.assertRejected(GOOD.replace(b"ledger::calculate_fee", b"calculate_fee"), "Rust path")
        self.assertRejected(GOOD.replace(b"fee_capped", b"fee capped; #eval"), "Lean declaration name")
        self.assertRejected(GOOD.replace(b"required: false", b"required: maybe"), "true or false")

    def test_policy_approvers(self):
        self.assertIsNone(manifest.parse(GOOD).approvers)
        m = manifest.parse(GOOD + b"policy:\n  approvers: [Alice, bob]\n")
        self.assertEqual(m.approvers, ("alice", "bob"))
        self.assertEqual(manifest.parse(GOOD + b"policy:\n  approvers: []\n").approvers, ())
        self.assertRejected(GOOD + b"policy:\n  approvers: alice\n", "GitHub logins")
        self.assertRejected(GOOD + b"policy:\n  owners: [alice]\n", "unknown keys")

    def test_lean_function_name(self):
        self.assertEqual(lean_function("ledger::Accounts::deposit"), "ledger.Accounts.deposit")


class PolicyChangeTests(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.tmp = tempfile.TemporaryDirectory()
        root = Path(self.tmp.name)
        self.base, self.head = root / "base", root / "head"
        for d in (self.base, self.head):
            (d / "proofci").mkdir(parents=True)
            (d / "proofci" / "Contract.lean").write_text("theorem fee_capped : True := sorry\n")

    def tearDown(self):
        self.tmp.cleanup()

    def changes(self, head_text, contract=None):
        if contract is not None:
            (self.head / "proofci" / "Contract.lean").write_text(contract)
        head = manifest.parse(head_text) if head_text is not None else None
        return policy_changes(self.base, manifest.parse(GOOD), self.head, head)

    def test_unchanged(self):
        self.assertEqual(self.changes(GOOD), [])

    def test_detects_weakening(self):
        removed = GOOD.replace(b"      - id: advisory\n        theorem: Ledger.advisory\n        required: false\n", b"")
        self.assertEqual(self.changes(removed), ["guarantee `fees/advisory` was removed"])
        optional = GOOD.replace(b"theorem: fee_capped", b"theorem: fee_capped\n        required: false")
        swapped = optional.replace(b"theorem: Ledger.advisory\n        required: false",
                                   b"theorem: Ledger.advisory\n        required: true")
        self.assertIn("guarantee `fees/fee-capped` was made optional", self.changes(swapped))
        self.assertEqual(self.changes(GOOD, contract="theorem fee_capped : True := trivial\n"),
                         ["the contract `proofci/Contract.lean` changed"])
        self.assertEqual(self.changes(None), ["proofci.yaml was removed or is invalid in the pull request"])
        self.assertIn("`policy.approvers` changed", self.changes(GOOD + b"policy:\n  approvers: [mallory]\n"))


if __name__ == "__main__":
    unittest.main()
