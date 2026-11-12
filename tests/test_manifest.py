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

    def test_typescript(self):
        data = GOOD.replace(b"version: 1", b"version: 1\nlanguage: typescript\npackage: packages/core")
        data = data.replace(b"ledger::calculate_fee", b"src/fees.ts::calculateFee")
        m = manifest.parse(data)
        self.assertEqual((m.language, m.crate), ("typescript", "packages/core"))
        self.assertEqual(m.summary()["language"], "typescript")
        for bad in (b"src/fees.js::f", b"../fees.ts::f", b"/etc/fees.ts::f", b"src/fees.ts", b"ledger::f"):
            with self.assertRaises(manifest.ManifestError):
                manifest.parse(data.replace(b"src/fees.ts::calculateFee", bad))

    def test_language_and_directory_key_must_match(self):
        with self.assertRaises(manifest.ManifestError):
            manifest.parse(GOOD.replace(b"version: 1", b"version: 1\npackage: ."))
        with self.assertRaises(manifest.ManifestError):
            manifest.parse(GOOD.replace(b"version: 1", b"version: 1\nlanguage: typescript\ncrate: ."))
        with self.assertRaises(manifest.ManifestError):
            manifest.parse(GOOD.replace(b"version: 1", b"version: 1\nlanguage: python"))

    def test_assumed_calls(self):
        base = b"""
version: 1
language: typescript
assumes:
  - call: "@acme/slug::slug"
    signature: "(a: string): string"
targets:
  - id: fees
    function: src/a.ts::f
    guarantees:
      - id: capped
        theorem: fee_capped
"""
        self.assertEqual(manifest.parse(base).assumes, (("@acme/slug::slug", "(a: string): string"),))
        self.assertEqual(manifest.parse(base.replace(b"@acme/slug::slug", b"lodash::kebabCase")).assumes[0][0], "lodash::kebabCase")
        for wrong in (b"call: nothing", b'call: "a::1b"'):
            with self.assertRaises(manifest.ManifestError):
                manifest.parse(base.replace(b'call: "@acme/slug::slug"', wrong))
        with self.assertRaises(manifest.ManifestError):
            manifest.parse(base.replace(b'signature: "(a: string): string"', b'signature: ""'))
        with self.assertRaises(manifest.ManifestError):
            manifest.parse(base.replace(b"language: typescript\n", b"").replace(b"src/a.ts::f", b"ledger::f"))

    EFFECTS = b"""
version: 1
language: typescript
effects:
  - id: getLink
    call: src/queries/link.ts::getLink
    signature: "(linkId: string): Promise<Link | null>"
    kind: read
  - id: saveLink
    call: "@acme/db::saveLink"
    signature: "(link: Link): Promise<void>"
    kind: write
  - id: findDevice
    method: "DeviceModel#findWorkspaceDeviceById"
    signature: "(id: string): Promise<DeviceRow | undefined>"
    kind: read
  - id: fetchTranscript
    param: deps.fetchTranscript
    signature: "(): Promise<Message[] | null>"
    kind: read
targets:
  - id: can-view
    function: src/permissions/link.ts::canViewLink
    guarantees:
      - id: anonymous
        theorem: canViewLink_anonymous
"""

    def test_effects(self):
        m = manifest.parse(self.EFFECTS)
        self.assertEqual([(e.id, e.form, e.target, e.kind) for e in m.effects], [
            ("fetchTranscript", "param", "deps.fetchTranscript", "read"),
            ("findDevice", "method", "DeviceModel#findWorkspaceDeviceById", "read"),
            ("getLink", "call", "src/queries/link.ts::getLink", "read"),
            ("saveLink", "call", "@acme/db::saveLink", "write")])
        self.assertEqual(m.effects[2].entry(), {"id": "getLink", "call": "src/queries/link.ts::getLink",
                                                "signature": "(linkId: string): Promise<Link | null>", "kind": "read"})

    def test_an_effect_can_narrow_any(self):
        narrowed = self.EFFECTS.replace(b'signature: "(linkId: string): Promise<Link | null>"',
                                        b'signature: "(linkId: string): Promise<any>"\n    narrowed: "(linkId: string): Promise<Link | null>"')
        m = manifest.parse(narrowed)
        self.assertEqual(m.effects[2].narrowed, "(linkId: string): Promise<Link | null>")
        self.assertEqual(m.effects[2].entry()["narrowed"], "(linkId: string): Promise<Link | null>")
        self.assertEqual(m.effects[3].narrowed, "")
        self.assertNotIn("narrowed", m.effects[3].entry())
        self.assertRejected(narrowed.replace(b'narrowed: "(linkId: string): Promise<Link | null>"', b'narrowed: "Link"'), "narrowed must be a TypeScript signature")
        # The narrowing is part of the policy a pull request can't change for itself.
        self.assertNotEqual(manifest.parse(narrowed).effects, manifest.parse(self.EFFECTS).effects)

    def test_effects_are_strict(self):
        cases = [
            (b"kind: write", b"kind: maybe", "must be one of: read, write"),
            (b'signature: "(link: Link): Promise<void>"', b'signature: "(link: Link): void"', "written `Promise<T>`"),
            (b'signature: "(link: Link): Promise<void>"', b'signature: ""', "written `Promise<T>`"),
            (b"id: saveLink", b"id: getLink", "duplicate effect id"),
            (b"id: saveLink", b"id: Save-Link", "must match"),
            (b'call: "@acme/db::saveLink"', b"call: src/queries/link.ts::getLink", "listed as an effect twice"),
            (b'call: "@acme/db::saveLink"', b"call: nothing", "must look like"),
            (b'method: "DeviceModel#findWorkspaceDeviceById"', b'method: "findWorkspaceDeviceById"', "must look like `Class#method`"),
            (b"param: deps.fetchTranscript", b"param: fetchTranscript", "must look like `parameter.field`"),
            (b"param: deps.fetchTranscript", b"param: deps.fetchTranscript\n    call: a::b", "exactly one of"),
            (b"    kind: write\n", b"    kind: write\n    exclusive: [store]\n", "unknown keys"),
        ]
        for old, new, fragment in cases:
            with self.subTest(fragment=fragment, old=old):
                self.assertRejected(self.EFFECTS.replace(old, new), fragment)
        self.assertRejected(self.EFFECTS.replace(b"language: typescript\n", b"").replace(
            b"src/permissions/link.ts::canViewLink", b"ledger::f"), "only available for TypeScript")
        self.assertRejected(self.EFFECTS.replace(b"    kind: write\n", b""), "is missing: kind")

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

    def test_effects_and_assumptions_are_protected(self):
        base = ManifestTests.EFFECTS
        original = self.base_manifest(base)
        same = self.compare(original, base)
        self.assertEqual(same, [])
        removed = base.replace(b"""  - id: saveLink
    call: "@acme/db::saveLink"
    signature: "(link: Link): Promise<void>"
    kind: write
""", b"")
        self.assertEqual(self.compare(original, removed), ["effect `saveLink` was removed"])
        added = base.replace(b"targets:", b"""  - id: audit
    call: "@acme/audit::record"
    signature: "(event: string): Promise<void>"
    kind: write
targets:""")
        self.assertEqual(self.compare(original, added), ["effect `audit` was added"])
        # Looser or different: a changed signature or kind is a different claim.
        self.assertEqual(self.compare(original, base.replace(b"Promise<Link | null>", b"Promise<Link | undefined>")),
                         ["effect `getLink` changed"])
        self.assertEqual(self.compare(original, base.replace(b"kind: write", b"kind: read")), ["effect `saveLink` changed"])
        self.assertEqual(self.compare(original, base.replace(b"call: src/queries/link.ts::getLink", b"call: src/queries/other.ts::getLink")),
                         ["effect `getLink` changed"])
        assumed = base.replace(b"effects:", b'assumes:\n  - call: slug::slug\n    signature: "(a: string): string"\neffects:')
        self.assertEqual(self.compare(original, assumed), ["the call `slug::slug` was assumed"])
        self.assertEqual(self.compare(self.base_manifest(assumed), base), ["the assumed call `slug::slug` was removed"])
        self.assertEqual(self.compare(self.base_manifest(assumed), assumed.replace(b"(a: string): string", b"(a: number): string")),
                         ["the assumed call `slug::slug` changed its signature"])

    def base_manifest(self, text):
        return manifest.parse(text)

    def compare(self, base, head_text):
        from proofci.check import policy_changes as pc
        return pc(self.base, base, self.head, manifest.parse(head_text))

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
