"""End-to-end scenarios against the real pinned toolchain.

Each scenario copies examples/ledger as the protected base, mutates a copy as
the candidate the way an agent might, runs `proofci check`, and asserts the
status of every guarantee. Run inside the toolchain image:

    PROOFCI_TOOLCHAIN=1 python3 -m unittest tests.test_scenarios -v
"""

import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXAMPLE = ROOT / "examples" / "ledger"
GUARANTEES = ("fees/fee-capped", "fees/zero-amount", "transfer/conservation", "transfer/rejects-overdraft")
V, U, X, S = "verified", "unproven", "unsupported", "contract-stale"


def edit(path, old, new):
    text = path.read_text()
    if old not in text:
        raise AssertionError(f"{old!r} not in {path}")
    path.write_text(text.replace(old, new, 1))


def buggy_fee_rounds_up(head):
    edit(head / "src/lib.rs", "amount % BPS_DENOMINATOR * bps / BPS_DENOMINATOR\n",
         "(amount % BPS_DENOMINATOR * bps + BPS_DENOMINATOR - 1) / BPS_DENOMINATOR + 1\n")


def transfer_can_overflow(head):
    edit(head / "src/lib.rs", "    if accounts.to > u64::MAX - amount {\n        return None;\n    }\n", "")


def proof_uses_sorry(head):
    proofs = head / "proofci/Proofs.lean"
    text = proofs.read_text()
    start = text.index("theorem transfer_conserves")
    end = text.index("theorem transfer_rejects_overdraft")
    statement = text[start:text.index(":= by", start)]
    proofs.write_text(text[:start] + statement + ":= by\n  sorry\n\n" + text[end:])


def proof_weakens_statement(head):
    proofs = head / "proofci/Proofs.lean"
    text = proofs.read_text()
    start = text.index("theorem transfer_rejects_overdraft")
    proofs.write_text(text[:start] + "theorem transfer_rejects_overdraft (a : Accounts) (amount : Std.U64)\n"
                      "    (h : a.from.val < amount.val) : True := by trivial\n")


def proof_fakes_the_model(head):
    # The proofs ignore the extracted code and define a convenient model.
    proofs = head / "proofci/Proofs.lean"
    proofs.write_text(
        "import Aeneas\nopen Aeneas Aeneas.Std Result\n"
        "namespace ledger\n"
        "def calculate_fee (amount fee_bps : Std.U64) : Result Std.U64 := ok 0#u64\n"
        "end ledger\nopen ledger\n"
        "theorem fee_capped (amount fee_bps : Std.U64) :\n"
        "    calculate_fee amount fee_bps ⦃ fee => fee.val ≤ amount.val ⦄ := by\n"
        "  simp [calculate_fee]\n")


def committed_fake_translation(head):
    # A committed Lean translation is ignored; ProofCI regenerates it.
    (head / "proofci/Ledger.lean").write_text("-- not the real model\n")


def weaken_policy(head):
    edit(head / "proofci.yaml", "      - id: rejects-overdraft\n        theorem: transfer_rejects_overdraft\n", "")
    edit(head / "proofci/Contract.lean", "fee.val ≤ amount.val ⦄ := by sorry", "True ⦄ := by sorry")


def contract_signature_change(head):
    edit(head / "src/lib.rs", "pub fn calculate_fee(amount: u64, fee_bps: u64) -> u64 {",
         "pub fn calculate_fee(amount: u64, fee_bps: u32) -> u64 {\n    let fee_bps = fee_bps as u64;")


def unsafe_code(head):
    edit(head / "src/lib.rs", "pub struct Accounts", "pub fn peek(x: &u64) -> u64 { unsafe { *(x as *const u64) } }\n\npub struct Accounts")


def adds_dependency(head):
    edit(head / "Cargo.toml", "[dependencies]\n", "[dependencies]\nserde = \"1\"\n")


SCENARIOS = {
    "baseline": (None, dict.fromkeys(GUARANTEES, V), 0),
    "buggy-fee-rounds-up": (buggy_fee_rounds_up, {
        "fees/fee-capped": U, "fees/zero-amount": U, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "transfer-can-overflow": (transfer_can_overflow, {
        "fees/fee-capped": V, "fees/zero-amount": V, "transfer/conservation": U, "transfer/rejects-overdraft": V}, 1),
    "proof-uses-sorry": (proof_uses_sorry, {
        "fees/fee-capped": V, "fees/zero-amount": V, "transfer/conservation": U, "transfer/rejects-overdraft": V}, 1),
    "proof-weakens-statement": (proof_weakens_statement, {
        "fees/fee-capped": V, "fees/zero-amount": V, "transfer/conservation": V, "transfer/rejects-overdraft": U}, 1),
    "proof-fakes-the-model": (proof_fakes_the_model, dict.fromkeys(GUARANTEES, U), 1),
    "committed-fake-translation": (committed_fake_translation, dict.fromkeys(GUARANTEES, V), 0),
    "weaken-policy": (weaken_policy, dict.fromkeys(GUARANTEES, V), 1),
    "contract-signature-change": (contract_signature_change, {
        "fees/fee-capped": S, "fees/zero-amount": S, "transfer/conservation": S, "transfer/rejects-overdraft": S}, 1),
    "unsafe-code": (unsafe_code, dict.fromkeys(GUARANTEES, X), 1),
    "adds-dependency": (adds_dependency, dict.fromkeys(GUARANTEES, X), 1),
}


@unittest.skipUnless(os.environ.get("PROOFCI_TOOLCHAIN"), "needs the ProofCI toolchain image")
class Scenarios(unittest.TestCase):
    results = {}

    def run_scenario(self, name):
        mutate, expected, expected_exit = SCENARIOS[name]
        with tempfile.TemporaryDirectory() as tmp:
            base, head = Path(tmp) / "base", Path(tmp) / "head"
            shutil.copytree(EXAMPLE, base)
            shutil.copytree(EXAMPLE, head)
            if mutate:
                mutate(head)
            report = Path(tmp) / "report.json"
            done = subprocess.run(
                [sys.executable, "-m", "proofci", "check", "--base", base, "--head", head, "--report", report],
                cwd=ROOT, capture_output=True, text=True, timeout=3600)
            self.assertTrue(report.exists(), done.stdout + done.stderr)
            data = json.loads(report.read_text())
            statuses = {f"{g['target']}/{g['guarantee']}": g["status"] for g in data["guarantees"]}
            self.results[name] = {"exit": done.returncode, "statuses": statuses,
                                  "policy_changes": data["policy_changes"], "timings": data["timings_seconds"]}
            out_dir = os.environ.get("PROOFCI_SCENARIO_OUTPUT")
            if out_dir:
                Path(out_dir).mkdir(parents=True, exist_ok=True)
                shutil.copyfile(report, Path(out_dir) / f"{name}.json")
            self.assertEqual(statuses, expected, done.stdout)
            self.assertEqual(done.returncode, expected_exit, done.stdout)
            if name == "weaken-policy":
                self.assertTrue(data["policy_changes"])
            return data


def _make(name):
    def test(self):
        self.run_scenario(name)
    test.__name__ = "test_" + name.replace("-", "_")
    return test


for _name in SCENARIOS:
    setattr(Scenarios, "test_" + _name.replace("-", "_"), _make(_name))


if __name__ == "__main__":
    unittest.main()
