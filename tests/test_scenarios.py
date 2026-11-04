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
TS_EXAMPLE = ROOT / "examples" / "ts-bank"
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
    # Only code the targets reach is translated; `unsafe` elsewhere is fine.
    edit(head / "src/lib.rs", "pub struct Accounts", "pub fn peek(x: &u64) -> u64 { unsafe { *(x as *const u64) } }\n\npub struct Accounts")


def target_reaches_unsafe(head):
    # `transfer` now reads through a raw pointer, which Aeneas cannot model;
    # the fee guarantees are still judged.
    edit(head / "src/lib.rs", "pub struct Accounts",
         "fn peek(x: &u64) -> u64 { unsafe { *(x as *const u64) } }\n\npub struct Accounts")
    edit(head / "src/lib.rs", "    if amount > accounts.from {", "    if amount > peek(&accounts.from) {")


def adds_dependency(head):
    edit(head / "Cargo.toml", "[dependencies]\n", "[dependencies]\nserde = \"1\"\n")


def _replace_proof(head, theorem, replacement):
    """Replace the declaration of `theorem` in Proofs.lean with `replacement`."""
    proofs = head / "proofci/Proofs.lean"
    text = proofs.read_text()
    start = text.index(f"theorem {theorem}")
    nxt = text.find("\ntheorem ", start + 1)
    proofs.write_text(text[:start] + replacement + ("\n" + text[nxt + 1:] if nxt != -1 else "\n"))


FEE_CAPPED = ("theorem fee_capped (amount fee_bps : Std.U64) :\n"
              "    calculate_fee amount fee_bps ⦃ fee => fee.val ≤ amount.val ⦄ := ")


def proof_adds_axiom(head):
    _replace_proof(head, "fee_capped", "axiom cheat : False\n\n" + FEE_CAPPED + "cheat.elim\n")


def proof_uses_native_decide(head):
    # native_decide trusts compiled code through the Lean.ofReduceBool axiom;
    # the otherwise valid proof now depends on it.
    proofs = head / "proofci/Proofs.lean"
    text = proofs.read_text()
    text = text.replace(FEE_CAPPED + "by\n",
                        "theorem big : 2 ^ 20 % 7 = 4 := by native_decide\n\n" + FEE_CAPPED + "by\n  have := big\n", 1)
    assert "native_decide" in text
    proofs.write_text(text)


def proof_bypasses_kernel(head):
    # Add a proof of False without kernel checking, then use it.
    _replace_proof(head, "fee_capped",
                   "open Lean in\nrun_cmd Lean.Elab.Command.liftCoreM do\n"
                   "  let decl : Declaration := .thmDecl ⟨⟨`bogus, [], mkConst ``False⟩, mkConst ``Nat.zero, [`bogus]⟩\n"
                   "  withOptions (fun o => o.setBool `debug.skipKernelTC true) (addDecl decl)\n\n"
                   + FEE_CAPPED + "(bogus).elim\n")


def proof_reuses_contract(head):
    # Importing the contract would let a proof cite the `sorry`ed statement.
    proofs = head / "proofci/Proofs.lean"
    text = proofs.read_text().replace("import Ledger\n", "import Ledger\nimport Contract\n", 1)
    proofs.write_text(text)
    _replace_proof(head, "fee_capped", "theorem fee_capped' (amount fee_bps : Std.U64) :\n"
                   "    calculate_fee amount fee_bps ⦃ fee => fee.val ≤ amount.val ⦄ := fee_capped amount fee_bps\n")


TAMPER = r"""
-- While the proofs build, recompile the contract with a weaker statement into
-- the build directory, then prove the weaker statement.
#eval show IO Unit from do
  IO.FS.writeFile ".lake/Contract.lean" "import Ledger\nopen Aeneas Aeneas.Std Result ledger\ntheorem fee_capped (amount fee_bps : Std.U64) : True := by sorry\n"
  let r ← IO.Process.output { cmd := "lean", args := #["--root=.lake", "-o", ".lake/build/lib/lean/Contract.olean", ".lake/Contract.lean"] }
  if r.exitCode != 0 then throw (IO.userError r.stderr)

theorem fee_capped (amount fee_bps : Std.U64) : True := trivial
"""


def proof_tampers_with_build(head):
    _replace_proof(head, "fee_capped", TAMPER)


def proof_writes_sources(head):
    # Elaboration-time code cannot change the contract or the extracted model.
    _replace_proof(head, "fee_capped",
                   "#eval show IO Unit from do\n"
                   "  IO.FS.writeFile \"Contract.lean\" \"import Ledger\\ntheorem fee_capped : True := trivial\\n\"\n"
                   "  IO.FS.writeFile \"Ledger.lean\" \"\"\n\n"
                   "theorem fee_capped : True := trivial\n")


def proof_import_broken(head):
    edit(head / "proofci/Proofs.lean", "import Ledger\n", "import Ledger\nimport Proofs.Missing\n")


def function_renamed(head):
    edit(head / "src/lib.rs", "pub fn calculate_fee(", "pub fn compute_fee(")


def calls_unmodelled_std(head):
    # Aeneas has no model for this standard library function.
    edit(head / "src/lib.rs", "    let bps = if fee_bps",
         "    let _ = amount.reverse_bits();\n    let bps = if fee_bps")


def as_workspace(checkout):
    """Turn the example into a Cargo workspace: the ledger becomes a member
    with inherited settings, next to a service whose dependencies are not
    available (and not needed: unrelated members are left out)."""
    member = checkout / "ledger"
    member.mkdir()
    shutil.move(checkout / "src", member / "src")
    (checkout / "Cargo.toml").unlink()
    (member / "Cargo.toml").write_text(
        '[package]\nname = "ledger"\nversion.workspace = true\nedition.workspace = true\n\n'
        '[dev-dependencies]\nproptest = "1"\n')
    app = checkout / "services" / "app"
    (app / "src").mkdir(parents=True)
    (app / "Cargo.toml").write_text(
        '[package]\nname = "app"\nversion.workspace = true\nedition.workspace = true\n\n'
        '[dependencies]\ntokio.workspace = true\nledger = { path = "../../ledger" }\n')
    (app / "src" / "main.rs").write_text("fn main() {}\n")
    (checkout / "Cargo.toml").write_text(
        '[workspace]\nresolver = "2"\nmembers = ["ledger", "services/app"]\n\n'
        '[workspace.package]\nversion = "0.1.0"\nedition = "2021"\n\n'
        '[workspace.dependencies]\ntokio = { version = "1", features = ["full"] }\n')
    edit(checkout / "proofci.yaml", "crate: .", "crate: ledger")


def workspace_member(head):
    as_workspace(head)


workspace_member.also_base = as_workspace

FAKE_CHECKSUM = "ab" * 32
MALICIOUS_BUILD_RS = r"""
// Tries to replace the buggy fee in the crate being verified with a correct
// one before ProofCI translates it, so that the bug would pass.
use std::{fs, path::Path};
fn visit(dir: &Path, depth: u32) {
    if depth > 8 { return; }
    let Ok(entries) = fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() { visit(&path, depth + 1); continue; }
        if path.file_name().map_or(false, |n| n == "lib.rs") {
            if let Ok(text) = fs::read_to_string(&path) {
                if text.contains("+ BPS_DENOMINATOR - 1) / BPS_DENOMINATOR + 1") {
                    let fixed = text.replace("(amount % BPS_DENOMINATOR * bps + BPS_DENOMINATOR - 1) / BPS_DENOMINATOR + 1",
                                             "amount % BPS_DENOMINATOR * bps / BPS_DENOMINATOR");
                    let result = fs::write(&path, fixed);
                    println!("cargo:warning=rewrite {}: {:?}", path.display(), result);
                }
            }
        }
    }
}
fn main() { visit(Path::new("/tmp"), 0); }
"""


def dependency_rewrites_source(head):
    """A crates.io dependency (served from a local vendor directory) whose
    build script rewrites the buggy code into correct code before translation."""
    buggy_fee_rounds_up(head)
    edit(head / "Cargo.toml", "[dependencies]\n", '[dependencies]\ntinydep = "0.1.0"\n')
    (head / "Cargo.lock").write_text(
        "version = 4\n\n[[package]]\nname = \"ledger\"\nversion = \"0.1.0\"\ndependencies = [\n \"tinydep\",\n]\n\n"
        "[[package]]\nname = \"tinydep\"\nversion = \"0.1.0\"\n"
        "source = \"registry+https://github.com/rust-lang/crates.io-index\"\n"
        f"checksum = \"{FAKE_CHECKSUM}\"\n")
    dep = head.parent / "vendor" / "tinydep-0.1.0"
    (dep / "src").mkdir(parents=True)
    (dep / "Cargo.toml").write_text('[package]\nname = "tinydep"\nversion = "0.1.0"\nedition = "2021"\nbuild = "build.rs"\n')
    (dep / "src" / "lib.rs").write_text("pub fn unused() {}\n")
    (dep / "build.rs").write_text(MALICIOUS_BUILD_RS)
    (dep / ".cargo-checksum.json").write_text(json.dumps({"files": {}, "package": FAKE_CHECKSUM}))


ZERO_CONTRACT = ("theorem zero_amount_no_fee (fee_bps : Std.U64) :\n"
                 "    calculate_fee 0#u64 fee_bps ⦃ fee => fee.val = 0 ⦄ := by sorry")


def contract_only_assumes(checkout):
    # The function appears only in a hypothesis: the statement constrains nothing.
    edit(checkout / "proofci/Contract.lean", ZERO_CONTRACT,
         "theorem zero_amount_no_fee (fee_bps : Std.U64) (h : calculate_fee 0#u64 fee_bps = ok 0#u64) :\n"
         "    True := by sorry")


def contract_assumes_result(checkout):
    # The claim is smuggled in as a hypothesis; ProofCI warns.
    edit(checkout / "proofci/Contract.lean", ZERO_CONTRACT,
         "theorem zero_amount_no_fee (fee_bps : Std.U64) (h : calculate_fee 0#u64 fee_bps = ok 0#u64) :\n"
         "    calculate_fee 0#u64 fee_bps ⦃ fee => fee.val = 0 ⦄ := by sorry")


def weak_contract_only_assumes(head):
    contract_only_assumes(head)


weak_contract_only_assumes.also_base = contract_only_assumes


def weak_contract_assumes_result(head):
    contract_assumes_result(head)


weak_contract_assumes_result.also_base = contract_assumes_result


def no_panic_contract(checkout):
    # "never panics or overflows": a meaningful guarantee, no warning expected.
    edit(checkout / "proofci/Contract.lean", ZERO_CONTRACT,
         "theorem zero_amount_no_fee (fee_bps : Std.U64) :\n"
         "    calculate_fee 0#u64 fee_bps ⦃ _ => True ⦄ := by sorry")
    edit(checkout / "proofci/Proofs.lean", "theorem zero_amount_no_fee (fee_bps : Std.U64) :\n"
         "    calculate_fee 0#u64 fee_bps ⦃ fee => fee.val = 0 ⦄ := by",
         "theorem zero_amount_no_fee (fee_bps : Std.U64) :\n"
         "    calculate_fee 0#u64 fee_bps ⦃ _ => True ⦄ := by")


def contract_no_panic(head):
    no_panic_contract(head)


contract_no_panic.also_base = no_panic_contract


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
    "unsafe-code": (unsafe_code, dict.fromkeys(GUARANTEES, V), 0),
    "target-reaches-unsafe": (target_reaches_unsafe, {
        "fees/fee-capped": V, "fees/zero-amount": V, "transfer/conservation": X, "transfer/rejects-overdraft": X}, 1),
    "adds-dependency": (adds_dependency, dict.fromkeys(GUARANTEES, X), 1),
    "proof-adds-axiom": (proof_adds_axiom, {
        "fees/fee-capped": U, "fees/zero-amount": V, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "proof-uses-native-decide": (proof_uses_native_decide, {
        "fees/fee-capped": U, "fees/zero-amount": V, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "proof-bypasses-kernel": (proof_bypasses_kernel, {
        "fees/fee-capped": U, "fees/zero-amount": V, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    # Importing the contract makes every restated theorem a duplicate.
    "proof-reuses-contract": (proof_reuses_contract, dict.fromkeys(GUARANTEES, U), 1),
    "proof-tampers-with-build": (proof_tampers_with_build, {
        "fees/fee-capped": U, "fees/zero-amount": V, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "proof-writes-sources": (proof_writes_sources, {
        "fees/fee-capped": U, "fees/zero-amount": V, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "proof-import-broken": (proof_import_broken, dict.fromkeys(GUARANTEES, U), 1),
    "function-renamed": (function_renamed, {
        "fees/fee-capped": S, "fees/zero-amount": S, "transfer/conservation": S, "transfer/rejects-overdraft": S}, 1),
    "calls-unmodelled-std": (calls_unmodelled_std, {
        "fees/fee-capped": X, "fees/zero-amount": X, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "workspace-member": (workspace_member, dict.fromkeys(GUARANTEES, V), 0),
    "dependency-rewrites-source": (dependency_rewrites_source, {
        "fees/fee-capped": U, "fees/zero-amount": U, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "contract-only-assumes": (weak_contract_only_assumes, {
        "fees/fee-capped": V, "fees/zero-amount": S, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "contract-assumes-result": (weak_contract_assumes_result, {
        "fees/fee-capped": V, "fees/zero-amount": U, "transfer/conservation": V, "transfer/rejects-overdraft": V}, 1),
    "contract-no-panic": (contract_no_panic, dict.fromkeys(GUARANTEES, V), 0),
}


def run_scenario(name, out_dir=None):
    """Run one scenario. Returns a list of mismatches (empty when it passed)."""
    mutate, expected, expected_exit = SCENARIOS[name]
    example = TS_EXAMPLE if name.startswith("ts-") else EXAMPLE
    with tempfile.TemporaryDirectory() as tmp:
        base, head = Path(tmp) / "base", Path(tmp) / "head"
        shutil.copytree(example, base)
        shutil.copytree(example, head)
        if mutate:
            mutate(head)
            if hasattr(mutate, "also_base"):
                mutate.also_base(base)
        report = Path(tmp) / "report.json"
        vendor = Path(tmp) / "vendor"
        done = subprocess.run(
            [sys.executable, "-m", "proofci", "check", "--base", base, "--head", head, "--report", report,
             *(["--vendor", vendor] if vendor.is_dir() else [])],
            cwd=ROOT, capture_output=True, text=True, timeout=3600)
        if not report.exists():
            return [f"no report:\n{done.stdout}{done.stderr}"]
        data = json.loads(report.read_text())
        if out_dir:
            Path(out_dir).mkdir(parents=True, exist_ok=True)
            shutil.copyfile(report, Path(out_dir) / f"{name}.json")
    statuses = {f"{g['target']}/{g['guarantee']}": g["status"] for g in data["guarantees"]}
    problems = []
    if statuses != expected:
        problems.append(f"statuses {statuses} != expected {expected}")
    if done.returncode != expected_exit:
        problems.append(f"exit {done.returncode} != expected {expected_exit}")
    wanted = TS_REASONS.get(name)
    if wanted and not any(wanted in g["reason"] for g in data["guarantees"]):
        problems.append(f"no guarantee was rejected for the expected reason: {wanted!r}")
    if name == "weaken-policy" and not data["policy_changes"]:
        problems.append("policy change not reported")
    if name == "contract-no-panic" and any(g.get("warnings") for g in data["guarantees"]):
        problems.append("a no-panic guarantee was warned about")
    if name == "contract-assumes-result":
        warned = {f"{g['target']}/{g['guarantee']}" for g in data["guarantees"] if g.get("warnings")}
        if warned != {"fees/zero-amount"}:
            problems.append(f"expected a contract warning on fees/zero-amount only, got {warned}")
    if problems:
        problems.append(done.stdout[-4000:])
    return problems


TS_LEDGER = "src/ledger.ts"
TS_GUARANTEES = ("fees/capped", "transfer/conservation", "transfer/rejects-overdraft")
TS_FEE, TS_CONSERVES, TS_OVERDRAFT = TS_GUARANTEES


def ts_results():
    return dict.fromkeys(TS_GUARANTEES, V)


def ts_transfer_loses_money(head):
    edit(head / TS_LEDGER, "to: accounts.to + amount", "to: accounts.to + amount - 1")


def ts_fee_cap_raised(head):
    edit(head / TS_LEDGER, "const MAX_FEE = 500;", "const MAX_FEE = 5000;")


def ts_overdraft_check_removed(head):
    edit(head / TS_LEDGER, "amount <= 0 || amount > accounts.from", "amount <= 0")


def ts_fractional_fee(head):
    edit(head / TS_LEDGER, "Math.floor(amount * rateBps / BASIS_POINTS)", "Math.floor(amount * 0.02)")


def ts_cast_hides_a_type(head):
    edit(head / TS_LEDGER, "amount <= 0 ||", "(amount as any) <= 0 ||")


def ts_javascript_beside_source(head):
    (head / "src/ledger.js").write_text("export const transfer = () => null;\n")


def ts_compiler_error_silenced(head):
    edit(head / TS_LEDGER, "const MAX_FEE = 500;", "// @ts-ignore\nconst MAX_FEE: string = 500;")


def ts_compiler_error(head):
    edit(head / TS_LEDGER, "return Math.min(", "const broken: string = 1;\n  return Math.min(")


def ts_tsconfig_relaxes_checks(head):
    (head / "tsconfig.json").write_text('{"compilerOptions": {"strict": false}}\n')
    edit(head / TS_LEDGER, "amount: number): Accounts | null", "amount): Accounts | null")


def ts_module_patches_math(head):
    edit(head / TS_LEDGER, "const MAX_FEE = 500;", "const MAX_FEE = 500;\nMath.floor = (x) => x + 1;")


def ts_import_for_side_effects(head):
    (head / "src/patch.ts").write_text("Math.floor = (x: number) => x + 1;\nexport {};\n")
    edit(head / TS_LEDGER, "export interface Accounts", 'import "./patch.ts";\n\nexport interface Accounts')


def ts_declaration_file_lies(head):
    (head / "src/helper.d.ts").write_text("export function always(a: number): number;\n")
    edit(head / TS_LEDGER, "export interface Accounts", 'import { always } from "./helper";\n\nexport interface Accounts')
    edit(head / TS_LEDGER, "from: accounts.from - amount", "from: always(accounts.from - amount)")


def ts_proof_uses_sorry(head):
    proofs = head / "proofci/Proofs.lean"
    edit(proofs, "  unfold transfer\n  step*\n", "  sorry\n")


def ts_function_removed(head):
    edit(head / TS_LEDGER, "export function transfer(", "export function move(")


def ts_contract_weakened(head):
    edit(head / "proofci/Contract.lean", "fee.val ≤ 500", "fee.val ≤ 5000")


SCENARIOS.update({
    "ts-baseline": (None, ts_results(), 0),
    "ts-transfer-loses-money": (ts_transfer_loses_money, {**ts_results(), TS_CONSERVES: U}, 1),
    "ts-fee-cap-raised": (ts_fee_cap_raised, {**ts_results(), TS_FEE: U}, 1),
    "ts-overdraft-check-removed": (ts_overdraft_check_removed, {**ts_results(), TS_CONSERVES: U, TS_OVERDRAFT: U}, 1),
    "ts-fractional-fee": (ts_fractional_fee, {**ts_results(), TS_FEE: X}, 1),
    "ts-cast-hides-a-type": (ts_cast_hides_a_type, {**ts_results(), TS_CONSERVES: X, TS_OVERDRAFT: X}, 1),
    "ts-javascript-beside-source": (ts_javascript_beside_source, dict.fromkeys(TS_GUARANTEES, X), 1),
    "ts-compiler-error-silenced": (ts_compiler_error_silenced, dict.fromkeys(TS_GUARANTEES, X), 1),
    "ts-compiler-error": (ts_compiler_error, dict.fromkeys(TS_GUARANTEES, X), 1),
    "ts-tsconfig-relaxes-checks": (ts_tsconfig_relaxes_checks, dict.fromkeys(TS_GUARANTEES, X), 1),
    "ts-module-patches-math": (ts_module_patches_math, dict.fromkeys(TS_GUARANTEES, X), 1),
    "ts-import-for-side-effects": (ts_import_for_side_effects, dict.fromkeys(TS_GUARANTEES, X), 1),
    "ts-declaration-file-lies": (ts_declaration_file_lies, {**ts_results(), TS_CONSERVES: X, TS_OVERDRAFT: X}, 1),
    "ts-proof-uses-sorry": (ts_proof_uses_sorry, {**ts_results(), TS_CONSERVES: U}, 1),
    "ts-function-removed": (ts_function_removed, {TS_FEE: S, TS_CONSERVES: X, TS_OVERDRAFT: X}, 1),
    "ts-contract-weakened": (ts_contract_weakened, ts_results(), 1),
})


# A crash in the translator also reports `unsupported`, so these check the cause.
TS_REASONS = {
    "ts-fractional-fee": "not a safe integer",
    "ts-cast-hides-a-type": "type assertions",
    "ts-javascript-beside-source": "sits beside",
    "ts-compiler-error-silenced": "@ts-",
    "ts-compiler-error": "TypeScript error",
    "ts-tsconfig-relaxes-checks": "TypeScript error",
    "ts-module-patches-math": "on import",
    "ts-import-for-side-effects": "side effects",
    "ts-declaration-file-lies": "no source",
    "ts-function-removed": "not a top-level function",
}


@unittest.skipUnless(os.environ.get("PROOFCI_TOOLCHAIN"), "needs the ProofCI toolchain image")
class Scenarios(unittest.TestCase):
    pass


def _make(name):
    def test(self):
        problems = run_scenario(name, os.environ.get("PROOFCI_SCENARIO_OUTPUT"))
        self.assertFalse(problems, "\n".join(problems))
    test.__name__ = "test_" + name.replace("-", "_")
    return test


for _name in SCENARIOS:
    setattr(Scenarios, "test_" + _name.replace("-", "_"), _make(_name))


def main(argv=None):
    """Run scenarios in parallel (see tests/run_scenarios.py)."""
    import argparse
    import time
    from concurrent.futures import ThreadPoolExecutor
    parser = argparse.ArgumentParser()
    parser.add_argument("--shard", default="1/1", help="run the i-th of n interleaved shards")
    parser.add_argument("--jobs", type=int, default=os.cpu_count() or 2)
    parser.add_argument("--output", default=os.environ.get("PROOFCI_SCENARIO_OUTPUT"))
    parser.add_argument("names", nargs="*")
    args = parser.parse_args(argv)
    index, count = map(int, args.shard.split("/"))
    names = args.names or list(SCENARIOS)
    names = names[index - 1::count]

    def one(name):
        started = time.monotonic()
        return name, run_scenario(name, args.output), time.monotonic() - started

    failed = 0
    with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
        for name, problems, seconds in pool.map(one, names):
            print(f"{'ok  ' if not problems else 'FAIL'} {name} ({seconds:.0f}s)", flush=True)
            if problems:
                failed += 1
                print("\n".join("     " + line for line in "\n".join(problems).splitlines()), flush=True)
    print(f"{len(names) - failed}/{len(names)} scenarios passed")
    return 1 if failed else 0


if __name__ == "__main__":
    unittest.main()
