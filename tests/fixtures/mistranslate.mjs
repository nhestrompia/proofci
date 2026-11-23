// A TEST HOOK, used only by tests/test_scenarios.py through PROOFCI_TRANSLATOR.
//
// It runs the real translator and then edits the Lean that came out, the way a translator bug
// would. Nothing in ProofCI itself can do this: there is no setting that edits a view. Which edit
// to make is chosen by the name this file is run under (see the two wrappers beside it).
import { spawnSync } from "node:child_process";
import { existsSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const EDITS = {
  // Differs from the code only for amount = 4242, which no sample of inputs is likely to hit.
  rare: [["(amount.val ≤ 0) ∨ (amount.val > accounts.«from».val)", "(amount.val ≤ 0) ∨ (amount.val > accounts.«from».val) ∨ (amount.val = 4242)"]],
  // Differs for every input that moves money.
  common: [["let tmp2 ← Js.add accounts.«to» amount", "let tmp2 ← Js.sub accounts.«to» amount"]],
  // A recursive function that subtracts each item after the first instead of adding it.
  recursive: [["let tmp2 ← Js.add list_1.value tmp1", "let tmp2 ← Js.sub list_1.value tmp1"]],
  // The same, only for an item of 4242.
  recursive_rare: [["let tmp2 ← Js.add list_1.value tmp1", "let tmp2 ← if list_1.value.val = 4242 then Js.sub list_1.value tmp1 else Js.add list_1.value tmp1"]],
  // Binary64: multiplies where the code divides — wrong for most inputs, so Node sees it.
  dbl_common: [["let tmp1 ← Js.Dbl.mul price quantity", "let tmp1 ← Js.Dbl.div price quantity"]],
  // Binary64: floors instead of rounding only for the exact amount the menu example hits
  // (2805.84 cents) — a value no sample is likely to hit, so the bridge is what must catch it.
  dbl_rare: [["let tmp9 ← Js.Dbl.math Core.F64.jsround tmp8",
    "let tmp9 ← if tmp8.f = Core.F64.ofBits 0x40a5ebae147ae148 then Js.Dbl.math Core.F64.floor tmp8 else Js.Dbl.math Core.F64.jsround tmp8"]],
  // Binary64: subtracts where the code takes the JS remainder — wrong for most inputs.
  dbl_rem: [["let tmp1 ← Js.Dbl.rem total parts", "let tmp1 ← Js.Dbl.sub total parts"]],
  // Binary64 mutants, one per translated operation. Each swaps one emitted call for a
  // different operation; the literal mutant is off by one ulp and the `num` mutant
  // swaps a `Js.Dbl` op for the `Js.Num` op so the view no longer type-checks.
  dbl_div: [["let tmp10 ← Js.Dbl.div tmp9 (Js.Dbl.lit 0x4059000000000000)",
    "let tmp10 ← Js.Dbl.mul tmp9 (Js.Dbl.lit 0x4059000000000000)"]],
  dbl_sub: [["let tmp3 ← Js.Dbl.sub (Js.Dbl.lit 0x3ff0000000000000) tmp2",
    "let tmp3 ← Js.Dbl.add (Js.Dbl.lit 0x3ff0000000000000) tmp2"]],
  dbl_add: [["let tmp8 ← Js.Dbl.add whole tmp7", "let tmp8 ← Js.Dbl.sub whole tmp7"]],
  dbl_neg: [["let tmp9 ← Js.Dbl.neg frac", "let tmp9 ← Js.Dbl.math Core.F64.abs frac"]],
  dbl_floor: [["let tmp11 ← Js.Dbl.math Core.F64.floor tmp10", "let tmp11 ← Js.Dbl.math Core.F64.ceil tmp10"]],
  dbl_ceil: [["let tmp5 ← Js.Dbl.math Core.F64.ceil tmp4", "let tmp5 ← Js.Dbl.math Core.F64.floor tmp4"]],
  dbl_round: [["let tmp9 ← Js.Dbl.math Core.F64.jsround tmp8", "let tmp9 ← Js.Dbl.math Core.F64.trunc tmp8"]],
  dbl_trunc: [["let tmp2 ← Js.Dbl.math Core.F64.trunc clipped", "let tmp2 ← Js.Dbl.math Core.F64.ceil clipped"]],
  dbl_abs: [["let tmp1 ← Js.Dbl.math Core.F64.abs price", "let tmp1 ← Js.Dbl.math Core.F64.neg price"]],
  dbl_min: [["Js.Dbl.min (Js.Dbl.max tmp1 min)", "Js.Dbl.max (Js.Dbl.max tmp1 min)"]],
  dbl_max: [["Js.Dbl.max tmp1 min", "Js.Dbl.min tmp1 min"]],
  dbl_sign: [["let tmp3 ← Js.Dbl.math Core.F64.sign tmp2", "let tmp3 ← Js.Dbl.math Core.F64.abs tmp2"]],
  dbl_eq: [["((clipped).f).eq ((whole).f)", "((clipped).f).eq ((min).f)"]],
  dbl_lt: [["((price).f).lt ((Js.Dbl.lit 0x0).f)", "((price).f).lt ((Js.Dbl.lit 0x4059000000000000).f)"]],
  dbl_le: [["((frac).f).le ((Js.Dbl.lit 0x3fa999999999999a).f)", "((Js.Dbl.lit 0x3fa999999999999a).f).le ((frac).f)"]],
  dbl_isfinite: [["Js.Dbl.isFinite price", "Js.Dbl.isNaN price"]],
  dbl_isnan: [["Js.Dbl.isNaN price", "Js.Dbl.isFinite price"]],
  dbl_isint: [["Js.Dbl.isInteger min", "Js.Dbl.isNaN min"]],
  dbl_ulp: [["let tmp2 ← Js.Dbl.div discountPct (Js.Dbl.lit 0x4059000000000000)",
    "let tmp2 ← Js.Dbl.div discountPct (Js.Dbl.lit 0x4059000000000001)"]],
  dbl_num: [["let tmp1 ← Js.Dbl.mul price quantity", "let tmp1 ← Js.mul price quantity"]],
};

export function run(kind, configPath) {
  const real = ["/opt/proofci/typescript/translate.mjs", new URL("../../typescript/translate.mjs", import.meta.url).pathname].find(existsSync);
  const done = spawnSync("node", [real, configPath], { encoding: "utf8" });
  process.stdout.write(done.stdout);
  process.stderr.write(done.stderr);
  if (done.status !== 0) process.exit(done.status);
  const config = JSON.parse(readFileSync(configPath, "utf8"));
  const file = join(config.out, `${config.module}.lean`);
  let text = readFileSync(file, "utf8");
  for (const [from, to] of EDITS[kind]) {
    if (!text.includes(from)) throw new Error(`the hook found nothing to edit: ${from}`);
    text = text.replace(from, to);
  }
  writeFileSync(file, text);
}
