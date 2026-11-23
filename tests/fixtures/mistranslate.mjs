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
  // Binary64: floors where the code rounds to nearest — off only on a halfway cent, which no
  // sample is likely to hit; the bridge is what must catch it.
  dbl_rare: [["Js.Dbl.math Core.F64.jsround", "Js.Dbl.math Core.F64.floor"]],
  // Binary64: subtracts where the code takes the JS remainder — wrong for most inputs.
  dbl_rem: [["let tmp1 ← Js.Dbl.rem price bucket", "let tmp1 ← Js.Dbl.sub price bucket"]],
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
