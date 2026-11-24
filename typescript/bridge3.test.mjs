import assert from "node:assert/strict";
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { after, test } from "node:test";
import { generate } from "../spike/core/bridge3.mjs";
import { workspacePaths } from "./paths.mjs";

const dir = mkdtempSync(join(tmpdir(), "bridge3-"));
after(() => rmSync(dir, { recursive: true, force: true }));

// changesets' trimSlashes: two `while` loops and a binder (`end`) whose view name is a
// Lean keyword, so the SSA suffix `_vN` used to leak into the step rule's heap keys.
test("two loops emit one `first`-combined rule per loop kind, on real names", () => {
  const root = join(dir, "pkg");
  mkdirSync(join(root, "src"), { recursive: true });
  writeFileSync(join(root, "package.json"), `{"name":"pkg","version":"0.0.0"}`);
  writeFileSync(join(root, "src/utils.ts"), `export function trimSlashes(str: string): string {
  let start = 0;
  let end = str.length;
  while (start < end && str.charCodeAt(start) === 47) start++;
  while (end > start && str.charCodeAt(end - 1) === 47) end--;
  return str.slice(start, end);
}
`);
  const { text } = generate(root, "src/utils.ts::trimSlashes", workspacePaths(root));
  const rules = text.match(/^macro_rules \| `\(tactic\| c_while\)/gm) ?? [];
  assert.equal(rules.length, 1, text.match(/macro_rules[^\n]*/g)?.join("\n"));
  const stepWhile = text.match(/apply step_while/g) ?? [];
  assert.equal(stepWhile.length, 2, "both loops must be alternatives of the one `first`");
  assert.ok(!/"[a-zA-Z]+_v\d+"/.test(text), "a `_vN` name leaked into a heap key");
});

import { lower } from "../spike/core/lower.mjs";

// formbricks' raiseLowQualityFlag shape: a record returned as `{ ...f, strict: true }`, and a
// dict spread followed by its own key. Both used to fail or lower to the wrong Core primitive.
test("a spread followed by own keys lowers to a record copy plus the own fields", () => {
  const root = join(dir, "pkg2");
  mkdirSync(join(root, "src"), { recursive: true });
  writeFileSync(join(root, "package.json"), `{"name":"pkg2","version":"0.0.0"}`);
  writeFileSync(join(root, "src/flag.ts"), `type Flags = { strict: boolean; label: string };
export function raise(f: Flags): Flags { return { ...f, strict: true }; }
export function merge(d: Record<string, number>): Record<string, number> { return { ...d, n: 1 }; }
`);
  const { lean } = lower(root, ["src/flag.ts::raise", "src/flag.ts::merge"], { paths: workspacePaths(root) });
  assert.match(lean, /\.record \[\("label", \.field \((\.var "f"|«f»)\) "label"\), \("strict", \.lit \(\.bool true\)\)\]/);
  assert.match(lean, /\.recPut \[\.prim \.recCopy \[(?:\.var "d"|«d»)\], \.lit \(\.str /);
});
