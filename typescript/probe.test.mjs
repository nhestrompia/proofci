import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { after, test } from "node:test";
import { probe } from "./probe.mjs";

const dir = mkdtempSync(join(tmpdir(), "probe-"));
after(() => rmSync(dir, { recursive: true, force: true }));

function run(source) {
  const root = join(dir, `p${Math.random()}`);
  mkdirSync(join(root, "src"), { recursive: true });
  writeFileSync(join(root, "src", "a.ts"), source);
  return probe({ root, module: "M" });
}

test("export lists name their functions too", () => {
  const { functions } = run(
    "function local(n: number): number { return n + 1 }\n"
    + "export { local }\n"
    + "const hidden = (n: number): number => n\n"
    + "export { hidden as seen }\n");
  assert.deepEqual(functions.map(f => f.function).sort(),
    ["src/a.ts::hidden", "src/a.ts::local"]);
  assert.ok(functions.every(f => f.translated));
});

test("non-exported functions are not targets", () => {
  const { functions } = run("const f = (n: number): number => n\n");
  assert.deepEqual(functions, []);
});

test("one statement can export several functions", () => {
  const { functions } = run(
    "export const one = (n: number): number => n, two = (n: number): number => n\n"
    + "const three = (n: number): number => n\nexport { three }\n");
  assert.deepEqual(functions.map(f => f.function).sort(),
    ["src/a.ts::one", "src/a.ts::three", "src/a.ts::two"]);
});

test("type-only exports are not callable targets", () => {
  const { functions } = run(
    "const f = (n: number): number => n\n"
    + "export type { f }\n"
    + "const g = (n: number): number => n\n"
    + "export { type g }\n");
  assert.deepEqual(functions, []);
});
