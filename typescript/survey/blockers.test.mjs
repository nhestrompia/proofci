import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { after, test } from "node:test";
import { measure } from "./blockers.mjs";
import { translate } from "../translate.mjs";

const dir = mkdtempSync(join(tmpdir(), "blockers-"));
after(() => rmSync(dir, { recursive: true, force: true }));
let count = 0;
const run = (source, ...names) => {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "m.ts"), source);
  return Object.fromEntries(measure(root, names.map(n => `m.ts::${n}`)).map(r => [r.target.split("::")[1], r.blockers]));
};

test("every blocker in a function is listed, not only the first", () => {
  const { f } = run(`export function f(a: unknown, b: any) {
    let n = 0; const m = [1].map(x => { n = x; return x; });
    return n; }`, "f");
  assert.ok(f.includes("type unknown"), f.join());
  assert.ok(f.includes("type any"), f.join());
  assert.ok(f.some(r => /nested function/.test(r)), f.join());
});

test("a caller inherits what its callees need", () => {
  const { f, g } = run(`function g(a: unknown) { return 1; }
    export function f(a: number) { return g(a); }
    export function h(a: number) { return a + 1; }`, "f", "g", "h");
  assert.ok(f.includes("type unknown"), f.join());
  assert.deepEqual(f, g);
});

test("the count of clean functions agrees with the real translator", () => {
  const source = `export function a1(a: number) { return a + 1; }
    export function b1(a: unknown) { return 1; }
    export function c1(a: number): number { return a > 0 ? c1(a - 1) : 0; }
    export function d1(a: string) { return a.length; }`;
  const root = join(dir, "same");
  mkdirSync(root);
  writeFileSync(join(root, "m.ts"), source);
  const names = ["a1", "b1", "c1", "d1"];
  const targets = names.map(n => `m.ts::${n}`);
  const real = translate({ root, module: "M", targets });
  const rows = measure(root, targets);
  for (const row of rows) assert.equal(row.blockers.length === 0, !real.failures[row.target], row.target);
});

test("`async` doesn't hide what the body needs", () => {
  const { f } = run("export async function f(a: unknown) { return await g(); } async function g() { return 1; }", "f");
  assert.ok(f.includes("async"), f.join());
  assert.ok(f.includes("type unknown"), f.join());
});

test("a type that fails blocks every function that uses it, not only the first", () => {
  const { f, g } = run(`interface T { a: unknown }
    export function f(x: T) { return 1; }
    export function g(x: T) { return 2; }`, "f", "g");
  assert.ok(f.includes("type unknown"), f.join());
  assert.deepEqual(g, f);
});

test("a function is counted as untyped through what it calls", () => {
  const rows = root => Object.fromEntries(measure(root, ["m.ts::f", "m.ts::g"]).map(r => [r.target.split("::")[1], r]));
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "m.ts"), `function h(a: number) { return a; }
    export function f(a: number): number { return h(a); }
    export const g = (a: number): number => [a].map(x => x + 1).length;`);
  const { f, g } = rows(root);
  assert.equal(f.untyped, 1);
  assert.deepEqual(f.self, []);
  assert.equal(g.untyped, 0);
});

test("an outside call says whether its published types translate", () => {
  const root = join(dir, `p${count++}`);
  mkdirSync(join(root, "node_modules/lib"), { recursive: true });
  writeFileSync(join(root, "node_modules/lib/index.d.ts"), "export function good(a: string): string;\nexport function bad(a: string): Promise<string>;\n");
  writeFileSync(join(root, "node_modules/lib/package.json"), '{"name":"lib","types":"index.d.ts"}');
  writeFileSync(join(root, "m.ts"), `import { good, bad } from "lib";
    export function f(a: string): string { return good(a); }
    export function g(a: string) { return bad(a); }`);
  const [f, g] = measure(root, ["m.ts::f", "m.ts::g"]);
  assert.ok(f.blockers.some(b => /types translate/.test(b)), f.blockers.join());
  assert.ok(g.blockers.some(b => /types don't translate/.test(b)), g.blockers.join());
});
