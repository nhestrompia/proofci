import assert from "node:assert/strict";
import { mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { after, test } from "node:test";
import { analyze, programFor, summarize, tierOf } from "./analyze.mjs";

const dir = mkdtempSync(join(tmpdir(), "survey-"));
after(() => rmSync(dir, { recursive: true, force: true }));

function run(source, name = "f") {
  const path = join(dir, `${Math.random().toString(36).slice(2)}.ts`);
  writeFileSync(path, source);
  const results = analyze(programFor([path]));
  const found = results.find(r => r.name === name);
  assert.ok(found, `no result for ${name}`);
  return found;
}

const has = (source, feature, name) => assert.ok(run(source, name).features.includes(feature), source);
const clean = source => assert.deepEqual(run(source).features, [], source);

test("plain integer logic has no blockers", () => {
  clean(`interface A { from: number; to: number }
    export function f(a: A, n: number): A | null {
      if (n <= 0 || n > a.from) return null;
      return { from: a.from - n, to: a.to + n };
    }`);
});

test("local mutation of a fresh value is fine", () => {
  clean(`export function f(xs: number[]) { const out: number[] = []; let t = 0;
    for (const x of xs) { t += x; out.push(t); } return out; }`);
});

test("floored division is an integer, other division is fractional", () => {
  clean(`export function f(a: number, b: number) { return Math.floor(a * 2 / b); }`);
  has(`export function f(a: number, b: number) { return a / b; }`, "fractional");
  has(`export function f(a: number) { return a * 0.02; }`, "fractional");
  has(`export function f(a: number) { return Math.sqrt(a); }`, "fractional");
  clean(`export function f(a: bigint, b: bigint) { return a / b; }`);
});

test("writes are told apart by what they reach", () => {
  has(`export function f(xs: number[]) { xs.push(1); }`, "param-mutation");
  has(`export function f(a: { n: number }) { a.n = 1; }`, "param-mutation");
  has(`let c = 0; export function f() { c = 1; }`, "module-state");
  has(`const c = { n: 0 }; export function f() { c.n = 1; }`, "module-state");
  has(`export function f(a: { b: { n: number } }) { const r = a.b; r.n = 1; }`, "alias-risk");
  has(`export function f(xs: { n: number }[]) { for (const x of xs) x.n = 1; }`, "alias-risk");
  has(`export function f(xs: number[]) { let t = 0; xs.forEach(x => { t += x; }); return t; }`, "closure-mutation");
  has(`export class C { n = 0; g() { this.n += 1; } }`, "this-state", "C.g");
});

test("casts: upcasts are fine, downcasts and any are not", () => {
  clean(`export function f(a: "x") { return a as string; }`);
  clean(`export function f() { return [1, 2] as const; }`);
  has(`export function f(a: string) { return a as "x"; }`, "unchecked-cast");
  has(`export function f(a: any) { return a; }`, "unchecked-cast");
});

test("non-null assertions translate to a failure, so they are fine", () => {
  clean(`export function f(a: number | null) { return a! + 1; }`);
});

test("coercion and reflection", () => {
  has(`export function f(a: number, b: number) { return a == b; }`, "coercion");
  clean(`export function f(a: number | null) { return a == null; }`);
  has(`export function f(a: string, b: number) { return a + b; }`, "coercion");
  has(`export function f(a: object) { return Object.keys(a); }`, "reflection");
  has(`export function f(a: { [k: string]: number }, k: string) { return a[k]; }`, "dynamic-key");
  clean(`export function f(a: number[], i: number) { return a[i]; }`);
});

test("ambient state and other builtins", () => {
  has(`export function f() { return Date.now(); }`, "date");
  has(`export function f() { return new Date(); }`, "date");
  has(`export function f(a: string) { return /x/.test(a); }`, "regex");
  has(`export function f() { return Math.random(); }`, "ambient-effect");
  has(`export function f() { console.log(1); }`, "ambient-effect");
  has(`export function f(a: string) { return a.toLowerCase(); }`, "unmodeled-builtin");
  has(`export async function f() { return 1; }`, "async");
  has(`export function* f() { yield 1; }`, "generator");
  has(`export function f(a: string) { return eval(a); }`, "dynamic");
});

test("a shadowing local is not the global", () => {
  clean(`export function f() { const console = 1; return console; }`);
});

test("blockers propagate through calls, including cycles", () => {
  has(`function g(a: number) { return a / 3; }
    export function f(a: number) { return g(a); }`, "fractional");
  has(`function g(n: number): number { return n <= 0 ? 0 : f(n - 1); }
    function h() { return Date.now(); }
    export function f(n: number): number { return n > 9 ? h() : g(n); }`, "date");
});

test("calls with no visible body are external", () => {
  has(`declare function g(a: number): number; export function f(a: number) { return g(a); }`, "external-call");
  has(`export function f(g: (a: number) => number) { return g(1); }`, "external-call");
  has(`interface S { get(): number } export function f(s: S) { return s.get(); }`, "external-call");
});

test("tiers", () => {
  assert.equal(tierOf(new Set()), 2);
  assert.equal(tierOf(new Set(["async"])), 3);
  assert.equal(tierOf(new Set(["async", "regex"])), 9);
});

test("summary counts only functions that decide something", () => {
  const summary = summarize([
    { logic: true, tier: 2, features: [] },
    { logic: true, tier: 3, features: ["async"] },
    { logic: true, tier: 9, features: ["regex"] },
    { logic: true, tier: 9, features: ["regex", "date"] },
    { logic: false, tier: 9, features: ["regex"] },
  ]);
  assert.deepEqual(summary, { functions: 5, logic: 4, m2: 1, m3: 2,
    blockers: { regex: 2, date: 1 }, sole: { regex: 1 } });
});
