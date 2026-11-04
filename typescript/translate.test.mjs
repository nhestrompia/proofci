import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { after, test } from "node:test";
import { translate } from "./translate.mjs";

const dir = mkdtempSync(join(tmpdir(), "translate-"));
after(() => rmSync(dir, { recursive: true, force: true }));
let count = 0;

function run(source, extra = {}, target = "f") {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "a.ts"), source);
  for (const [path, text] of Object.entries(extra)) writeFileSync(join(root, path), text);
  return translate({ root, module: "M", targets: [`a.ts::${target}`] });
}

const failure = (source, extra, target) => {
  const result = run(source, extra, target);
  return result.failures[`a.ts::${target ?? "f"}`] ?? result.fatal;
};

function rejects(source, pattern, extra) {
  const reason = failure(source, extra);
  assert.ok(reason, `accepted:\n${source}`);
  assert.match(reason, pattern);
}

function emits(source, ...fragments) {
  const result = run(source);
  assert.deepEqual(result.failures, {}, source);
  for (const fragment of fragments) assert.ok(result.source.includes(fragment), `${fragment}\nin\n${result.source}`);
}

test("arithmetic binds each step, so a failure stops the function", () => {
  emits("export function f(a: number) { return a + 1 - 2; }", "Js.add a", "Js.sub tmp1");
});

test("floored division keeps the exact quotient", () => {
  emits("export function f(a: number, b: number) { return Math.floor(a / b); }", "Js.floorDiv a b");
  emits("export function f(a: number, b: number) { return Math.ceil(a / b); }", "Js.ceilDiv a b");
  emits("export function f(a: number, b: number) { return a / b; }", "Js.div a b");
});

test("the right side of && only runs when it has to", () => {
  emits(`function g(a: number): boolean { return a > 0; }
    export function f(a: number) { return a !== 0 && g(a); }`, "if ¬(a.val = 0) then");
});

test("names Lean reserves are escaped", () => {
  emits("interface A { to: number } export function f(a: A) { return a.to; }", "a.«to»");
});

test("nullable values narrow through a match", () => {
  emits("export function f(a: number | null) { if (a === null) return 0; return a; }", "match a with", "| some a_1 =>");
  emits("export function f(a: number): number | null { return a; }", "Result.ok (some a)");
  emits("export function f(a: number | undefined) { return a === undefined ? 0 : a; }", "| none =>");
});

test("a null test on the wrong nullish value is rejected, not treated as null", () => {
  rejects("export function f(a: number | null) { if (a === undefined) return 0; return 1; }", /always false/);
  rejects("export function f(a: number | undefined) { if (a === null) return 0; return 1; }", /always false|TypeScript error/);
});

test("types the model can't represent exactly are rejected", () => {
  const cases = [
    ["export function f(a: string) { return 1; }", /type `string`/],
    ["export function f(a: [number, number]) { return 1; }", /not supported/],
    ["export function f(a: { x: number }) { return a.x; }", /not supported/],
    ["interface A { x?: number } export function f(a: A) { return 1; }", /optional/],
    ["interface A { x: number; g(): void } export function f(a: A) { return 1; }", /plain field/],
    ["interface A { x: number } interface B extends A { y: number } export function f(a: B) { return 1; }", /extends/],
    ["export function f(a: number | null | undefined) { return 1; }", /both/],
    ["export function f<T>(a: T) { return 1; }", /generic/],
    ["export function f(a = 1) { return a; }", /plain parameters/],
    ["export function f(...a: number[]) { return 1; }", /plain parameters/],
    ["export function f({ a }: { a: number }) { return a; }", /plain parameters/],
  ];
  for (const [source, pattern] of cases) rejects(source, pattern);
});

test("structural typing can't smuggle one record in as another", () => {
  rejects(`interface A { x: number } interface B { x: number; y: number }
    function g(a: A) { return a.x; } export function f(b: B) { return g(b); }`, /is used as/);
});

test("JavaScript behavior the model doesn't cover is rejected", () => {
  const cases = [
    ["export function f(a: number) { return a * 0.5; }", /not a safe integer/],
    ["export function f() { return 9007199254740993; }", /not a safe integer/],
    ["export function f(a: number) { return a == 1; }", /not supported/],
    ["export function f(a: number) { return a ? 1 : 0; }", /truthiness/],
    ["export function f(a: number, b: boolean) { return a && b; }", /boolean/],
    ["export function f(a: number) { return a & 1; }", /not supported/],
    ["export function f(a: number) { return +a; }", /not supported/],
    ["export function f(a: number) { return Math.sqrt(a); }", /Math.sqrt/],
    ["export function f(a: number) { return typeof a; }", /not supported/],
    ["export function f(a: number) { return (a as any); }", /type assertions|`any`/],
    ["export function f() { return `x`; }", /not supported/],
  ];
  for (const [source, pattern] of cases) {
    rejects(source, pattern);
  }
});

test("reassigning a local makes a new name, so nothing is shadowed", () => {
  emits("export function f(a: number) { let b = 0; b += a; b = b + 1; return b; }", "let b_1 ←", "let b_2 ←");
  emits("export function f(a: number) { a = a + 1; return a; }", "let a_1 ←");
  emits("export function f(a: number) { let b = a; b++; b--; return b; }", "Js.add b", "Js.sub b_1");
});

test("branches that don't return join the code after them", () => {
  emits("export function f(a: number) { let r = a; if (r > 9) { r = 9; } return r + 1; }", "let r_2 ← if", "Js.add r_2");
  emits(`export function f(a: number | null) { let t = 0; if (a !== null) { t = a; } return t; }`, "let t_2 ← do", "match a with");
});

test("a branch that leaves makes no join", () => {
  emits("export function f(a: number) { if (a < 0) throw new RangeError('x'); return a; }", "Result.fail .panic");
  const { source } = run("export function f(a: number) { if (a < 0) return 1; return a; }");
  assert.ok(!source.includes("← if"), source);
});

test("loops use Aeneas's loop, with the changed variables as state", () => {
  emits("export function f(n: number) { let s = 0; for (let i = 0; i < n; i++) { s += i; } return s; }",
    "Aeneas.Std.loop", "(i_1, s_1)", ".cont (i_2, s_2)", ".done s_1");
  emits("export function f(n: number) { let i = 0; while (i < n) { i += 1; } return i; }", ".cont i_2");
});

test("a counter stays out of what the code after a for loop sees", () => {
  const { source } = run("export function f(n: number) { let s = 0; for (let i = 0; i < n; i++) { s += 1; } return s; }");
  assert.ok(source.includes("Result (Js.Num))"), source);
});

test("break, continue and return inside loops", () => {
  emits("export function f(n: number) { let i = 0; while (true) { if (i > n) break; i += 1; } return i; }", ".done i_1");
  emits("export function f(n: number) { for (let i = 0; i < n; i++) { if (i === 3) return i; } return -1; }",
    ".done (.inl", ".done (.inr", "Sum (Js.Num)");
  emits("export function f(n: number) { let s = 0; for (let i = 0; i < n; i++) { if (i === 3) continue; s += i; } return s; }", "Js.add i_1");
});

test("a block's declarations end with the block", () => {
  emits("export function f(a: number) { const b = a; { const b = 2; if (b > a) { throw new Error('x'); } } return b; }", "let b_1 ←");
  rejects("export function f(a: number) { const b = 1; { const b = 2; if (a > b) { return a; } } return b; }", /nested block/);
});

test("a void function can be called for what it throws", () => {
  emits(`function check(a: number): void { if (a < 0) throw new Error("x"); }
    export function f(a: number) { check(a); return a; }`, "_root_.a.check a", "Result.ok ()");
});

test("catch runs for throws, and can't see what it can't model", () => {
  emits("function g(a: number): number { return a; } export function f(a: number) { try { return g(a); } catch { return 0; } }", "Js.attempt");
  rejects("export function f(a: number) { try { return a; } catch (e) { throw e; } }", /caught value|only `throw new/);
  rejects("export function f(a: number) { let b = 0; try { b = 1; throw new Error(); } catch { return b; } }", /inside `try`/);
  rejects("export function f(a: number) { try { return a; } finally { } }", /finally/);
});

test("only what can be modelled can be thrown", () => {
  rejects("export function f(a: number) { throw a; }", /throw new/);
  rejects("function g() { return 1; } export function f(a: number) { throw new Error(String(g())); }", /throw new/);
});

test("writes that could reach shared state are rejected", () => {
  rejects("interface A { x: number } export function f(a: A) { a.x = 1; return a; }", /shared with the caller/);
  rejects("let c = 0; export function f(a: number) { c = a; return a; }", /module-level/);
  rejects("export function f(a: number) { var b = a; return b; }", /var/);
  rejects("export function f(a: number) { let b = 0; [1].length; const g = () => { b = 1; }; return b; }", /nested function/);
  rejects("export function f(a: number | null) { if (a !== null) { a = null; } return 1; }", /own null check/);
  rejects("export function f(a: number) { let b = 0; const c = (b = 1); return c; }", /not supported/);
  rejects("export function f(a: number) { let b = 0; return b++; }", /not supported/);
  rejects("export function f(a: number) { let b = 1; b **= 2; return b; }", /operator/);
});

test("arrays are lists, and reading past the end is undefined", () => {
  emits("export function f(xs: number[]) { return xs[0]; }", "Js.at_ xs", "Option");
  emits("export function f(xs: readonly number[]) { return xs.length; }", "Js.len xs");
  emits("export function f(xs: number[]) { return [...xs, 1]; }", "xs ++ [");
  emits("export function f(xs: number[], i: number) { return xs[i] === 3; }", "= some");
  emits("export function f(xs: number[]) { return xs[0]!; }", "Js.unwrap");
});

test("for...of walks a copy of the list it started with", () => {
  emits("export function f(xs: number[]) { let s = 0; for (const x of xs) { s += x; } return s; }", "| [] =>", "| x :: tmp");
});

test("callbacks become functions, in the order JavaScript runs them", () => {
  emits("export function f(xs: number[]) { return xs.map(x => x + 1); }", "Js.map (fun (x : Js.Num) => do");
  emits("export function f(xs: number[]) { return xs.filter(x => { if (x > 0) return true; return false; }); }", "Js.filter");
  emits("export function f(xs: number[]) { return xs.reduce((a, b) => a + b, 0); }", "Js.reduce");
});

test("callbacks that would see more than the model passes are rejected", () => {
  rejects("export function f(xs: number[]) { return xs.map((x, i) => x + i); }", /exactly 1/);
  rejects("function g(x: number) { return x; } export function f(xs: number[]) { return xs.map(g); }", /inline function/);
  rejects("export function f(xs: number[]) { return xs.reduce((a, b) => a + b); }", /initial value/);
  rejects("export function f(xs: number[]) { let s = 0; xs.forEach(x => { s += x; }); return s; }", /nested function/);
});

test("an in-place change needs a value nobody else can see", () => {
  const shared = [
    ["the caller's array", "export function f(xs: number[]) { xs.push(1); return xs; }", /shared with the caller/],
    ["an alias of a parameter", "export function f(xs: number[]) { const y = xs; y.push(1); return y; }", /must start as a new/],
    ["a second name", "export function f() { const a: number[] = []; const b = a; a.push(1); return b; }", /passed around or stored/],
    ["storing it", "interface B { a: number[] } export function f() { const a: number[] = []; const b: B = { a }; a.push(1); return b; }", /passed around or stored/],
    ["passing it on", "function g(a: number[]) { return a; } export function f() { const a: number[] = []; const b = g(a); a.push(1); return b; }", /passed around or stored/],
    ["an element", "interface L { n: number } export function f(xs: L[]) { for (const x of xs) { x.n = 1; } return xs; }", /element of an array|shared/],
    ["a field holding an array", "interface B { a: number[] } export function f(b: B) { const a = b.a; a.push(1); return b; }", /must start as a new/],
    ["a nested field", "interface B { a: number[] } export function f() { const b: B = { a: [] }; b.a.push(1); return b; }", /nested/],
    ["reassigned from outside", "export function f(xs: number[]) { let a: number[] = []; a = xs; a.push(1); return xs; }", /must start as a new/],
    ["while looping over it", "export function f() { const a = [1]; for (const x of a) { a.push(x); } return a; }", /looping over/],
    ["a result that can't be used yet", "export function f() { const a = [1]; return a.push(2); }", /own statement/],
  ];
  for (const [what, source, pattern] of shared) {
    const reason = failure(source);
    assert.ok(reason, `accepted ${what}`);
    assert.match(reason, pattern, what);
  }
});

test("a new array can change freely", () => {
  emits("export function f(xs: number[]) { const a = xs.slice(); a.push(1); return a; }", "a ++ [");
  emits("export function f() { const a = [1, 2]; a[0] = 5; return a; }", "Js.setAt");
  emits("interface P { x: number } export function f() { const p: P = { x: 1 }; p.x = 2; return p; }", "with x :=");
  emits("export function f(n: number) { const a: number[] = []; for (let i = 0; i < n; i++) { a.push(i); } return a.length; }", "a_2");
});

test("identity comparison isn't approximated", () => {
  rejects("interface L { n: number } export function f(xs: L[], x: L) { return xs.includes(x); }", /identity/);
  rejects("export function f(a: number[], b: number[]) { return a === b; }", /only supported on/);
});

test("switch handles grouped cases, default and a final break", () => {
  emits(`type S = "a" | "b" | "c"; export function f(s: S) {
    let r = 0;
    switch (s) { case "a": case "b": r = 1; break; default: r = 2; }
    return r; }`, "| .a =>", "| .c =>");
  rejects(`type S = "a" | "b"; export function f(s: S) { let r = 0; switch (s) { case "a": r = 1; case "b": r = 2; } return r; }`, /falling through|TypeScript error/);
});

test("self-recursion becomes a fixpoint, and mutual recursion is rejected", () => {
  emits("export function f(n: number): number { return n <= 0 ? 0 : f(n - 1); }", "partial_fixpoint", "a.f tmp");
  rejects(`function g(n: number): number { return f(n); } export function f(n: number): number { return g(n); }`, /mutual/);
});

test("bigint stays exact and division follows JavaScript", () => {
  emits("export function f(a: bigint, b: bigint) { return (a * 2n + 1n) / b; }", "(a * (2 : Int))", "Js.bdiv");
  emits("export function f(a: bigint) { return a < 3n; }", "a < (3 : Int)");
  rejects("export function f(a: bigint, b: number) { return a + b; }", /TypeScript error/);
});

test("code outside the subset can't reach a function through a closure", () => {
  rejects("export function f(a: number) { const g = (b: number) => a + b; return g(1); }", /not supported|can see/);
  rejects("export function f(a: number) { function g() { return a; } return g(); }", /not supported/);
});

test("a local can't shadow what the generated code refers to", () => {
  rejects("export function f(none: number) { return none; }", /none/);
  rejects("export function f(a: number) { const Js = a; return Js; }", /Js/);
});

test("Math must be the real Math", () => {
  rejects("const Math = 1; export function f(a: number) { return Math.floor(a); }", /TypeScript error/);
  rejects(`import { Math } from "./b.ts"; export function f(a: number) { return Math.floor(a); }`, /see|outside|not supported/,
    { "b.ts": "export const Math = { floor: (a: number) => a + 1 };" });
});

test("a shadow JavaScript file, a compiler switch or a side effect rejects the file", () => {
  const source = "export function f(a: number) { return a; }";
  rejects(source, /beside/, { "a.js": "export const f = () => 0;" });
  rejects(`// @ts-nocheck\n${source}`, /@ts-/);
  rejects(`// @ts-expect-error\nconst x: string = 1;\n${source}`, /@ts-/);
  rejects(`import "./b.ts";\n${source}`, /side effects/, { "b.ts": "export {};" });
  rejects(`Math.floor = (a: number) => a;\n${source}`, /on import/);
  rejects(`let x = 1;\n${source}`, /module-level/);
  rejects(`export const x = compute();\nfunction compute() { return 1; }\n${source}`, /module-level/);
});

test("a problem with a file rejects every target in it, not only the first", () => {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "a.ts"), "export function f(a: number) { return a; }\nexport function g(a: number) { return a; }\n");
  writeFileSync(join(root, "a.js"), "export const f = () => 0;\n");
  const result = translate({ root, module: "M", targets: ["a.ts::f", "a.ts::g"] });
  assert.match(result.failures["a.ts::f"], /beside/);
  assert.match(result.failures["a.ts::g"], /beside/);
});

test("a problem in a callee's file rejects every caller", () => {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "a.ts"), `import { h } from "./b.ts";
    export function f(a: number) { return h(a); }
    export function g(a: number) { return h(a) + 1; }\n`);
  writeFileSync(join(root, "b.ts"), "export function h(a: number) { return a; }\nMath.floor = (x: number) => x;\n");
  const result = translate({ root, module: "M", targets: ["a.ts::f", "a.ts::g"] });
  assert.deepEqual(Object.keys(result.failures).sort(), ["a.ts::f", "a.ts::g"]);
});

test("a function with no source is rejected", () => {
  rejects("declare function g(a: number): number; export function f(a: number) { return g(a); }", /module-level|no body|no source/);
  rejects(`import { g } from "./b"; export function f(a: number) { return g(a); }`, /outside|no source|error/,
    { "b.d.ts": "export function g(a: number): number;" });
  rejects(`import { g } from "some-package"; export function f(a: number) { return g(a); }`, /TypeScript error/);
});

test("a failed target stays declared so that the other targets are judged", () => {
  const result = run("export function f(a: number) { return a * 0.5; }");
  assert.ok(result.source.includes("axiom a.f"), result.source);
});

test("calls cross files through their own namespaces", () => {
  const result = run(`import { g } from "./b.ts"; export function f(a: number) { return g(a); }`,
    { "b.ts": "export function g(a: number) { return a + 1; }" });
  assert.deepEqual(result.failures, {});
  assert.ok(result.source.includes("_root_.b.g a"));
});
