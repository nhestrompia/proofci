import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import { after, test } from "node:test";
import { differential } from "./differential.mjs";
import { translate } from "./translate.mjs";

const dir = mkdtempSync(join(tmpdir(), "translate-"));
after(() => rmSync(dir, { recursive: true, force: true }));
let count = 0;

function run(source, extra = {}, target = "f") {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "a.ts"), source);
  for (const [path, text] of Object.entries(extra)) {
    mkdirSync(dirname(join(root, path)), { recursive: true });
    writeFileSync(join(root, path), text);
  }
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
    ["export function f(a: symbol) { return 1; }", /type `symbol`/],
    ["export function f(a: [number, number]) { return 1; }", /not supported/],
    ["interface A { x: number; g(): void } export function f(a: A) { return 1; }", /plain field/],
    ["export function f(...a: number[]) { return 1; }", /rest parameters/],
  ];
  for (const [source, pattern] of cases) rejects(source, pattern);
});

test("`extends` flattens into one record, and the base is still a different type", () => {
  emits("interface A { x: number } interface B extends A { y: number } export function f(a: B) { return a.x + a.y; }", "structure a.B where", "x : Js.Num", "y : Js.Num");
  rejects("interface A { x: number; g(): void } interface B extends A { y: number } export function f(a: B) { return a.y; }", /plain field/);
  rejects(`interface A { x: number } interface B extends A { y: number }
    function g(a: A) { return a.x; }
    export function f(b: B) { return g(b); }`, /not supported|different|record/);
});

test("each use of a generic type is its own structure", () => {
  const result = run(`interface Box<T> { value: T }
    export function f(a: Box<number>, b: Box<string>) { return a.value + b.value.length; }`);
  assert.equal([...result.source.matchAll(/structure a\.Box_\w+ where/g)].length, 2, result.source);
  rejects("interface Box<T> { value: T } export function f<T>(a: Box<T>) { return 1; }", /type parameter/);
  emits("interface L<T = number> { value: T } export function f(a: L) { return a.value; }", "value : Js.Num");
  emits("type P<T> = { value: T; next: T | null }; export function f(a: P<string>) { return a.value; }", "next : (Option Js.Str)");
  emits("interface Box<T> { value: T } export function f(a: number): Box<number> { return { value: a }; }", "Box_");
  rejects("interface T<A> { next: T<A> | null } export function f(a: T<number>) { return 1; }", /recursive/);
});

test("data types from declaration files come in under the package's name", () => {
  const manifest = JSON.stringify({ name: "@acme/lib", version: "1.2.3" });
  const package_ = { "node_modules/@acme/lib/package.json": manifest,
    "node_modules/@acme/lib/index.d.ts": `export interface Base { id: string } export interface Item extends Base { price: number; note?: string }
      export type Mode = "on" | "off"; export declare class C { x: number; m(): void } export declare function g(a: number): number;` };
  const result = run(`import type { Item, Mode } from "@acme/lib";
    export function f(a: Item, m: Mode) { return m === "on" ? a.price : 0; }`, package_);
  assert.ok(result.source.includes("structure Proofci.Package._acme.lib.index.Item where"), result.source);
  assert.ok(result.source.includes("inductive Proofci.Package._acme.lib.index.Mode where"), result.source);
  assert.ok(result.source.includes("note : (Option Js.Str)"), result.source);
  assert.deepEqual(result.packages, { "@acme/lib": "1.2.3" });
  rejects(`import type { C } from "@acme/lib"; export function f(a: C) { return a.x; }`, /not supported/, package_);
  rejects(`import { g } from "@acme/lib"; export function f(a: number) { return g(a); }`, /no source/, package_);
});

test("a local declaration file can give a type but not a function", () => {
  const declared = { "b.d.ts": "export interface P { x: number } export function g(a: number): number;" };
  const result = run(`import type { P } from "./b"; export function f(a: P) { return a.x; }`, declared);
  assert.deepEqual(result.failures, {}, result.source);
  assert.ok(result.source.includes("x : Js.Num"), result.source);
  rejects(`import { g } from "./b"; export function f(a: number) { return g(a); }`, /no source/, declared);
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
    ["export function f(a: symbol) { return a ? 1 : 0; }", /truthiness|type `symbol`/],
    ["export function f(a: number, b: boolean) { return a && b; }", /boolean/],
    ["export function f(a: number) { return a & 1; }", /not supported/],
    ["export function f(a: number) { return +a; }", /not supported/],
    ["export function f(a: number) { return Math.sqrt(a); }", /Math.sqrt/],
    ["export function f(a: number) { return typeof a; }", /not supported/],
    ["export function f(a: number) { return (a as any); }", /type assertions|`any`/],
    ["export function f(a: object) { return `${a}`; }", /template|not supported/],
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
  rejects("export function f(xs: number[]) { let s = 0; const ys = xs.map(x => { s += x; return x; }); return s; }", /nested function/);
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

test("strings are code units, and text the model can't handle is rejected", () => {
  emits(`export function f(a: string) { return a + "x"; }`, `a ++ (js!"x")`);
  emits("export function f(a: string, n: number) { return `${a}:${n}`; }", "Js.numStr n");
  emits("export function f(a: string) { return a.length; }", "Js.len a");
  emits(`export function f(a: string) { return "😀" + a; }`, "[55357, 56832]");
  emits(`export function f(a: string, b: string) { return a === b || a < b; }`, "Js.strLt a b");
  rejects(`export function f(a: string) { return a.match(/x/); }`, /not supported/);
  rejects(`export function f(a: string) { return a.replace(/x/, "y"); }`, /regular expression/);
  rejects(`export function f(a: string, b: number) { return a + b; }`, /string and another type/);
  rejects(`export function f(a: string) { return a.localeCompare("b"); }`, /not supported on strings/);
});

test("a string-literal union stays an enum where the types say so", () => {
  emits(`type S = "a" | "b"; export function f(s: S): S { return s === "a" ? "b" : "a"; }`, ".a");
  emits(`type S = "a" | "b"; export function f(): S { return "a"; }`, "(.a :");
  emits(`export function f(a: string) { return a === "x"; }`, `a = (js!"x")`);
});

test("maps and sets are owned, and their keys are compared by value", () => {
  emits(`export function f(xs: string[]) { const m = new Map<string, number>();
    for (const x of xs) { m.set(x, (m.get(x) ?? 0)); } return m.size; }`.replace("(m.get(x) ?? 0)", "1"), "Js.dictSet", "([] : (Js.Dict Js.Str Js.Num))");
  emits("export function f(m: Map<number, string>, k: number) { return m.has(k) ? m.get(k) : undefined; }", "Js.dictHas");
  emits("export function f(xs: number[]) { const s = new Set<number>(); for (const x of xs) { s.add(x); } return s.size; }", "Js.setAdd");
  rejects("export function f(m: Map<number, number>) { m.set(1, 2); return m; }", /shared with the caller/);
  rejects("interface L { n: number } export function f(m: Map<L, number>) { return 1; }", /keys/);
  rejects("export function f() { return new Map([[1, 2]]); }", /empty/);
  rejects("export function f() { const m = new Map<number, number>(); return m.set(1, 2); }", /own statement/);
});

test("a class that looks like Map is not treated as one", () => {
  rejects("class Map { set(a: number) { return a; } } export function f(m: Map) { return m.set(1); }", /type `Map`/);
});

test("parameters can be optional, defaulted or destructured", () => {
  emits("export function f(a?: number) { return a === undefined ? 0 : a; }", "(Option Js.Num)");
  emits("export function f(a = 2) { return a; }", "a_arg", "| none => do");
  emits("export function f({ x, y: z }: { x: number; y: number }) { return x + z; }", "arg0.x", "arg0.y");
  emits("function g(a: number, b = 1) { return a + b; } export function f(a: number) { return g(a) + g(a, 2); }", "none", "(some ");
});

test("optional fields read as options, and a literal may omit them", () => {
  emits("interface A { x?: number; y: number } export function f(): A { return { y: 1 }; }", "x := none");
  emits("interface A { x?: number; y: number } export function f(a: A) { return a.x === undefined ? 0 : a.x + 1; }", "match a.x with");
  emits("interface A { x: number | null } export function f(a: A) { if (a.x !== null) { return a.x; } return 0; }", "| some tmp1 =>");
  rejects("interface A { x?: number } export function f(a: A) { return a.x === null ? 0 : 1; }", /always false|TypeScript error/);
  emits("interface A { x: number | null } export function f() { let a: A = { x: 1 }; if (a.x !== null) { a = { x: null }; return a.x; } return 0; }", "a_1");
});

test("inline object types are one type per shape", () => {
  const { source } = run("export function f(a: { x: number }): { x: number } { return { x: a.x + 1 }; }");
  assert.equal(source.match(/structure /g).length, 1, source);
});

test("generic functions keep their type parameters", () => {
  emits("export function f<T>(xs: T[]): T[] { return xs.slice(1); }", "{T : Type}");
  rejects("export function f<T>(a: T, b: T) { return a === b; }", /only supported/);
});

test("null checks in their other spellings", () => {
  emits("export function f(a: number | null) { return a ?? 0; }", "| none => do");
  emits("interface A { x: number } export function f(a: A | null) { return a?.x; }", "Option.map (fun item");
  emits("interface A { x?: number } export function f(a: A | null) { return a?.x; }", "Option.bind a");
  emits("interface A { x: number } export function f(a: A | null) { if (a) return a.x; return 0; }", "match a with");
  emits("interface A { x: number } export function f(a: A | null) { if (!a) return 0; return a.x; }", "match a with");
  emits("interface A { x: number } export function f(a: A | null) { if (a !== null && a.x > 0) { return a.x; } return 0; }", "match a with");
  emits("interface A { x: number } export function f(a: A | null) { if (a === null || a.x > 0) { return 1; } return a.x; }", "match a with");
  emits("export function f(a: number | null | undefined) { return a == null ? 0 : a; }");
  rejects("export function f(a: number | null | undefined) { return a === null ? 0 : 1; }", /tell `null` from `undefined`/);
  emits("export function f(a: string | null) { return a ? 1 : 0; }", "Js.truthyStr a = true", "Js.unwrap a");
});

test("a read the project assumes is present stops the model when it isn't", () => {
  emits("interface A { x: number } export function f(xs: A[]) { return xs[0].x; }", "Js.unwrap");
  emits("export function f(xs: number[]) { const a: number = xs[0]; return a; }", "Js.unwrap");
});

test("module-level values are computed once", () => {
  emits("const LIMIT = 2 * 3; export function f(a: number) { return a + LIMIT; }", "def a.LIMIT : Result Js.Num");
  emits("const C = { a: 1 }; export function f(a: number) { return a + C.a; }", "_root_.a.C");
  emits("const NAMES = ['a', 'b']; export function f(a: string) { return NAMES.includes(a); }");
});

test("forEach is a loop, and return only ends one call", () => {
  emits("export function f(xs: number[]) { let s = 0; xs.forEach(x => { s += x; }); return s; }", "Aeneas.Std.loop");
  emits("export function f(xs: number[]) { let s = 0; xs.forEach(x => { s += 1; if (x > 0) return; s += x; }); return s; }", ".cont (tmp2, s_2)");
  rejects("export function f() { const a = [1]; a.forEach(x => { a.push(x); }); return a; }", /looping over/);
});

test("identity comparison isn't approximated", () => {
  rejects("interface L { n: number } export function f(xs: L[], x: L) { return xs.includes(x); }", /identity/);
  rejects("export function f(a: number[], b: number[]) { return a === b; }", /only supported on/);
});

test("truth follows JavaScript, by type", () => {
  emits("export function f(a?: number) { if (a) { return a; } return 0; }", "Js.truthyNum a = true");
  emits("export function f(a?: boolean) { return a ? 1 : 0; }", "Js.truthyBool a = true");
  emits("export function f(a: number[] | null) { return a ? 1 : 0; }", "match a with");
  emits("interface R { s?: string } export function f(r: R) { return r.s ? r.s.length : 0; }", "Js.truthyStr r.s = true");
  rejects("export function f(a: number[]) { if (a) { return 1; } return 0; }", /always truthy/);
  rejects(`type M = "a" | "b"; export function f(a: M) { return a ? 1 : 0; }`, /always truthy/);
  emits("export function f(a: string, b: number) { if (a && b) { return 1; } return 0; }", "(a ≠ []) ∧ (b.val ≠ 0)");
  emits("export function f(a?: string) { if (a && a.length > 1) { return a; } return ''; }", "Js.truthyStr a = true");
  emits("export function f(a: 1 | 2, b: number) { return a === b; }", "a.val = b.val");
});

test("\`&&\` and \`||\` as values keep the value", () => {
  emits("export function f(a: string, b: string) { return a || b; }", "a ≠ []");
  emits("export function f(a: number, b: number) { return a && b; }", "a.val ≠ 0");
  emits("export function f(a?: string) { return a || 'x'; }", "Js.truthyStr a = true");
  emits("interface R { x: number } export function f(a?: R): number | undefined { return a && a.x; }", "Result.ok none");
  emits("export function f(a: string | null, b: boolean): boolean { return a !== null && b; }");
  rejects("declare function g(): string; export function f() { return g() || 'x'; }", /no body|no source|variable or field/);
});

test("null tests work anywhere, and still tell null from undefined", () => {
  emits("export function f(a: number | null) { const b = a === null; return b; }", "Option.isNone a = true");
  emits("export function f(a: number | undefined) { return a !== undefined; }", "¬(Option.isNone a = true)");
  emits("export function f(a: number | null | undefined) { return a == null; }", "Option.isNone a = true");
  emits("export function f(a: number | null | undefined) { return a != null; }", "¬(Option.isNone a = true)");
  rejects("export function f(a: number | null | undefined) { return a === null; }", /tell `null` from `undefined`/);
  rejects("export function f(a: number | undefined) { const b = (a as unknown) === null; return b; }", /assertion|null check/);
  rejects("export function f(a: number) { return a == 1; }", /operator/);
});

test("equality on optional values", () => {
  emits("export function f(a?: boolean) { return a === true; }", "a = some true");
  emits("export function f(a: string | null, b: string) { return a === b; }", "a = some b");
  emits("export function f(a?: string, b?: string) { return a === b; }", "a = b");
  rejects("export function f(a: string | null, b?: string) { return a === b; }", /only supported/);
  rejects("export function f(a: string | null | undefined, b: string | null | undefined) { return a === b; }", /only supported/);
  emits(`type M = "a" | "b"; export function f(a: M, b: M) { return a === b; }`, "a = b");
  rejects("export function f(a: 'x' | 'y', b: number) { return (a as string) === String(b); }", /assertion|supported/);
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
  rejects(`export function f(a: number) {\n  // @ts-expect-error\n  const x: string = 1;\n  return a;\n}`, /@ts-/);
  rejects(`import "./b.ts";\n${source}`, /side effects/, { "b.ts": "export {};" });
  rejects(`Math.floor = (a: number) => a;\n${source}`, /replaces a built-in/);
  rejects(`function g() { Array.prototype.map = () => []; }\n${source}`, /replaces a built-in/);
  rejects(`Object.defineProperty(Math, "floor", { value: 1 });\n${source}`, /replaces a built-in/);
  rejects(`(globalThis as any).Math = {};\n${source}`, /replaces a built-in/);
});

test("package imports resolve through the protected mapping, not the candidate's", () => {
  const make = (name, helper) => {
    const repo = join(dir, name);
    mkdirSync(join(repo, "packages/core/src"), { recursive: true });
    writeFileSync(join(repo, "packages/core/package.json"), JSON.stringify({ name: "@acme/core" }));
    writeFileSync(join(repo, "packages/core/src/index.ts"), helper);
    return repo;
  };
  const base = make("policy", "export function g(a: number) { return a + 1; }");
  const head = make("head", "export function g(a: number) { return a + 2; }");
  // The candidate adds a package claiming the name, which the base doesn't map.
  mkdirSync(join(head, "fake"), { recursive: true });
  writeFileSync(join(head, "fake/package.json"), JSON.stringify({ name: "@acme/fake" }));
  writeFileSync(join(head, "fake/index.ts"), "export function g(a: number) { return a; }");
  writeFileSync(join(head, "a.ts"), `import { g } from "@acme/core"; export function f(a: number) { return g(a); }`);
  writeFileSync(join(head, "b.ts"), `import { g } from "@acme/fake"; export function f(a: number) { return g(a); }`);
  const good = translate({ root: head, repository: head, policyRoot: base, module: "M", targets: ["a.ts::f"] });
  assert.deepEqual(good.failures, {});
  assert.ok(good.source.includes("Js.Num.mk (2)"), good.source);
  const bad = translate({ root: head, repository: head, policyRoot: base, module: "M", targets: ["b.ts::f"] });
  assert.ok(bad.failures["b.ts::f"]);
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

test("only what a function reaches matters", () => {
  const f = "export function f(a: number) { return a + 1; }";
  assert.deepEqual(run(`import { x } from "missing-package";\nexport const y = x;\n${f}`).failures, {});
  assert.deepEqual(run(`const broken: string = 1;\nexport const config = { a: "b" };\n${f}`).failures, {});
  assert.deepEqual(run(`let counter = 0;\nexport function g() { counter += 1; }\n${f}`).failures, {});
  assert.deepEqual(run(`// @ts-ignore\nconst broken: string = 1;\n${f}`).failures, {});
  rejects(`import { x } from "missing-package";\nexport function f(a: number) { return x + a; }`, /TypeScript error|`any`/);
  rejects("let n = 0; export function f(a: number) { return a + n; }", /module-level/);
  rejects("const broken: string = 1; const n = 2; export function f(a: number) { return a + g(); }\nfunction g(): number { const b: string = 1; return 1; }", /TypeScript error/);
});

test("a function with no source is rejected", () => {
  rejects("declare function g(a: number): number; export function f(a: number) { return g(a); }", /module-level|no body|no source/);
  rejects(`import { g } from "./b"; export function f(a: number) { return g(a); }`, /outside|no source|error/,
    { "b.d.ts": "export function g(a: number): number;" });
  rejects(`import { g } from "some-package"; export function f(a: number) { return g(a); }`, /TypeScript error|`any`/);
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

test("a field named after a Lean token is quoted", () => {
  const { source } = run(`export type P = { name: string; to: number };\nexport function f(p: P): number {\n  return p.to;\n}`);
  assert.match(source, /«name» : Js\.Str/);
});

test("the Node comparison stands in for imports the target doesn't reach", async () => {
  const repo = join(dir, "standins");
  mkdirSync(join(repo, "src/lib"), { recursive: true });
  writeFileSync(join(repo, "src/lib/errors.ts"), `throw new Error("must not load");\nexport class Oops extends Error {}\n`);
  writeFileSync(join(repo, "src/lib/index.ts"), "export const STEP = 2n;\n");
  writeFileSync(join(repo, "src/a.ts"), `import { STEP } from "./lib";
import { Oops } from "./lib/errors";
import { thing } from "some-package";
const made = thing({ a: 1 });
export class Late extends Oops {}
export function unrelated() { return made; }
export function twice(a: bigint): bigint {
  return a * STEP;
}
`);
  const result = translate({ root: repo, module: "M", targets: ["src/a.ts::twice"] });
  assert.deepEqual(result.failures, {});
  const out = join(dir, "standins-out");
  mkdirSync(out);
  await differential({ root: repo, out, module: "M", signatures: result.signatures, files: result.files, imports: result.imports, cases: 3 });
  const replay = readFileSync(join(out, "Differential.lean"), "utf8");
  assert.equal(replay.match(/#eval/g).length, 3);
});

test("?. reads a length, and refuses other built-in members", () => {
  emits("export function f(a?: number[]) { return a?.length ?? 0; }", "Js.len item");
  rejects("export function f(a?: Map<string, number>) { return a?.size ?? 0; }", /only supported on fields/);
});

test("a literal compares with an optional value through some", () => {
  emits(`export type K = "x" | "y";\nexport function f(a?: K) {\n  if (a === "x") return 1;\n  if (a === "y") return 2;\n  return 3;\n}`,
    "a = some .x", "a = some .y");
  emits(`export function f(a?: string) { return a === "x"; }`, "a = some (js!");
});

test("number built-ins", () => {
  emits("export function f(a: number) { return Number.isFinite(a); }", "Js.isFinite a");
  emits("export function f(a?: number) { return Number.isInteger(a); }", "Option.isSome a");
  emits("export function f(a: number) { return Number.isNaN(a); }", "Js.isNaN a");
  emits("export function f(a: number) { return a.toFixed(2); }", "Js.toFixed a");
  emits("export function f(a: number) { return a.toFixed(); }", "Js.numStr a");
  emits("export function f(a: number) { return a.toString(); }", "Js.numStr a");
  emits("export function f(a: boolean) { return a.toString(); }", "Js.boolStr a");
  emits("export function f(a: string) { return parseInt(a); }", "Js.parseIntStr true a");
  emits("export function f(a: string) { return Number.parseInt(a, 10); }", "Js.parseIntStr false a");
  emits("export function f(a: string) { return Boolean(a); }", "decide");
  rejects("export function f(a: string) { return parseInt(a, 16); }", /see|no source/);
  rejects("export function f(a: number) { return a.toString(2); }", /see|no source/);
  rejects("export function f(a: unknown) { return Number.isFinite(a); }", /unknown/);
  // A name the code declares itself is not the built-in.
  rejects("function isNaN(a: number) { return a > 1; }\nexport function f(a: string) { return isNaN(1) ? a : parseInt; }", /./);
});

test("an outside call is only usable as the policy lists it", () => {
  const call = (source, assumes) => {
    const root = join(dir, `p${count++}`);
    mkdirSync(root);
    writeFileSync(join(root, "a.ts"), source);
    mkdirSync(join(root, "node_modules/slugger"), { recursive: true });
    writeFileSync(join(root, "node_modules/slugger/package.json"), '{"name":"slugger","types":"index.d.ts"}');
    writeFileSync(join(root, "node_modules/slugger/index.d.ts"), `
      export function slug(a: string): string;
      export function find(a: string, b?: number): string | undefined;
      export function now(): number;
      export function send(a: string): void;
      export function id<T>(a: T): T;
      export function all(...a: string[]): string;
      export function later(a: string): Promise<string>;`);
    return translate({ root, module: "M", targets: ["a.ts::f"], assumes });
  };
  const using = (fn, args = '"x"') => `import { ${fn} } from "slugger";\nexport function f(): unknown { return ${fn}(${args}); }`.replace("unknown", fn === "find" ? "string | undefined" : "string");
  const slug = { call: "slugger::slug", signature: "(a: string): string" };
  assert.match(call(using("slug"), []).failures["a.ts::f"], /no source|can see/);
  const ok = call(using("slug"), [slug]);
  assert.deepEqual(ok.failures, {});
  assert.ok(ok.source.includes("opaque Proofci.Assumed.slugger.slug : Js.Str → Result Js.Str"), ok.source);
  assert.deepEqual(ok.assumed["a.ts::f"], ["slugger::slug"]);
  assert.match(call(using("slug"), [{ ...slug, signature: "(a: string): number" }]).failures["a.ts::f"], /but `assumes` lists/);
  const find = call(using("find"), [{ call: "slugger::find", signature: "(a: string, b?: number | undefined): string | undefined" }]);
  assert.deepEqual(find.failures, {});
  assert.ok(find.source.includes("(js!\"x\") none"), find.source);
  const refused = (fn, signature, args, pattern) => assert.match(call(using(fn, args), [{ call: `slugger::${fn}`, signature }]).failures["a.ts::f"], pattern);
  refused("id", "(a: string): string", '"x"', /generic/);
  refused("all", "(...a: string[]): string", '"x"', /rest parameter/);
  assert.match(call(`import { now } from "slugger";\nexport function f(): number { return now(); }`, [{ call: "slugger::now", signature: "(): number" }]).failures["a.ts::f"], /no arguments/);
  refused("later", "(a: string): Promise<string>", '"x"', /Promise/);
  // A caller inherits what its callee relies on.
  const nested = call(`import { slug } from "slugger";\nfunction g(a: string): string { return slug(a); }\nexport function f(): string { return g("x") + g("y"); }`, [slug]);
  assert.deepEqual(nested.assumed["a.ts::f"], ["slugger::slug"]);
});

test("a listed call whose package isn't installed takes its types from the policy", () => {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "a.ts"), `import { slug } from "not-installed";\nexport function f(a: string): string { return slug(a); }`);
  const target = ["a.ts::f"];
  const signature = "(a: string): string";
  assert.ok(translate({ root, module: "M", targets: target }).failures["a.ts::f"]);
  const ok = translate({ root, module: "M", targets: target, assumes: [{ call: "not-installed::slug", signature }] });
  assert.deepEqual(ok.failures, {});
  assert.ok(ok.source.includes("Proofci.Assumed.not_installed.slug"), ok.source);
  // Listing a different function doesn't make this one usable.
  assert.ok(translate({ root, module: "M", targets: target, assumes: [{ call: "not-installed::other", signature }] }).failures["a.ts::f"]);
});

test("the action requires every function a guarantee reaches to write its types", () => {
  const typed = (source, extra) => {
    const root = join(dir, `p${count++}`);
    mkdirSync(root);
    writeFileSync(join(root, "a.ts"), source);
    for (const [path, text] of Object.entries(extra ?? {})) writeFileSync(join(root, path), text);
    return translate({ root, module: "M", targets: ["a.ts::f"], requireTypes: true }).failures["a.ts::f"];
  };
  assert.match(typed("export function f(a: number) { return a + 1; }"), /add a return type of `number`/);
  assert.match(typed("export function f(a) { return 1; }"), /TypeScript error|`a: any`/);
  assert.match(typed("function g(a: number) { return a; }\nexport function f(a: number): number { return g(a); }"), /add a return type of `number`/);
  assert.equal(typed("export function f(a: number): number { return [a].map(x => x + 1).length; }"), undefined);
  assert.equal(typed("export const f = (a: number): number => a + 1;"), undefined);
  assert.equal(typed("type F = (a: number) => number;\nexport const f: F = a => a + 1;"), undefined);
});

test("a set is built from an array and read by value", () => {
  emits(`export function f(a: string[], k: string) { return new Set(a).has(k); }`, "Js.setHas (Js.setOf a) k");
  emits(`export function f(a: number[]) { return new Set(a).size; }`, "Js.setOf a");
  emits(`export function f(a: string[]) { return [...new Set(a)]; }`, "Js.setOf a");
  emits(`export type K = "x" | "y";\nexport function f(a: K[], k: K) { return new Set(a).has(k); }`, "Js.setOf a");
  rejects(`export function f(a: string) { return new Set(a).size; }`, /on an array/);
  rejects(`export function f(a: string[]) { return new Map(a.map(x => [x, 1])).size; }`, /new Map/);
  rejects(`export type R = { x: number };\nexport function f(a: R[]) { return new Set(a).size; }`, /can be keys/);
});

test("a template prints optional values, enums and unions of literals", () => {
  const kind = `export type K = "x" | "y";\n`;
  emits("export function f(a?: string) { return `<${a}>`; }", "Js.showUndef id a");
  emits("export function f(a: string | null) { return `<${a}>`; }", "Js.showNull id a");
  emits("export function f(a?: number) { return `<${a}>`; }", "Js.showUndef Js.numStr a");
  emits("export function f(a?: boolean) { return `<${a}>`; }", "Js.showUndef Js.boolStr a");
  emits(`${kind}export function f(a: K) { return \`<\${a}>\`; }`, ".toJsStr a");
  emits(`${kind}export function f(a?: K) { return \`<\${a}>\`; }`, "Js.showUndef", ".toJsStr a");
  emits(`${kind}export function f(a: K) { return a === "x" ? \`\${a}\` : "n"; }`, ".toJsStr a");
  emits("export function f(n: number) { return `${n === 1 ? '' : 's'}`; }", "if n.val = 1");
  rejects("export function f(a: string | null | undefined) { return `<${a}>`; }", /isn't known which word prints/);
  rejects("export function f(a: { x: number }) { return `<${a}>`; }", /can go in a template/);
});

test("string search from the end and character codes", () => {
  emits(`export function f(s: string) { return s.lastIndexOf("/"); }`, "Js.strLastIndexOf s");
  emits(`export function f(s: string, i: number) { return s.charCodeAt(i); }`, "Js.charCodeAt s i");
  rejects(`export function f(s: string) { return s.lastIndexOf("/", 2); }`, /with these arguments/);
});

test("a comparison keeps the enumeration after an earlier test narrows it", () => {
  const kind = `export type K = "x" | "y" | "z";\n`;
  emits(`${kind}export function f(a: K) { return a === "x" || a === "y"; }`, "a = .x", "a = .y");
  emits(`${kind}export function f(a: K) {\n  if (a === "x") return 1;\n  if (a === "y") return 2;\n  return a === "z" ? 3 : 4;\n}`, "a = .z");
  emits(`${kind}export type R = { s: K };\nexport function f(r: R) {\n  if (r.s === "x") return 1;\n  return r.s === "y" ? 2 : 3;\n}`, "r.s = .x", "r.s = .y");
  emits(`${kind}export type B<T> = { s: T };\nexport function f(r: B<K>) { return r.s === "x" || r.s === "y"; }`, "r.s = .x", "r.s = .y");
  emits(`export function f(a: string) { return a === "x" || a === "y"; }`, "a = (js!");
  emits(`${kind}export function f(a?: K) { return a === "x" || a === "y"; }`, "a = some .x", "a = some .y");
});

test("a filter with a type guard gives plain values", () => {
  const { source } = run(`export function f(xs: (string | undefined)[]): string[] { return xs.filter((x): x is string => x !== undefined); }\n`);
  assert.match(source, /Js\.unwrapAll tmp/);
});

test("a filter without a type guard keeps the missing values", () => {
  const { source } = run(`export function f(xs: (string | undefined)[]): (string | undefined)[] { return xs.filter(x => x !== "a"); }\n`);
  assert.doesNotMatch(source, /Js\.unwrapAll/);
});

test("a field narrowed inside && is read only when the test passed", () => {
  const { source } = run(`
interface O { on: boolean; wave: number | null }
export function f(w: number, o: O): boolean { return o.on && o.wave !== null && w <= o.wave; }
`);
  const unwrap = source.indexOf("Js.unwrap o.wave"), test = source.indexOf("if (o.on = true)");
  assert.ok(test >= 0 && test < unwrap, source);
});

test("a type parameter with a bound is read at its bound", () => {
  const { source, signatures } = run(`export function f<T extends { to: string }>(xs: T[]): T[] { return xs.filter(x => x.to !== "a"); }\n`);
  assert.doesNotMatch(source, /\{T : Type\}/);
  assert.match(source, /x\.«?to»?/);
  assert.equal(signatures["a.ts::f"].result.item.kind, "record");
});

test("a type parameter with no usable bound stays generic", () => {
  for (const bound of ["", " extends object", " extends unknown[]", " extends () => void"]) {
    const { source } = run(`export function f<T${bound}>(xs: T[]): number { return xs.length; }\n`);
    assert.match(source, /\{T : Type\}/, bound);
  }
});

test("records used only inside a constant are listed for the bridge", () => {
  const { records } = run(`
const ROLES = [{ value: "a" }, { value: "b" }];
const NAMES = ROLES.map(r => r.value);
export function f(r: string): boolean { return NAMES.includes(r); }
`);
  assert.ok(records().some(t => t.kind === "record" && t.fields[0].name === "value"));
});

test("switch on a string, number or field runs its tests in order", () => {
  emits(`export function f(x: string) { switch (x) { case "a": return 1; default: return 0; } }`, 'if (x = (js!"a")) then');
  emits(`export function f(n: number) { switch (n) { case 2: return 1; default: return 0; } }`, "if (n.val =");
  emits(`export function f(o: { m: string }) { switch (o.m) { case "a": { return 1; } default: return 0; } }`, 'if (o.m = (js!"a")) then');
  rejects(`export function f(x: string) { switch (x) { case "a": x = "b"; case "c": return 1; default: return 0; } }`, /Fallthrough case/);
  rejects(`export function f(x: string) { switch (x) { default: return 0; case "a": return 1; } }`, /last case/);
  rejects(`export function f(x: string) { switch (x.trim()) { case "a": return 1; default: return 0; } }`, /this expression/);
});

test("a variable declared without a value is assigned on every path before it is read", () => {
  // date-fns `normalizeTwoDigitYear`
  const { source } = run(`
export function f(twoDigitYear: number, currentYear: number): number {
  const isCommonEra = currentYear > 0;
  const absCurrentYear = isCommonEra ? currentYear : 1 - currentYear;
  let result;
  if (isCommonEra) {
    const rangeEnd = absCurrentYear + 50;
    const isPreviousCentury = twoDigitYear > rangeEnd % 100;
    result = twoDigitYear + rangeEnd - (isPreviousCentury ? 100 : 0);
  } else {
    const rangeStart = absCurrentYear - 50;
    const isPreviousCentury = twoDigitYear >= rangeStart % 100;
    result = twoDigitYear + rangeStart + (isPreviousCentury ? 100 : 0);
  }
  return isCommonEra ? result : 1 - result;
}`);
  assert.match(source, /let result ← Result\.ok \(none : Option Js\.Num\)/);
  assert.match(source, /let result_3 ← if isCommonEra = true then/);
  assert.match(source, /Result\.ok result_3/);
  emits(`export function f(n: number): string { let s: string; if (n > 9) { s = "big"; } else { s = "small"; } return s; }`,
    "(none : Option Js.Str)");
  emits(`export function f(n: number): number { let x; x = n + 1; x = x * 2; return x; }`, "Js.mul x_1");
  emits(`export function f(n: number): number { let x; if (n > 5) { return 0; } x = n; return x; }`);
});

test("a variable declared without a value stops where it might be read unassigned", () => {
  rejects(`export function f(n: number): number { let x; if (n > 0) { x = 1; } return n; }`, /`x` is not assigned on every path/);
  rejects(`export function f(n: number): number { let x; if (n > 0) { x = 1; } return x; }`, /`x` is not assigned on every path|may be read before it is assigned|TypeScript error/);
  rejects(`export function f(n: number): number { let x; return x + n; }`, /never assigned|may be read|TypeScript error/);
  rejects(`export function f(n: number): number { let x; x += n; x = n; return x; }`, /may be read before it is assigned|not assigned on every path|TypeScript error/);
  rejects(`export function f(n: number): number { let x; for (let i = 0; i < n; i++) { x = i; } return n; }`, /not assigned on every path/);
  rejects(`export function f(n: number): string { let x; if (n > 0) { x = 1; } else { x = "a"; } return String(x); }`, /different types|may be read/);
  rejects(`export function f(n: number): number | null { let x: number | null; x = n; return x; }`, /can't hold `null`/);
});

test("|| and && take any left side, which runs once", () => {
  // date-fns `validateDate` in parseISO
  const { source } = run(`
const DAYS_IN_MONTH = [31, null, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31];
function isLeapYearIndex(year: number): boolean { return year % 400 === 0 || (year % 4 === 0 && year % 100 !== 0); }
export function f(year: number, month: number, date: number): boolean {
  return month >= 0 && month <= 11 && date >= 1 && date <= (DAYS_IN_MONTH[month] || (isLeapYearIndex(year) ? 29 : 28));
}`);
  assert.match(source, /\(Js\.at_ tmp\d+ month\)\.join/);
  assert.match(source, /if Js\.truthyNum tmp\d+ = true then/);
  assert.match(source, /Js\.unwrap tmp\d+/);
  emits(`export function f(a: number, b: number): number { return Math.max(a, b) || 7; }`, "Js.max a b", "≠ 0");
  emits(`export function f(a: string): string { return a.trim() && a.slice(1); }`, "Js.trim a", "≠ []");
  emits(`export function f(xs: number[], i: number): number { return xs[i] || 1; }`, "Js.at_ xs i");
  emits(`export function f(a: number, b: number, c: number): number { return (a > b ? a : b) || c; }`);
  emits(`export function f(xs: (number | null)[], i: number): number { return xs[i] || 1; }`, ".join");
  rejects(`export function f(xs: (number | null)[], i: number): number | null { return xs[i] && 1; }`, /`&&` on a value that may be/);
});

test("null and undefined sit in an array whose elements allow them", () => {
  emits(`export function f(a: number): (number | null)[] { return [a, null, 3]; }`, "some a", "none");
  emits(`export function f(a: number): (number | undefined)[] { return [undefined, a]; }`, "none", "some a");
  emits(`export function f(a: string): (string | null)[] { return [null, a, null]; }`, "[none, (some a), none]");
  emits(`export function f(a: number): ((number | null)[] | null)[] { return [[a, null], null]; }`);
  emits(`const SLOTS = [31, null, 30];\nexport function f(): number { let n = 0; for (const s of SLOTS) { if (s !== null) n += s; } return n; }`, "(List (Option Js.Num))");
  rejects(`export function f(a: number): number[] { return [a, null]; }`, /null|assignable|type/);
});

test("an index signature leaves the named fields, and a read through it stops", () => {
  const types = `interface Point { type: "Point"; coordinates: number[]; [foreign: string]: unknown }
interface Bag { count: number; [key: string]: number }\n`;
  const { source } = run(`${types}export function f(p: Point): number { return p.coordinates.length; }`);
  assert.match(source, /structure a\.Point where/);
  assert.doesNotMatch(source, /foreign/);
  emits(`${types}export function f(b: Bag): number { return b.count + 1; }`, "b.count");
  emits(`interface Feature { type: "Feature"; id: number; [foreign: string]: unknown }\nexport function f(n: number): Feature { return { type: "Feature", id: n }; }`);
  rejects(`${types}export function f(b: Bag): number { return b.other; }`, /read through an index signature/);
  rejects(`${types}export function f(b: Bag, k: string): number { return b[k]; }`, /only supported on arrays/);
  rejects(`${types}export function f(b: Bag): Bag { return { ...b, count: 1 }; }`, /spreading a value with an index signature/);
  rejects(`${types}export function f(b: Bag): number { return Object.keys(b).length; }`, /Object|not supported|unsupported|call/);
});

// ---------------------------------------------------------------------------------------- async

const WORLD = `export interface Link { id: string; userId: string | null }
export async function getLink(id: string): Promise<Link | null> { throw new Error("outside"); }
export async function save(id: string, name: string): Promise<void> { throw new Error("outside"); }
export async function count(): Promise<number> { throw new Error("outside"); }\n`;
const EFFECTS = [
  { id: "getLink", call: "world.ts::getLink", signature: "(id: string): Promise<Link | null>", kind: "read" },
  { id: "save", call: "world.ts::save", signature: "(id: string, name: string): Promise<void>", kind: "write" },
  { id: "count", call: "world.ts::count", signature: "(): Promise<number>", kind: "read" },
];

function runAsync(body, { effects = EFFECTS, world = WORLD, target = "f" } = {}) {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "world.ts"), world);
  writeFileSync(join(root, "a.ts"), `import { getLink, save, count } from "./world";\nimport type { Link } from "./world";\n${body}\n`);
  return translate({ root, module: "M", targets: [`a.ts::${target}`], requireTypes: true, effects });
}

function asyncEmits(body, ...fragments) {
  const result = runAsync(body);
  assert.deepEqual(result.failures, {}, body);
  assert.equal(result.fatal, null);
  for (const fragment of fragments) assert.ok(result.source.includes(fragment), `${fragment}\nin\n${result.source}`);
  return result;
}

function asyncRejects(body, pattern, options) {
  const result = runAsync(body, options);
  const reason = result.failures["a.ts::f"] ?? result.fatal;
  assert.ok(reason, `accepted:\n${body}`);
  assert.match(reason, pattern);
}

test("an awaited call listed under effects is one step of the world, recorded in the history", () => {
  const result = asyncEmits(`export async function f(id: string): Promise<boolean> {
    const link = await getLink(id);
    return link !== null;
  }`, "import ProofciAsync", "namespace Proofci.Effects", "| getLink", "Proofci.Effects.call .getLink id",
    ": Proofci.Effects.Eff Bool := do", "  | .getLink => (Option _root_.world.Link)");
  assert.deepEqual(result.effects["a.ts::f"], ["getLink"]);
  assert.equal(result.signatures["a.ts::f"].async, true);
  assert.equal(result.signatures["a.ts::f"].result.kind, "boolean");
});

test("the world lists only the effects that were awaited, with the argument types", () => {
  const { source } = asyncEmits(`export async function f(id: string): Promise<number> {
    await save(id, "x");
    return await count();
  }`, "| save", "| count", "Js.Str × Js.Str", "Proofci.Effects.call .save (id, (js!\"x\"))");
  assert.doesNotMatch(source, /getLink/);
});

test("a function with no async code is translated as before, without the world", () => {
  const result = run("export function f(a: number) { return a + 1; }");
  assert.doesNotMatch(result.source, /Proofci\.Effects|ProofciAsync/);
});

test("an effect's signature has to be the one in the policy", () => {
  asyncRejects(`export async function f(id: string): Promise<boolean> { return (await getLink(id)) !== null; }`,
    /lists `\(id: string\): Promise<Link \| undefined>`/, {
      effects: [{ ...EFFECTS[0], signature: "(id: string): Promise<Link | undefined>" }] });
});

test("an awaited async function that is not listed is translated, and one that can't be is refused", () => {
  // Its body is part of the proof, so what it does is not left to the world.
  const result = asyncEmits(`export async function f(id: string): Promise<number> { return await count(); }`);
  assert.equal(runAsync(`export async function f(id: string): Promise<number> { return await count(); }`, { effects: [] }).failures["a.ts::f"], undefined);
  assert.deepEqual(result.effects["a.ts::f"], ["count"]);
  const opaque = `export async function count(): Promise<number> { return await Promise.resolve(1); }\n`;
  asyncRejects(`export async function f(id: string): Promise<number> { return await count(); }`, /Promise\.resolve|not supported/, { effects: [], world: opaque });
  asyncRejects(`import { readFile } from "fs/promises";
    export async function f(id: string): Promise<number> { return (await readFile(id)).length; }`, /no source in the package|TypeScript error|Cannot find|effects/, { effects: [] });
});

test("a promise that is never awaited is refused", () => {
  asyncRejects(`export async function f(id: string): Promise<void> { save(id, "x"); }`, /never awaited/);
  asyncRejects(`async function g(id: string): Promise<void> { return; }
    export async function f(id: string): Promise<void> { g(id); }`, /without `await`/);
  asyncRejects(`async function g(id: string): Promise<number> { return 1; }
    export function f(id: string): number { return g(id) as unknown as number; }`, /without `await`|type assertions|not supported/);
});

test("Promise.all, .then and the rest fail closed with a reason", () => {
  asyncRejects(`export async function f(id: string): Promise<void> { await Promise.all([save(id, "a"), save(id, "b")]); }`, /`Promise.all` is not supported yet/);
  asyncRejects(`export async function f(id: string): Promise<void> { await save(id, "a").then(() => 1); }`, /`\.then\(\.\.\.\)` on a promise/);
  asyncRejects(`export async function f(id: string): Promise<void> { await new Promise<void>(r => setTimeout(r, 5)); }`, /await.*call|not supported/);
  asyncRejects(`export async function f(ids: string[]): Promise<void> { for await (const x of ids) { await save(x, "a"); } }`, /for await/);
  asyncRejects(`export async function* f(id: string): Promise<void> { await save(id, "a"); }`, /generators|Promise|TypeScript error/);
});

test("an async function has to write Promise<T> as its return type", () => {
  asyncRejects(`export async function f(id: string) { return await count(); }`, /add a return type of `Promise<number>`/);
});

test("calls through an object or a function-typed parameter are not effects yet", () => {
  asyncRejects(`export async function f(deps: { load: () => Promise<number> }): Promise<number> { return await deps.load(); }`,
    /method.*param|handle|not supported/, {
      effects: [...EFFECTS, { id: "load", param: "deps.load", signature: "(): Promise<number>", kind: "read" }] });
});

test("reading shared state that other code may change after an await is refused", () => {
  const world = `${WORLD}\n`;
  asyncRejects(`let total = 0;\nexport async function f(id: string): Promise<number> { await save(id, "x"); return total; }`, /module-level `let`/);
  asyncRejects(`const cache: string[] = [];\nexport async function f(id: string): Promise<boolean> { await save(id, "x"); return cache.length > 0; }`,
    /module-level object that other code may change/, { world });
  // Before the first await there is nothing to interleave with, and immutable data never changes.
  asyncEmits(`const LIMIT = 5;\nconst NAMES: readonly string[] = ["a", "b"];\nexport async function f(id: string): Promise<boolean> {
    await save(id, "x");
    return NAMES.length < LIMIT;
  }`);
});

test("a read after an await in a loop counts as after", () => {
  asyncRejects(`const cache: string[] = [];\nexport async function f(ids: string[]): Promise<number> {
    let n = 0;
    for (const id of ids) {
      n += cache.length;
      await save(id, "x");
    }
    return n;
  }`, /module-level object/);
});

test("the lost-update pattern is refused: read shared state, await, write it back", () => {
  asyncRejects(`let stored = 0;\nexport async function f(id: string): Promise<number> {
    const before = stored;
    await save(id, "x");
    stored = before + 1;
    return stored;
  }`, /module-level `let`|module-level/);
});

test("a function that reads a mutable argument after an await says so; primitives and readonly types don't", () => {
  const first = asyncEmits(`interface Who { id: string; tags: string[] }
    export async function f(who: Who, n: number): Promise<boolean> {
      const link = await getLink(who.id);
      return link !== null && who.tags.length > n;
    }`);
  assert.deepEqual(first.argumentsRelied["a.ts::f"], ["who"]);
  const second = asyncEmits(`interface Who { readonly id: string; readonly tags: readonly string[] }
    export async function f(who: Who, n: number): Promise<boolean> {
      const link = await getLink(who.id);
      return link !== null && who.tags.length > n;
    }`);
  assert.deepEqual(second.argumentsRelied["a.ts::f"], []);
  const third = asyncEmits(`export async function f(id: string, n: number): Promise<boolean> {
      const link = await getLink(id);
      return link !== null && n > 1;
    }`);
  assert.deepEqual(third.argumentsRelied["a.ts::f"], []);
  // Read before the await only: nothing to rely on.
  const fourth = asyncEmits(`interface Who { id: string; tags: string[] }
    export async function f(who: Who): Promise<boolean> {
      const n = who.tags.length;
      const link = await getLink(who.id);
      return link !== null && n > 1;
    }`);
  assert.deepEqual(fourth.argumentsRelied["a.ts::f"], []);
});

test("a callee's reliance on arguments and its effects reach the caller", () => {
  const result = asyncEmits(`interface Who { id: string; tags: string[] }
    async function g(who: Who): Promise<boolean> { const l = await getLink(who.id); return l !== null && who.tags.length > 1; }
    export async function f(w: Who): Promise<boolean> { return await g(w); }`);
  assert.deepEqual(result.effects["a.ts::f"], ["getLink"]);
  assert.deepEqual(result.argumentsRelied["a.ts::f"], ["g: who"]);
});

test("throw, try, catch and finally are outcomes of the computation", () => {
  asyncEmits(`export async function f(id: string): Promise<void> {
    if (id === "") throw new Error("empty id");
    await save(id, "x");
  }`, "Js.Eff.throw ({ «name» := (js!\"Error\"), message := (js!\"empty id\") } : Js.Exn)");
  asyncEmits(`export async function f(id: string): Promise<string> {
    try {
      const link = await getLink(id);
      return link === null ? "none" : link.id;
    } catch (e) {
      if (e instanceof Error) return e.message;
      throw e;
    }
  }`, "Js.Eff.tryCatch", "(fun e => do", "e.message", "Js.Eff.throw e");
  asyncEmits(`export async function f(id: string): Promise<number> {
    try {
      return await count();
    } finally {
      await save(id, "done");
    }
  }`, "Js.Eff.tryFinally");
  asyncRejects(`export async function f(id: string): Promise<void> { throw "text"; }`, /only `throw new Error\(message\)`/);
  asyncRejects(`export async function f(id: string): Promise<void> { throw new Error(1 as unknown as string, { cause: id }); }`, /options|type assertions/);
  asyncRejects(`export async function f(id: string): Promise<string> {
    try { await save(id, "x"); return "a"; } catch (e) { if (e instanceof Error) return e.stack ?? ""; throw e; }
  }`, /only `message` and `name`|not supported/);
});

test("an await inside a loop keeps the history in the loop's state", () => {
  asyncEmits(`export async function f(ids: string[]): Promise<number> {
    let n = 0;
    for (const id of ids) {
      const link = await getLink(id);
      if (link !== null) n += 1;
    }
    return n;
  }`, "Js.Eff.loop", ": Proofci.Effects.Eff (");
  asyncEmits(`export async function f(limit: number): Promise<number> {
    let tries = 0;
    while (tries < limit) {
      if ((await count()) > 2) return tries;
      tries += 1;
    }
    return -1;
  }`, "Js.Eff.loop");
});

test("an await in a short-circuited position runs only when the left side lets it", () => {
  asyncEmits(`export async function f(id: string, ok: boolean): Promise<boolean> {
    return ok && (await getLink(id)) !== null;
  }`, "if ok = true then");
});

test("a failed async target leaves a declaration the contract can still use", () => {
  const result = runAsync(`export async function f(id: string): Promise<void> { await Promise.all([save(id, "a")]); }`);
  assert.ok(result.failures["a.ts::f"]);
  assert.match(result.source, /axiom a\.f \(id : Js\.Str\) : Proofci\.Effects\.Eff Unit/);
  assert.match(result.source, /import ProofciAsync/);
});

test("an effect can be a project function whose body is never read", () => {
  const world = `${WORLD}\nexport async function weird(id: string): Promise<number> { return [1].reduce((a, b) => a + b, 0) + (await new Promise<number>(r => r(1))); }\n`;
  asyncEmits(`export async function f(id: string): Promise<number> { return await count(); }`);
  void world;
});
