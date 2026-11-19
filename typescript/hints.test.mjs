import { test } from "node:test";
import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { translate } from "./translate.mjs";
import { hintFor, PREFIX } from "./hints.mjs";

const FALLBACK = hintFor("no reason like this one");
const source = readFileSync(new URL("./translate.mjs", import.meta.url), "utf8");

// The literal start of every reason the translator writes, with `${...}` read as `x`.
function reasons() {
  const found = [];
  for (const pattern of [/\bfail\(\s*[^;]*?,\s*(["`])((?:\\.|(?!\1)[^\\])*)\1/gs, /new Unsupported\(\s*(["`])((?:\\.|(?!\1)[^\\])*)\1/gs]) {
    for (const match of source.matchAll(pattern)) {
      found.push(match[2].replace(/\$\{(?:[^{}]|\{[^{}]*\})*\}/g, "x").replace(/\\`/g, "`"));
    }
  }
  return found;
}

test("every reason the translator writes has a hint", () => {
  const all = reasons();
  assert.ok(all.length > 150, `found only ${all.length} reasons`);
  const missing = all.filter(reason => hintFor(`a.ts:1: ${reason}`) === FALLBACK);
  assert.deepEqual(missing, []);
});

const dir = mkdtempSync(join(tmpdir(), "hints-"));
let count = 0;
function failure(text, options = {}) {
  const root = join(dir, `p${count++}`);
  mkdirSync(root);
  writeFileSync(join(root, "a.ts"), text);
  const result = translate({ root, module: "M", targets: ["a.ts::f"], ...options });
  return result.failures["a.ts::f"] ?? result.fatal ?? undefined;
}

// What the code uses, the hint it gets, and the rewrite the hint suggests.
const rewrites = [
  ["recursion through a second interface", /let the type hold itself directly/,
    `interface A { value: number; b: B | null }\ninterface B { a: A }\nexport function f(a: A): number { return a.value; }`,
    `interface A { value: number; next: A | null }\nexport function f(a: A): number { return a.value; }`],
  ["a recursive type with no end", /so a value can end/,
    `interface R { value: number; next: R }\nexport function f(r: R): number { return r.value; }`,
    `interface R { value: number; next: R | null }\nexport function f(r: R): number { return r.value; }`],
  ["regular expression outside the subset", /keep to code units, classes/,
    `export function f(s: string): boolean { return /^a{2}/.test(s); }`,
    `export function f(s: string): boolean { return /^aa/.test(s); }`],
  ["`split` with capturing groups", /non-capturing/,
    `export function f(s: string): string[] { return s.split(/(,|;)/); }`,
    `export function f(s: string): string[] { return s.split(/(?:,|;)/); }`],
  ["`any`", /write the type the value really has/,
    `export function f(x: any): number { return x; }`,
    `export function f(x: number): number { return x; }`],
  ["number-keyed record", /key the record by strings/,
    `export function f(r: Record<number, string>): string { return r[1] ?? ""; }`,
    `export function f(r: Record<string, string>): string { return r["a1"] ?? ""; }`],
  ["utility type", /write the fields out as an interface/,
    `interface A { a: number; b: string }\nexport function f(x: Partial<A>): number { return x.a ?? 0; }`,
    `interface A { a?: number; b?: string }\nexport function f(x: A): number { return x.a ?? 0; }`],
  ["`enum`", /string-literal union/,
    `enum E { A = "a", B = "b" }\nexport function f(e: E): boolean { return e === E.A; }`,
    `type E = "a" | "b";\nexport function f(e: E): boolean { return e === "a"; }`],
  ["untagged union", /named `type` whose members each have a string literal field named `kind`/,
    `interface A { a: number }\ninterface B { b: string }\nexport function f(x: A | B): number { return 0; }`,
    `interface A { kind: "a"; a: number }\ninterface B { kind: "b"; b: string }\ntype U = A | B;\nexport function f(x: U): number { switch (x.kind) { case "a": return x.a; case "b": return 0; } }`],
  ["missing return type", /write them into the function's signature/,
    `export function f(x: number) { return x + 1; }`,
    `export function f(x: number): number { return x + 1; }`, { requireTypes: true }],
  ["nested write", /replace the inner object/,
    `interface B { c: number }\ninterface A { b: B }\nexport function f(a: A): A { const n: A = { b: { ...a.b } }; n.b.c = 1; return n; }`,
    `interface B { c: number }\ninterface A { b: B }\nexport function f(a: A): A { const n: A = { ...a }; n.b = { ...n.b, c: 1 }; return n; }`],
  ["`??=`", /write it out with `=`/,
    `export function f(x: number | null): number { x ??= 1; return x; }`,
    `export function f(x: number | null): number { const y = x ?? 1; return y; }`],
  ["`splice`", /`slice` and spread/,
    `export function f(xs: number[]): number[] { const ys = [...xs]; ys.splice(0, 1); return ys; }`,
    `export function f(xs: number[]): number[] { return [...xs.slice(0, 0), ...xs.slice(1)]; }`],
  ["`Math.sign`", /compare with 0/,
    `export function f(a: number): number { return Math.sign(a); }`,
    `export function f(a: number): number { return a > 0 ? 1 : a < 0 ? -1 : 0; }`],
  ["`Math.pow`", /write the product out/,
    `export function f(a: number): number { return Math.pow(a, 2); }`,
    `export function f(a: number): number { return a * a; }`],
  ["`.at` on nullable items", /index from the end/,
    `export function f(xs: (number | null)[]): number | null | undefined { return xs.at(-1); }`,
    `export function f(xs: (number | null)[]): number | null | undefined { return xs[xs.length - 1]; }`],
  ["`pop`", /xs\[xs\.length - 1\]/,
    `export function f(s: string): string { return s.split(".").pop() ?? ""; }`,
    `export function f(s: string): string { const parts = s.split("."); return parts[parts.length - 1] ?? ""; }`],
  ["a library type", /instead of the library object `URLSearchParams`/,
    `export function f(q: URLSearchParams): number { return 0; }`,
    `export function f(q: string): number { return q.length; }`],
  ["`concat` of two arrays", /spread instead/,
    `export function f(a: number[], b: number[], c: number[]): number[] { return a.concat(b, c); }`,
    `export function f(a: number[], b: number[], c: number[]): number[] { return [...a, ...b, ...c]; }`],
  ["`reduce` without an initial value", /pass an initial value/,
    `export function f(xs: number[]): number { return xs.reduce((a, b) => a + b); }`,
    `export function f(xs: number[]): number { return xs.reduce((a, b) => a + b, 0); }`],
  ["`for...in`", /`for\.\.\.of`/,
    `export function f(xs: number[]): number { let n = 0; for (const i in xs) n++; return n; }`,
    `export function f(xs: number[]): number { let n = 0; for (const x of xs) n++; return n; }`],
  ["`do...while`", /while \(true\)/,
    `export function f(n: number): number { let i = 0; do { i++; } while (i < n); return i; }`,
    `export function f(n: number): number { let i = 0; while (true) { i++; if (!(i < n)) break; } return i; }`],
  ["`var`", /use `let` or `const`/,
    `export function f(): number { var x = 1; return x; }`,
    `export function f(): number { const x = 1; return x; }`],
  ["rest parameter", /take an array parameter/,
    `export function f(...xs: number[]): number { return xs.length; }`,
    `export function f(xs: number[]): number { return xs.length; }`],
  ["array destructuring", /read the elements by index/,
    `export function f(xs: number[]): number | undefined { const [a] = xs; return a; }`,
    `export function f(xs: number[]): number | undefined { const a = xs[0]; return a; }`],
  ["`+` on a string and a number", /use a template/,
    `export function f(s: string, n: number): string { return s + n; }`,
    "export function f(s: string, n: number): string { return `${s}${n}`; }"],
  ["`join` of numbers", /map to strings first/,
    `export function f(xs: number[]): string { return xs.join(","); }`,
    "export function f(xs: number[]): string { return xs.map(x => `${x}`).join(\",\"); }"],
  ["assignment inside a callback", /`forEach` callback can update an outer variable/,
    `export function f(xs: number[]): number { let n = 0; xs.map(x => { n += x; return x; }); return n; }`,
    `export function f(xs: number[]): number { let n = 0; xs.forEach(x => { n += x; }); return n; }`],
  ["module-level `let`", /declare it `const`/,
    `let k = 1;\nexport function f(): number { return k; }`,
    `const k = 1;\nexport function f(): number { return k; }`],
  ["`===` with a value that may be undefined", /`== null`/,
    `export function f(x: number | null | undefined): boolean { return x === null; }`,
    `export function f(x: number | null | undefined): boolean { return x == null; }`],
  ["`Math.pow` with a higher power", /`a \* a \* a` for `Math.pow\(a, 3\)`/,
    `export function f(a: number): number { return Math.pow(a, 3); }`,
    `export function f(a: number): number { return a * a * a; }`],
  ["the result of `pop`", /`const last = xs\[xs\.length - 1\]; xs\.pop\(\);`/,
    `export function f(xs: number[]): number { const ys = [...xs]; const last = ys.pop(); return last ?? 0; }`,
    `export function f(xs: number[]): number { const ys = [...xs]; const last = ys[ys.length - 1]; ys.pop(); return last ?? 0; }`],
];

for (const [uses, hint, before, after, options] of rewrites) {
  test(`the hint for ${uses} names a rewrite the translator accepts`, () => {
    const reason = failure(before, options);
    assert.ok(reason, `accepted:\n${before}`);
    const [, said] = reason.split(`\n${PREFIX}`);
    assert.ok(said, `no hint in:\n${reason}`);
    assert.match(said, hint);
    assert.equal(failure(after, options), undefined, `the rewrite is refused:\n${after}`);
  });
}

test("a package import gets the `assumes` entry to write", () => {
  const root = join(dir, `p${count++}`);
  mkdirSync(join(root, "node_modules", "lib"), { recursive: true });
  writeFileSync(join(root, "node_modules", "lib", "package.json"), JSON.stringify({ name: "lib", types: "index.d.ts" }));
  writeFileSync(join(root, "node_modules", "lib", "index.d.ts"), "export declare function slug(s: string): string;\n");
  writeFileSync(join(root, "a.ts"), `import { slug } from "lib";\nexport function f(s: string): string { return slug(s); }`);
  const result = translate({ root, module: "M", targets: ["a.ts::f"] });
  assert.match(result.failures["a.ts::f"], /How to fix: list it under `assumes` in proofci\.yaml as `call: lib::slug`, `signature: "\(s: string\): string"`/);
});

test("a reason gets one hint", () => {
  const reason = failure(`export function f(x: any): number { return x; }`);
  assert.equal(reason.split(PREFIX).length, 2);
});
