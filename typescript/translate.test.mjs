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
  emits("export function f(a: number | null) { if (a === null) return 0; return a; }", "match a with", "| some a =>");
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
    ["export function f(a: number[]) { return 1; }", /not supported/],
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

test("mutation is rejected until the ownership check exists", () => {
  rejects("export function f(a: number) { a = 1; return a; }", /assignment/);
  rejects("export function f(a: number) { let b = 0; b += a; return b; }", /assignment/);
  rejects("export function f(a: number) { let b = 0; b++; return b; }", /assignment/);
  rejects("interface A { x: number } export function f(a: A) { a.x = 1; return a; }", /assignment/);
  rejects("export function f(a: number) { var b = a; return b; }", /var/);
});

test("control flow that needs joins or loops is rejected", () => {
  rejects("export function f(a: number) { for (;;) { return a; } }", /not supported/);
  rejects("export function f(a: number) { if (a > 0) { const b = 1; } return a; }", /neither branch/);
  rejects("export function f(a: number): number { return f(a); }", /recursion/);
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
