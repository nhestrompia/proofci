import { after, test } from "node:test";
import assert from "node:assert/strict";

import { generator } from "./differential.mjs";

const hits = (seeds, make) => seeds.map(s => generator(s)(make));

test("generator biases optional toward the nothing value", () => {
  const type = { kind: "optional", inner: { kind: "number" }, nothing: "undefined" };
  const none = hits([...Array(20).keys()], type).filter(v => v === undefined).length;
  assert.ok(none >= 6, `only ${none}/20 generated values were undefined`);
});

test("generator injects hypothesis literals into matching kinds", () => {
  const seeds = [...Array(40).keys()];
  const numbers = hits(seeds, { kind: "number" });
  assert.ok(numbers.every(Number.isSafeInteger));
  const biased = seeds.map(s => generator(s, { numbers: [20], strings: ["admin"] })({ kind: "number" }));
  assert.ok(biased.includes(20), "the `offset = 20` literal never appeared in 40 seeds");
  const strings = seeds.map(s => generator(s, { strings: ["admin"] })({ kind: "string" }));
  assert.ok(strings.includes("admin"), "the `tag = \"admin\"` literal never appeared in 40 seeds");
});

test("generator emits empty arrays sometimes", () => {
  const type = { kind: "array", item: { kind: "number" } };
  assert.ok(hits([...Array(40).keys()], type).some(v => v.length === 0));
});

import { mkdtempSync, mkdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { compile } from "./differential.mjs";

const root = mkdtempSync(join(tmpdir(), "differential-"));
after(() => rmSync(root, { recursive: true, force: true }));
let cases_ = 0;
const project = files => {
  const dir = join(root, `p${cases_++}`);
  for (const [path, text] of Object.entries(files)) {
    mkdirSync(join(dir, path.split("/").slice(0, -1).join("/")), { recursive: true });
    writeFileSync(join(dir, path), text);
  }
  return dir;
};

test("compile emits only the statements the targets reach", () => {
  const dir = project({ "a.ts": `class Boom { constructor() { throw new Error("unrelated") } }
const boom = new Boom();
const STEP = 3;
function helper(a: number): number { return a + STEP; }
export function f(a: number): number { return helper(a); }
export function unrelated(): unknown { return boom; }
` });
  const out = join(dir, "out");
  const reasons = compile(dir, ["a.ts"], {}, out, [], { "a.ts": ["f"] });
  assert.deepEqual(reasons, {});
  const emitted = readFileSync(join(out, "a.mjs"), "utf8");
  assert.ok(!emitted.includes("Boom"), emitted);
  assert.ok(emitted.includes("helper"));
});

test("compile fails closed when what a target needs is not there or is written elsewhere", () => {
  const dir = project({
    "missing.ts": "export function f(): number { return neverDeclared(); }\n",
    "shared.ts": `let s = 0;
s = 1;
export function f(): number { return s; }
` });
  const reasons = compile(dir, ["missing.ts", "shared.ts"], {}, join(dir, "out"), [],
    { "missing.ts": ["f"], "shared.ts": ["f"] });
  assert.match(reasons["missing.ts"], /neverDeclared.*not declared/);
  assert.match(reasons["shared.ts"], /writes `s`/);
});

test("compile keeps a helper imported from another target's file", () => {
  const dir = project({
    "b.ts": `export function helper(x: number): number { return x * 2; }
class Boom { constructor() { throw new Error("x") } }
const b = new Boom();
export function other(): number { return 0; }
`,
    "a.ts": `import { helper } from "./b";
export function target(x: number): number { return helper(x); }
` });
  const reasons = compile(dir, ["a.ts", "b.ts"], { "a.ts": { "./b": join(dir, "b.ts") } }, join(dir, "out"),
    [], { "a.ts": ["target"], "b.ts": ["other"] });
  assert.deepEqual(reasons, {});
  const emitted = readFileSync(join(dir, "out/b.mjs"), "utf8");
  assert.ok(emitted.includes("helper"), emitted);
  assert.ok(!emitted.includes("Boom"), emitted);
});

test("compile keeps constants read in parameter defaults and outside callback scopes", () => {
  const dir = project({
    "c.ts": `const LIMIT = 5;
export function f(n: number = LIMIT): number { return n; }
`,
    "d.ts": `const s = 9;
export function g(cb: (s: number) => number): number { return cb(s); }
` });
  const reasons = compile(dir, ["c.ts", "d.ts"], {}, join(dir, "out"), [], { "c.ts": ["f"], "d.ts": ["g"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/c.mjs"), "utf8").includes("LIMIT"));
  assert.ok(readFileSync(join(dir, "out/d.mjs"), "utf8").includes("const s = 9"));
});

test("a workspace path cannot collide with a same-suffix package path", () => {
  const dir = project({
    "pkg/x.ts": "export function t(): number { return 1; }\n",
    "src/a.ts": "import { t } from '../pkg/x';\nexport function f(): number { return t(); }\n",
  });
  mkdirSync(join(root, "other/pkg"), { recursive: true });
  writeFileSync(join(root, "other/pkg/x.ts"), "export const u = 1;\n");
  const reasons = compile(dir, ["pkg/x.ts", "src/a.ts", "../other/pkg/x.ts"], {}, join(dir, "out"), [],
    { "pkg/x.ts": ["t"], "src/a.ts": ["f"], "../other/pkg/x.ts": ["u"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/pkg/x.mjs"), "utf8").includes("function t"));
  assert.ok(readFileSync(join(dir, "out/__up/other/pkg/x.mjs"), "utf8").includes("const u"));
});
