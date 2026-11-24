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
  // A write to a kept name is kept, never dropped: the emitted module reproduces
  // the real state (s === 1).
  assert.equal(reasons["shared.ts"], undefined);
  assert.ok(readFileSync(join(dir, "out/shared.mjs"), "utf8").includes("s = 1"));
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

test("an aliased re-export seeds the source name, not the public name", () => {
  const dir = project({
    "b.ts": `export function orig(x: number): number { return x + 1; }
export function boom(): number { return 0; }
`,
    "a.ts": `export { orig as pub } from "./b";
export function local(x: number): number { return x; }
`,
    "c.ts": `import { pub } from "./a";
export function t(x: number): number { return pub(x); }
` });
  const imports = { "a.ts": { "./b": join(dir, "b.ts") }, "c.ts": { "./a": join(dir, "a.ts") } };
  const reasons = compile(dir, ["a.ts", "b.ts", "c.ts"], imports, join(dir, "out"), [],
    { "a.ts": ["local"], "b.ts": ["boom"], "c.ts": ["t"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/b.mjs"), "utf8").includes("orig"));
});

test("an unused sibling import cannot pull a crashing initializer back", () => {
  const dir = project({
    "b.ts": `export function helper(x: number): number { return x + 1; }
export const boom = (() => { throw new Error("x") })();
`,
    "a.ts": `import { helper, boom } from "./b";
export function t(x: number): number { return helper(x); }
` });
  const reasons = compile(dir, ["a.ts", "b.ts"], { "a.ts": { "./b": join(dir, "b.ts") } }, join(dir, "out"), [],
    { "a.ts": ["t"], "b.ts": ["helper"] });
  assert.deepEqual(reasons, {});
  assert.ok(!readFileSync(join(dir, "out/b.mjs"), "utf8").includes("boom"));
});

// A dropped top-level statement can change what the kept code sees without
// assigning to it — each of these must run in the emitted module, exactly as
// real JavaScript runs it (pilot review: soundness of `isolate`).
const touches = {
  "push": `const TABLE: number[] = [];
TABLE.push(1);
export function t(): number { return TABLE.length; }`,
  "freeze": `const CONFIG = { a: 1 };
Object.freeze(CONFIG);
export function t(): number { return CONFIG.a; }`,
  "property write": `const LIMITS = { max: 0 };
LIMITS.max = 5;
export function t(): number { return LIMITS.max; }`,
  "map set": `const registry = new Map<string, number>();
const K = "k";
registry.set(K, 2);
export function t(): number { return registry.get(K) ?? -1; }`,
};
for (const [what, text] of Object.entries(touches)) {
  test(`a top-level ${what} on a kept name is never dropped`, () => {
    const dir = project({ "a.ts": text });
    const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
    assert.deepEqual(reasons, {});
  });
}

test("a kept mutation makes Node see what real JavaScript sees", async () => {
  const dir = project({
    "a.ts": `const TABLE: number[] = [];
TABLE.push(1);
export function t(): number { return TABLE.length; }
`,
  });
  compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
  const { t } = await import(join(dir, "out/a.mjs"));
  assert.equal(t(), 1); // naive isolation would drop the push and see 0
});

test("a literal __up directory cannot collide with an escaped .. path", () => {
  const dir = project({
    "x.ts": `export function a(): number { return 1; }`,
    "__up/x.ts": `export function b(): number { return 2; }`,
    "../x.ts": `export function c(): number { return 3; }`,
  });
  // A workspace file resolved above root and a real directory named __up must
  // emit to different paths, both inside out/.
  const reasons = compile(dir, ["x.ts", "__up/x.ts", "../x.ts"], {}, join(dir, "out"), [],
    { "x.ts": ["a"], "__up/x.ts": ["b"], "../x.ts": ["c"] });
  assert.deepEqual(reasons, {});
  const out = join(dir, "out");
  assert.ok(readFileSync(join(out, "__up__up/x.mjs"), "utf8").includes("function b"));
  assert.ok(readFileSync(join(out, "__up/x.mjs"), "utf8").includes("function c"));
});

// Pilot regression: t3code — an unrelated `Schema.TaggedError` class in the same
// module must not crash the comparison of a pure target.
test("pilot: an unrelated Schema-like class in the same module never runs", () => {
  const dir = project({
    "a.ts": `class TaggedError extends (() => { throw new Error("schema init") })() {}
export function double(x: number): number { return x * 2; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["double"] });
  assert.deepEqual(reasons, {});
  assert.ok(!readFileSync(join(dir, "out/a.mjs"), "utf8").includes("TaggedError"));
});

// Pilot regression: t3code — a constant imported from another workspace package
// (resolved above the package root) is emitted inside out/ and stays importable.
test("pilot: a constant imported across a workspace package boundary is kept", () => {
  const dir = project({
    "pkg/src/t.ts": `import { SINCE } from "../../shared/src/consts";
export function gate(v: number): number { return v >= SINCE ? 1 : 0; }
`,
    "../shared/src/consts.ts": `export const SINCE: number = 3;
`,
  });
  const imports = { "pkg/src/t.ts": { "../../shared/src/consts": join(dir, "../shared/src/consts.ts") } };
  const reasons = compile(dir, ["pkg/src/t.ts", "../shared/src/consts.ts"], imports, join(dir, "out"), [],
    { "pkg/src/t.ts": ["gate"], "../shared/src/consts.ts": ["SINCE"] });
  assert.deepEqual(reasons, {});
  const emitted = readFileSync(join(dir, "out/__up/shared/src/consts.mjs"), "utf8");
  assert.ok(emitted.includes("SINCE"));
  // The rewritten specifier must resolve to a file inside out/.
  const t = readFileSync(join(dir, "out/pkg/src/t.mjs"), "utf8");
  const spec = t.match(/from "([^"]+)"/)?.[1];
  assert.ok(spec, `no import specifier in ${t}`);
  const resolved = join(dir, "out/pkg/src", spec);
  assert.ok(resolved.startsWith(join(dir, "out")), `import escapes out/: ${resolved}`);
  assert.equal(readFileSync(resolved, "utf8"), emitted);
});

test("a side-effect statement is kept even when the worklist ends on a global", () => {
  const dir = project({
    "a.ts": `const TABLE: number[] = [];
TABLE.push(Math.max(1, 2));
export function t(): number { return TABLE.length; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
  assert.deepEqual(reasons, {});
  const emitted = readFileSync(join(dir, "out/a.mjs"), "utf8");
  assert.ok(emitted.includes("push"), emitted);
});

test("a never-called function body cannot keep its reads alive", () => {
  const dir = project({
    "a.ts": `const TABLE: number[] = [];
function unused(): string { return TABLE[0] + document.title; }
export function t(): number { return TABLE.length; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
  assert.deepEqual(reasons, {});
  assert.ok(!readFileSync(join(dir, "out/a.mjs"), "utf8").includes("unused"));
});

test("a kept import that feeds a local re-export still reaches the source module", () => {
  const dir = project({
    "b.ts": `export function helper(x: number): number { return x + 1; }`,
    "a.ts": `import { helper } from "./b";
export { helper };
export function t(x: number): number { return helper(x); }
` });
  const reasons = compile(dir, ["a.ts", "b.ts"], { "a.ts": { "./b": join(dir, "b.ts") } }, join(dir, "out"), [],
    { "a.ts": ["t"], "b.ts": ["helper"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/b.mjs"), "utf8").includes("helper"));
});

test("an export alias keeps the declaration it re-exports", () => {
  const dir = project({
    "a.ts": `function internal(): number { return 7; }
export { internal as pub };
export function t(): number { return 1; }
` });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t", "pub"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/a.mjs"), "utf8").includes("internal"));
});

test("static class initialization touching a kept name runs", () => {
  const dir = project({
    "a.ts": `const TABLE: number[] = [];
class C { static n = TABLE.push(1); }
export function t(): number { return TABLE.length; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/a.mjs"), "utf8").includes("static n"));
});

test("a computed class member name touching a kept name runs", () => {
  const dir = project({
    "a.ts": `const KEYS = { m: "seen" };
class C { [KEYS.m]() { return 1; } }
export function t(): string { return KEYS.m; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/a.mjs"), "utf8").includes("[KEYS.m]"));
});

test("a static initializer that writes a module variable keeps its declaration", () => {
  const dir = project({
    "a.ts": `let MOD: number;
const TABLE: number[] = [];
class C { static x = (TABLE.push(1), MOD = 7); }
export function t(): number { return TABLE.length + MOD; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/a.mjs"), "utf8").includes("let MOD"));
});

test("a computed method name is evaluated in the enclosing scope, not the method's", () => {
  const dir = project({
    "a.ts": `const x = "m";
class C { [x](x: number) { return x; } }
export function t(): string { return x; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/a.mjs"), "utf8").includes("const x"));
});

test("a class's own name inside its body never means an outer declaration", () => {
  const dir = project({
    "a.ts": `const C = class C { static s = C.y; static y = 1; };
const TABLE: number[] = [];
export function t(): number { return TABLE.length; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["t"] });
  assert.deepEqual(reasons, {});
  assert.ok(!readFileSync(join(dir, "out/a.mjs"), "utf8").includes("class C"));
});

test("a call to a module function that mutates a kept name is kept", () => {
  const dir = project({
    "a.ts": `const TABLE: number[] = [];
function init(): void { TABLE.push(1); }
init();
export function f(): number { return TABLE.length; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["f"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/a.mjs"), "utf8").includes("init()"));
});

test("a binding statement calling a module function that mutates a kept name is kept", () => {
  const dir = project({
    "a.ts": `const TABLE: number[] = [];
function init(): number { TABLE.push(1); return 1; }
const ready = init();
export function f(): number { return TABLE.length; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["f"] });
  assert.deepEqual(reasons, {});
  assert.ok(readFileSync(join(dir, "out/a.mjs"), "utf8").includes("init()"));
});

test("transitive: init -> fill -> TABLE.push is kept", () => {
  const dir = project({
    "a.ts": `const TABLE: number[] = [];
function fill(): void { TABLE.push(1); }
function init(): void { fill(); }
init();
export function f(): number { return TABLE.length; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["f"] });
  assert.deepEqual(reasons, {});
  const emitted = readFileSync(join(dir, "out/a.mjs"), "utf8");
  assert.ok(emitted.includes("init()"), emitted);
});

test("a property read of a module callable does not expand its body", () => {
  const dir = project({
    "a.ts": `const TABLE: number[] = [];
class Handler { static { throw new Error("init") } m(): number { return TABLE[0]; } }
const label = Handler.name;
export function f(): number { return TABLE.length; }
`,
  });
  const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["f"] });
  assert.deepEqual(reasons, {});
  assert.ok(!readFileSync(join(dir, "out/a.mjs"), "utf8").includes("class Handler"));
});

test("indirect invocations still count as calls: (init)(), init.call, forEach(init)", () => {
  for (const site of ["(init)();", "init.call(undefined);", "[0].forEach(init);"]) {
    const dir = project({
      "a.ts": `const TABLE: number[] = [];
function init(): void { TABLE.push(1); }
${site}
export function f(): number { return TABLE.length; }
`,
    });
    const reasons = compile(dir, ["a.ts"], {}, join(dir, "out"), [], { "a.ts": ["f"] });
    assert.deepEqual(reasons, {}, site);
    assert.ok(readFileSync(join(dir, "out/a.mjs"), "utf8").includes("function init"), site);
  }
});
