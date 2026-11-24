import assert from "node:assert/strict";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { after, test } from "node:test";
import { probe } from "./probe.mjs";

const dir = mkdtempSync(join(tmpdir(), "probe-"));
after(() => rmSync(dir, { recursive: true, force: true }));

function runFiles(files) {
  const root = join(dir, `p${Math.random()}`);
  mkdirSync(join(root, "src"), { recursive: true });
  for (const [name, source] of files)
    writeFileSync(join(root, name), source);
  return probe({ root, module: "M" });
}

function run(source) {
  return runFiles([["src/a.ts", source]]);
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

test("a refused function does not hide the functions that translate", () => {
  const { functions, summary } = run(
    "export function good(x: number): number { return x + 1; }\n"
    + "export function bad(x: any): number { return x.y; }\n");
  const good = functions.find(f => f.function.endsWith("::good"));
  const bad = functions.find(f => f.function.endsWith("::bad"));
  assert.equal(good.translated, true);
  assert.equal(bad.translated, false);
  assert.match(bad.reason, /any/);
  assert.equal(bad.code, "type-any");
  assert.deepEqual(summary, { total: 2, translated: 1, refused: 1, by_code: { "type-any": 1 } });
});

test("a refusal in one file does not hide functions in other files", () => {
  const { functions } = runFiles([
    ["src/a.ts", "export function good(x: number): number { return x + 1; }\n"],
    ["src/b.ts", "export function bad(x: any): number { return x.y; }\n"],
  ]);
  const good = functions.find(f => f.function === "src/a.ts::good");
  const bad = functions.find(f => f.function === "src/b.ts::bad");
  assert.equal(good.translated, true);
  assert.equal(bad.translated, false);
  assert.equal(bad.code, "type-any");
});

test("a file that fails to compile refuses its own functions only", () => {
  const { functions } = runFiles([
    ["src/a.ts", "export function good(x: number): number { return x + 1; }\n"],
    ["src/b.ts", "export function bad(x: number): number { return x + ; }\n"],
  ]);
  const good = functions.find(f => f.function === "src/a.ts::good");
  const bad = functions.find(f => f.function === "src/b.ts::bad");
  assert.equal(good.translated, true);
  assert.equal(bad.translated, false);
  assert.equal(bad.code, "compile-error");
});

test("every refusal carries a documented code", () => {
  const { functions } = run(
    "export function bad(x: any): number { return x.y; }\n");
  const bad = functions.find(f => f.function.endsWith("::bad"));
  assert.equal(typeof bad.code, "string");
  assert.match(bad.code, /^[a-z0-9-]+$/);
});

test("renaming the class or parameter does not change the code", () => {
  const variants = [
    "export function bad(db: Db): number { return db.get(); }\nclass Db { get(): number { return 1; } }",
    "export function bad(conn: ConnectionPool): number { return conn.get(); }\nclass ConnectionPool { get(): number { return 1; } }",
  ];
  const codes = variants.map(source =>
    run(source).functions.find(f => f.function.endsWith("::bad")).code);
  assert.deepEqual(codes, ["type-named", "type-named"]);
});

test("a refusal naming a variable still has a stable code", () => {
  const { functions } = run(
    "export function bad(log: number[]): number { log.push(1); return log.length; }\n");
  const bad = functions.find(f => f.function.endsWith("::bad"));
  assert.equal(bad.translated, false);
  assert.equal(bad.code, "in-place-mutation");
});

test("a translator crash on one file refuses only that file's functions", () => {
  const root = join(dir, `crash${Math.random()}`);
  mkdirSync(join(root, "src"), { recursive: true });
  writeFileSync(join(root, "src/a.ts"), "export function good(x: number): number { return x + 1; }\n");
  writeFileSync(join(root, "src/b.ts"), "export function bad(x: number): number { return x; }\n");
  // A crash inside TypeScript (e.g. "Debug Failure: Node must have a real
  // position") escapes translate() as a plain Error — simulate it for src/b.ts.
  const boom = new Error("Debug Failure. False expression: Node must have a real position");
  const failing = opts => {
    if (opts.targets.some(t => t.startsWith("src/b.ts"))) throw boom;
    return { module: "M", failures: {} };
  };
  const { functions, summary } = probe({ root, module: "M", translate: failing });
  const good = functions.find(f => f.function === "src/a.ts::good");
  const bad = functions.find(f => f.function === "src/b.ts::bad");
  assert.equal(good.translated, true);
  assert.equal(bad.translated, false);
  assert.match(bad.reason, /translator crash/);
  assert.equal(bad.code, "translator-crash");
  assert.equal(summary.by_code["translator-crash"], 1);
});
