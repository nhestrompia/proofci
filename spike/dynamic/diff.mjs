// Runs the dynamic translation against Node on random inputs drawn from the TypeScript types.
// Writes Diff.lean (one `#eval` per case); `node diff.mjs check <lean output>` compares.
//   node diff.mjs gen [cases]      then run Diff.lean in the image, then
//   node diff.mjs check out.txt
import { createRequire } from "node:module";
import fs from "node:fs";
import path from "node:path";
import { translate } from "./dyn.mjs";

const require = createRequire(new URL("../../typescript/package.json", import.meta.url));
const ts = require("typescript");
const here = path.dirname(new URL(import.meta.url).pathname);
const C = process.env.CORPUS ?? `${process.env.HOME}/corpus`;
const A = `${C}/AppFlowy-Web/src/application/database-yjs`;

export const TARGETS = [
  ["Unknown", `${A}/chart-extended-settings.ts`, ["parseChartGroupByFieldId", "parseChartDecimalPlaces"]],
  ["Union", `${A}/dashboard-private.ts`, ["isDashboardPrivateKeyOfUser", "dashboardPrivateStorageKey"]],
  ["Alias", `${C}/continue/core/llm/messages.ts`, ["addSpaceToAnyEmptyMessages", "messageIsEmpty"]],
  ["Closure", `${C}/continue/core/util/messageContent.ts`, ["renderContextItemsWithStatus"]],
  ["Budget", `${A}/fields/formula/budget.ts`, ["FormulaEvaluationBudget.new", "FormulaEvaluationBudget.consume", "FormulaEvaluationBudget.consumeRegex"]],
  ["Slideshow", `${C}/immich/web/src/lib/utils/slideshow-history.ts`, ["SlideshowHistory.reset", "SlideshowHistory.queue"]],
  ["Fixtures", `${here}/fixtures.ts`, ["colorIndexes", "bumpBoth", "Counter.bump"]],
  ["Bank", `${here}/../../examples/ts-bank/src/ledger.ts`, ["calculateFee", "transfer", "sumAmounts"]],
];

let seed = 12345;
const rnd = () => ((seed = (seed * 1103515245 + 12345) % 2147483648) / 2147483648);
const pick = (xs) => xs[Math.floor(rnd() * xs.length)];

const NUMS = [0, 1, 2, 3, 4, 5, 6, -1, -3, 10, 100, 1.5, -0, NaN, 2 ** 53 + 2];

class Gen {
  constructor(d, strings) { this.d = d; this.c = d.checker; this.strings = [...strings, "", " ", "  ", "a", "x:y", "text", "list", "😀", "a😀:b"]; this.made = []; this.classes = {}; }
  str() {
    const r = rnd();
    if (r < 0.15) return Array.from({ length: 4 }, () => pick([...this.strings, String(pick([0, 1, 7]))])).join(":");
    if (r < 0.6) return pick(this.strings);
    return Array.from({ length: Math.floor(rnd() * 4) }, () => pick("ab :\n")).join("");
  }
  any(depth = 0) {
    const r = rnd();
    if (r < 0.1) return undefined;
    if (r < 0.15) return null;
    if (r < 0.25) return rnd() < 0.5;
    if (r < 0.45) return pick(NUMS);
    if (r < 0.65) return this.str();
    if (r < 0.75) return pick([0n, 3n, -2n, 2n ** 60n]);
    if (depth > 1) return 0;
    if (r < 0.87) return Array.from({ length: Math.floor(rnd() * 3) }, () => this.any(depth + 1));
    return { content: this.any(depth + 1), status: this.any(depth + 1), type: pick(["text", "list", "x"]), text: this.any(depth + 1) };
  }
  of(t, node, depth = 0) {
    const F = ts.TypeFlags, c = this.c;
    if (t.flags & (F.Any | F.Unknown) || depth > 3) return this.any(depth);
    if (t.isUnion()) return this.of(pick(t.types), node, depth);
    if (t.flags & (F.Undefined | F.Void)) return undefined;
    if (t.flags & F.Null) return null;
    if (t.flags & F.BooleanLiteral) return c.typeToString(t) === "true";
    if (t.flags & F.Boolean) return rnd() < 0.5;
    if (t.flags & F.StringLiteral) return t.value;
    if (t.flags & F.String) return this.str();
    if (t.flags & F.NumberLiteral) return t.value;
    if (t.flags & F.Number) return pick(NUMS);
    if (c.isArrayType(t)) return Array.from({ length: Math.floor(rnd() * 4) }, () => this.share(c.getTypeArguments(t)[0], node, depth + 1));
    if (t.flags & F.Object) {
      if (t.getCallSignatures().length) return function cb() {};
      const sym = t.getSymbol();
      const o = sym && sym.flags & ts.SymbolFlags.Class ? Object.create(this.classes[sym.name]?.prototype ?? Object.prototype) : {};
      for (const p of t.getProperties()) {
        if (p.flags & ts.SymbolFlags.Method) continue;
        const pt = c.getTypeOfSymbolAtLocation(p, node);
        const x = this.of(pt, node, depth + 1);
        if (x !== undefined || !(p.flags & ts.SymbolFlags.Optional)) o[p.name] = x;
      }
      return o;
    }
    throw new Error(`no generator for ${c.typeToString(t)}`);
  }
  // Objects are sometimes reused, so inputs share structure.
  share(t, node, depth) {
    const fits = this.made.filter((m) => m.t === t);
    if (fits.length && rnd() < 0.3) return pick(fits).v;
    const v = this.of(t, node, depth);
    if (v && typeof v === "object") this.made.push({ t, v });
    return v;
  }
}

// --- JavaScript values to Lean terms, and both sides printed the same way

function bits(x) { const b = new DataView(new ArrayBuffer(8)); b.setFloat64(0, x); return b.getBigUint64(0); }
function encode(vals) {
  const heap = [], seen = new Map();
  const enc = (x) => {
    if (x === undefined) return ".undef";
    if (x === null) return ".null";
    if (typeof x === "boolean") return `(.bool ${x})`;
    if (typeof x === "number") return `(.num (F64.ofBits ${bits(x)}))`;
    if (typeof x === "bigint") return `(.big (${x}))`;
    if (typeof x === "string") return `(str ${JSON.stringify(x)})`;
    if (typeof x === "function") return `(.fn "f" .undef)`;
    if (seen.has(x)) return `(.ref ${seen.get(x)})`;
    const l = heap.length; seen.set(x, l); heap.push(null);
    if (Array.isArray(x)) heap[l] = `.array [${x.map(enc).join(", ")}]`;
    else {
      const fsx = Object.keys(x).map((k) => { if (k.startsWith("__class")) throw new Error("reserved"); return `(${JSON.stringify(k)}, ${enc(x[k])})`; });
      const proto = Object.getPrototypeOf(x);
      if (proto !== Object.prototype) fsx.unshift(`("__class", str ${JSON.stringify(proto.constructor.name)})`);
      heap[l] = `.record [${fsx.join(", ")}]`;
    }
    return `(.ref ${l})`;
  };
  const vs = vals.map(enc);
  return { vs, heap: `[${heap.join(", ")}]` };
}
export function show(x, d = 50) {
  if (d === 0) return "?";
  if (x === undefined) return "undefined";
  if (x === null) return "null";
  if (typeof x === "boolean") return String(x);
  if (typeof x === "function") return "fn";
  if (typeof x === "number") return Number.isNaN(x) ? "NaN" : `#${bits(x)}`;
  if (typeof x === "bigint") return `${x}n`;
  if (typeof x === "string") return `s[${[...Array(x.length).keys()].map((i) => x.charCodeAt(i)).join(",")}]`;
  if (Array.isArray(x)) return `[${x.map((y) => show(y, d - 1)).join(",")}]`;
  return `{${Object.keys(x).sort().map((k) => `${k}:${show(x[k], d - 1)}`).join(",")}}`;
}

function nodeSide(d) {
  const src = [...[...d.consts].map(([k, v]) => `const ${k} = ${v};`), ...d.js.values()].join("\n");
  const js = ts.transpileModule(src.replace(/^export /gm, ""), { compilerOptions: { target: ts.ScriptTarget.ES2022, useDefineForClassFields: true } }).outputText;
  const names = [...d.js.keys()];
  return new Function(`${js}\nreturn { ${names.join(", ")} };`)();
}

function cases(n) {
  const out = [];
  for (const [ns, file, names] of TARGETS) {
    const d = translate(file, names.map((x) => x.split(".")[0]));
    const mod = nodeSide(d);
    const g = new Gen(d, d.strings);
    for (const [k, v] of Object.entries(mod)) if (typeof v === "function" && /^class /.test(v.toString())) g.classes[k] = v;
    const sf = d.prog.getSourceFile(file);
    for (const name of names) {
      const [top, member] = name.split(".");
      let decl;
      sf.forEachChild((s) => { if (s.name?.text === top) decl = s; });
      const target = member === "new" ? decl.members.find(ts.isConstructorDeclaration) : member ? decl.members.find((m) => m.name?.text === member) : decl;
      const params = target?.parameters ?? [];
      const selfType = member && member !== "new" ? d.checker.getTypeAtLocation(decl) : null;
      for (let i = 0; i < n; i++) {
        g.made = [];
        const args = params.map((p) => g.share(d.checker.getTypeAtLocation(p), p, 0));
        const self = selfType ? g.of(d.checker.getDeclaredTypeOfSymbol(d.checker.getSymbolAtLocation(decl.name)), decl, 0) : null;
        const all = self ? [self, ...args] : args;
        const { vs, heap } = encode(all);
        let expect;
        try {
          const copy = structuredCloneKeep(all, g.classes);
          const r = member === "new" ? new mod[top](...copy) : member ? mod[top].prototype[member].apply(copy[0], copy.slice(1)) : mod[top](...copy);
          expect = `${show(r)}|${copy.map((x) => show(x)).join("|")}`;
        } catch {
          expect = `throw`;
        }
        const call = member === "new" ? `${ns}.${top}.new` : member ? `${ns}.${top}.${member}` : `${ns}.${top}`;
        const pre = member ? "true" : `decide (${ns}.${top}.pre ${vs.join(" ")} h)`;
        out.push({ id: `${ns}.${name}#${i}`, expect, lean: `#eval let h : Heap := ${heap}; IO.println ("${ns}.${name}#${i} " ++ toString (${pre}) ++ " " ++ report (${call} ${vs.join(" ")} h) [${vs.join(", ")}])` });
      }
    }
  }
  return out;
}

// A deep copy that keeps sharing and class prototypes, so Node runs on the inputs Lean got.
function structuredCloneKeep(vals, classes) {
  const m = new Map();
  const cp = (x) => {
    if (!x || typeof x !== "object") return x;
    if (m.has(x)) return m.get(x);
    const y = Array.isArray(x) ? [] : Object.create(Object.getPrototypeOf(x));
    m.set(x, y);
    for (const k of Object.keys(x)) y[k] = cp(x[k]);
    return y;
  };
  return vals.map(cp);
}

const [mode, arg] = process.argv.slice(2);
if (mode === "gen") {
  const cs = cases(Number(arg ?? 100));
  fs.writeFileSync(path.join(here, "Diff.lean"), `import Gen.Unknown\nimport Gen.Union\nimport Gen.Alias\nimport Gen.Closure\nimport Gen.Budget\nimport Gen.Slideshow\nimport Gen.Fixtures\nimport Gen.Bank\nopen Core Dyn\n\n${cs.map((c) => c.lean).join("\n")}\n`);
  fs.writeFileSync(path.join(here, "diff-expected.json"), JSON.stringify(cs.map(({ id, expect }) => ({ id, expect }))));
  console.log(`${cs.length} cases`);
} else if (mode === "check") {
  const exp = JSON.parse(fs.readFileSync(path.join(here, "diff-expected.json"), "utf8"));
  const got = new Map(fs.readFileSync(arg, "utf8").split("\n").filter((l) => l.includes("#")).map((l) => { const [id, pre, ...r] = l.split(" "); return [id, { pre, out: r.join(" ") }]; }));
  const stats = {};
  let bad = 0;
  for (const { id, expect } of exp) {
    const fn = id.split("#")[0];
    const s = (stats[fn] ??= { same: 0, stuck: 0, pre: 0 });
    const g = got.get(id);
    if (!g) { console.log(`missing ${id}`); bad++; continue; }
    if (g.pre !== "true") { s.pre++; console.log(`precondition false: ${id}`); bad++; }
    if (g.out === "stuck") s.stuck++;
    else if (g.out === expect || (g.out.startsWith("throw") && expect === "throw")) s.same++;
    else { bad++; console.log(`DIFF ${id}\n  lean ${g.out}\n  node ${expect}`); }
  }
  for (const [fn, s] of Object.entries(stats)) console.log(`${fn}: ${s.same} same, ${s.stuck} stuck`);
  process.exit(bad ? 1 : 0);
}
