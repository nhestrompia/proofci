// Runs translated functions in Node on generated inputs and writes a Lean file
// that replays them against the model. The two must agree wherever the model
// returns a value. A disagreement means the translator or the runtime is wrong.
//
// Usage: node differential.mjs <config.json>
//   config: { root, out, module, signatures, files, imports, cases }

import { mkdirSync, readFileSync, realpathSync, writeFileSync } from "node:fs";
import { dirname, join, posix, relative } from "node:path";
import { pathToFileURL } from "node:url";
import ts from "typescript";

const MAX = Number.MAX_SAFE_INTEGER;
const EDGES = [0, 1, -1, 2, -2, 3, 7, 10, -10, 100, 500, 1000, 9999, 10000, 10001, 94906265, 94906266, 2 ** 31, 2 ** 32, 2 ** 52, MAX - 1, MAX, -MAX];

const TEXTS = ["", "a", "b", "abc", " x ", "A-b", "a,b,c", ",", ",,", "Hello World", "é", "😀", "a😀b", "\ud800", "ÄB", "\t\n", "12", "$&"];

export function generator(seed) {
  let state = seed >>> 0;
  const next = () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const pick = list => list[Math.floor(next() * list.length)];
  const number = () => {
    const shape = next();
    if (shape < 0.45) return Math.floor(next() * 2001) - 1000;
    if (shape < 0.75) return pick(EDGES);
    if (shape < 0.9) return Math.floor(next() * 200_000_001) - 100_000_000;
    return Math.floor((next() - 0.5) * 2 * MAX);
  };
  const value = type => {
    switch (type.kind) {
      case "number": return number();
      case "boolean": return next() < 0.5;
      case "bigint": return BigInt(number()) * (next() < 0.2 ? 1000000007n : 1n);
      case "void": return undefined;
      case "generic": return number();
      case "string": return pick(TEXTS);
      case "map": return new Map(Array.from({ length: Math.floor(next() * 5) }, () => [value(type.key), value(type.value)]));
      case "set": return new Set(Array.from({ length: Math.floor(next() * 5) }, () => value(type.item)));
      case "array": return Array.from({ length: Math.floor(next() * 7) }, () => value(type.item));
      case "optional": return next() < 0.3 ? (type.nothing === "null" ? null : undefined) : value(type.inner);
      case "enum": return pick(type.tags).tag;
      case "record": return Object.fromEntries(type.fields.map(f => [f.name, value(f.type)]));
      case "tagged": {
        const variant = pick(type.variants);
        return { kind: variant.tag, ...Object.fromEntries(variant.fields.map(f => [f.name, value(f.type)])) };
      }
      default: throw new Error(`no generator for ${type.kind}`);
    }
  };
  return value;
}

// The Lean spelling of a JavaScript value, or undefined if it isn't of `type`.
export function term(type, value) {
  switch (type.kind) {
    case "number":
      if (!Number.isSafeInteger(value)) return undefined;
      return `(Js.lit (${value === 0 ? 0 : value}))`;
    case "boolean":
      return typeof value === "boolean" ? String(value) : undefined;
    case "bigint":
      return typeof value === "bigint" ? `(${value} : Int)` : undefined;
    case "void":
      return value === undefined ? "()" : undefined;
    case "string": {
      if (typeof value !== "string") return undefined;
      const units = Array.from({ length: value.length }, (_, i) => value.charCodeAt(i));
      return `([${units.join(", ")}] : Js.Str)`;
    }
    case "map": {
      if (!(value instanceof Map)) return undefined;
      const parts = [...value].map(([k, v]) => [term(type.key, k), term(type.value, v)]);
      return parts.flat().includes(undefined) ? undefined : `[${parts.map(([k, v]) => `(${k}, ${v})`).join(", ")}]`;
    }
    case "set": {
      if (!(value instanceof Set)) return undefined;
      const parts = [...value].map(item => term(type.item, item));
      return parts.includes(undefined) ? undefined : `[${parts.join(", ")}]`;
    }
    case "array": {
      if (!Array.isArray(value)) return undefined;
      const parts = value.map(item => term(type.item, item));
      return parts.includes(undefined) ? undefined : `[${parts.join(", ")}]`;
    }
    case "optional": {
      if (value === (type.nothing === "null" ? null : undefined) || (type.both && value == null)) return "none";
      const inner = term(type.inner, value);
      return inner === undefined ? undefined : `(some ${inner})`;
    }
    case "enum": {
      const tag = type.tags.find(t => t.tag === value);
      return tag ? `_root_.${type.lean}.${tag.lean}` : undefined;
    }
    case "record": {
      if (typeof value !== "object" || value === null) return undefined;
      const parts = type.fields.map(f => term(f.type, value[f.name]));
      if (parts.includes(undefined)) return undefined;
      return `(_root_.${type.lean}.mk ${parts.join(" ")})`;
    }
    case "tagged": {
      if (typeof value !== "object" || value === null) return undefined;
      const variant = type.variants.find(v => v.tag === value.kind);
      if (!variant) return undefined;
      const parts = variant.fields.map(f => term(f.type, value[f.name]));
      if (parts.includes(undefined)) return undefined;
      return `(_root_.${type.lean}.${variant.lean} ${parts.join(" ")})`;
    }
    default: return undefined;
  }
}

const show = value => JSON.stringify(value, (_, v) => {
  if (typeof v === "bigint") return `${v}n`;
  if (v instanceof Map || v instanceof Set) return [...v];
  return v;
});

// Stands in for code the targets don't reach. Those modules may only be loaded by
// something else in the file, so a stand-in has to survive any use at load time.
const STAND_IN = `const stub = new Proxy(function () {}, {
  get: (_, key) => (key === Symbol.toPrimitive ? () => 0 : stub),
  apply: () => stub,
  construct: () => stub,
});
export default stub;
`;

const module_ = file => file.replace(/\.tsx?$/, ".mjs");

function importedNames(statement) {
  const names = new Set();
  const bindings = ts.isImportDeclaration(statement) ? statement.importClause?.namedBindings : statement.exportClause;
  if (bindings && (ts.isNamedImports(bindings) || ts.isNamedExports(bindings))) {
    for (const element of bindings.elements) names.add((element.propertyName ?? element.name).text);
  }
  names.delete("default");
  return [...names];
}

// Files reached by a target run for real. Anything else they import is replaced,
// so the comparison runs only code that was translated, and doesn't depend on
// packages being installed.
export function compile(root, files, imports, out, effects = []) {
  const realRoot = realpathSync(root);
  // An outside call is replaced by a stand-in that asks the test's world, wherever it is declared.
  const byName = new Map(effects.map(e => [e.call.split("::").at(-1), e]));
  const asksWorld = (name, e) => `export function ${name}(...args) { return globalThis.__proofciWorld(${JSON.stringify(e.id)}, args); }\n`;
  const reached = new Set(files);
  // A package's index can re-export a value from a file the translation reached. Such a name
  // is real, so it comes from that file, and only the rest are stubbed.
  const exported = new Map();
  for (const file of files) {
    const source = ts.createSourceFile(file, readFileSync(join(root, file), "utf8"), ts.ScriptTarget.ES2022, true);
    for (const statement of source.statements) {
      if (!ts.getModifiers?.(statement)?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) continue;
      if (ts.isVariableStatement(statement)) {
        for (const d of statement.declarationList.declarations) if (ts.isIdentifier(d.name)) exported.set(d.name.text, file);
      } else if (ts.isFunctionDeclaration(statement) && statement.name) exported.set(statement.name.text, file);
    }
  }
  let stubs = 0;
  for (const file of files) {
    let js = ts.transpileModule(readFileSync(join(root, file), "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, jsx: ts.JsxEmit.React },
    }).outputText;
    // A project function listed as an effect is never run: its declaration is replaced.
    for (const e of effects) {
      const [where, fn] = e.call.split("::");
      if (where !== file) continue;
      const found = ts.createSourceFile("out.mjs", js, ts.ScriptTarget.ES2022, true);
      for (const statement of [...found.statements].reverse()) {
        const declared = ts.isFunctionDeclaration(statement) ? statement.name?.text
          : ts.isVariableStatement(statement) ? statement.declarationList.declarations.map(d => d.name.getText())[0] : undefined;
        if (declared !== fn) continue;
        js = `${js.slice(0, statement.getStart(found))}${asksWorld(fn, e)}${js.slice(statement.end)}`;
      }
    }
    const parsed = ts.createSourceFile("out.mjs", js, ts.ScriptTarget.ES2022, true);
    const path = join(out, module_(file));
    mkdirSync(dirname(path), { recursive: true });
    let rewritten = js;
    const statements = parsed.statements.filter(s => s.moduleSpecifier).reverse();
    for (const statement of statements) {
      const specifier = statement.moduleSpecifier;
      const resolved = imports[file]?.[specifier.text];
      const target = resolved && relative(realRoot, resolved);
      let replacement;
      if (target && reached.has(target)) {
        replacement = posix.relative(dirname(module_(file)), module_(target));
      } else {
        const stub = `__stand_in_${stubs += 1}.mjs`;
        writeFileSync(join(out, stub), STAND_IN + importedNames(statement).map(n => byName.has(n)
          ? asksWorld(n, byName.get(n))
          : exported.has(n)
          ? `export { ${n} } from ${JSON.stringify(`./${module_(exported.get(n))}`)};\n`
          : `export { stub as ${n} };\n`).join(""));
        replacement = posix.relative(dirname(module_(file)), stub);
      }
      if (!replacement.startsWith(".")) replacement = `./${replacement}`;
      rewritten = `${rewritten.slice(0, specifier.getStart(parsed))}${JSON.stringify(replacement)}${rewritten.slice(specifier.end)}`;
    }
    writeFileSync(path, rewritten);
  }
}

// A small deterministic generator for the world's behaviour: delays and which calls are rejected.
function chance(seed) {
  let state = seed >>> 0;
  return () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const MESSAGES = ["boom", "", "database down", "x y"];
// A rejection is an Error, or sometimes one of the built-in subclasses code tells apart with `instanceof`.
const ERRORS = ["Error", "Error", "TypeError", "RangeError"];
const text = value => `([${Array.from({ length: value.length }, (_, i) => value.charCodeAt(i)).join(", ")}] : Js.Str)`;

// Answers from a database are often empty or missing in the way that matters: an empty string is falsy
// but present. Random values rarely reach that, so some strings in an answer are emptied.
function emptied(type, value, random) {
  switch (type.kind) {
    case "string": return random() < 0.25 ? "" : value;
    case "array": return value.map(item => emptied(type.item, item, random));
    case "optional": return value == null ? value : emptied(type.inner, value, random);
    case "record": return Object.fromEntries(type.fields.map(f => [f.name, emptied(f.type, value[f.name], random)]));
    default: return value;
  }
}

// Runs an async function in Node against stand-ins for its outside calls. Each call is answered
// from a random script (a value of the declared type, or a rejection), after a random number of
// turns of the event loop, so the real scheduler is exercised. Returns what happened.
export async function runAsync(fn, inputs, effects, seed) {
  const random = chance(seed);
  const value = generator(seed + 7919);
  const trace = [];
  globalThis.__proofciWorld = (id, args) => new Promise((resolve, reject) => {
    const effect = effects.find(e => e.id === id);
    const answer = random() < 0.2
      ? { reject: MESSAGES[Math.floor(random() * MESSAGES.length)], kind: ERRORS[Math.floor(random() * ERRORS.length)] }
      : { value: emptied(effect.returns, value(effect.returns), random) };
    trace.push({ id, args: effect.params.map((_, i) => args[i]), answer });
    const settle = () => (answer.reject !== undefined ? reject(new globalThis[answer.kind](answer.reject)) : resolve(answer.value));
    const turns = Math.floor(random() * 3);
    if (turns === 0) queueMicrotask(settle); else setTimeout(settle, turns - 1);
  });
  let outcome;
  try {
    outcome = { value: await fn(...inputs) };
  } catch (error) {
    outcome = { error };
  }
  delete globalThis.__proofciWorld;
  return { outcome, trace };
}

// The oracle that replays Node's answers, and the check that the model asked the same questions.
function replay(trace, effects) {
  const op = id => `Proofci.Effects.Op.${effects.find(e => e.id === id).lean}`;
  const answer = (effect, a) => (a.reject !== undefined
    ? `Js.Answer.reject ⟨${text(a.kind)}, ${text(a.reject)}⟩`
    : `Js.Answer.value ${term(effect.returns, a.value)}`);
  const arms = trace.map((call, i) => {
    const effect = effects.find(e => e.id === call.id);
    return `| ${i}, ${op(call.id)} => ${answer(effect, call.answer)}`;
  });
  const oracle = `(fun op _ hist => match hist.length, op with ${arms.join(" ")} | _, _ => Js.Answer.reject ⟨${text("Error")}, ${text("the test's world has no more answers")}⟩)`;
  const checks = trace.map((call, i) => {
    const effect = effects.find(e => e.id === call.id);
    const terms = effect.params.map((type, j) => term(type, call.args[j]));
    if (terms.includes(undefined)) return undefined;
    const arg = terms.length === 0 ? "()" : terms.length === 1 ? terms[0] : `(${terms.join(", ")})`;
    return `(match e${i} with | ⟨${op(call.id)}, a, _⟩ => decide (a = ${arg}) | _ => false)`;
  });
  if (checks.includes(undefined)) return undefined;
  const pattern = `[${trace.map((_, i) => `e${i}`).join(", ")}]`;
  const trace_ = `(fun h => match h with | ${pattern} => ${checks.length ? checks.join(" && ") : "true"} | _ => false)`;
  return { oracle, trace: trace_ };
}

export async function differential({ root, out, module, signatures, files, imports = {}, cases = 200, effects = [] }) {
  const compiled = join(out, "js");
  const names = effects.map(e => e.call.split("::").at(-1));
  const ambiguous = new Set(names.filter((n, i) => names.indexOf(n) !== i));
  compile(root, files, imports, compiled, effects.filter(e => !ambiguous.has(e.call.split("::").at(-1))));
  const lines = [`import ${module}`, ...(signatures && Object.values(signatures).some(s => s.async) ? ["import ProofciAsync"] : []),
    "open Aeneas Aeneas.Std Result", ""];
  const skipped = [];
  const labels = [];
  let seed = 1;
  for (const [target, signature] of Object.entries(signatures)) {
    if (!signature.exported) { skipped.push(`${target}: not exported`); continue; }
    if (JSON.stringify(signature).includes('"generic"')) { skipped.push(`${target}: generic`); continue; }
    const loaded = await import(pathToFileURL(join(compiled, module_(signature.file))));
    const fn = loaded[signature.name];
    const value = generator(seed++);
    if (signature.async) {
      if ([...ambiguous].length) { skipped.push(`${target}: two effects have the same function name`); continue; }
      for (let index = 0; index < cases; index += 1) {
        const inputs = signature.params.map(value);
        const { outcome, trace } = await runAsync(fn, structuredClone(inputs), effects, seed * 1000 + index);
        let expected;
        if ("value" in outcome) {
          const t = term(signature.result, outcome.value);
          if (t !== undefined) expected = `(Js.Settled.fulfilled ${t})`;
        } else if (outcome.error instanceof Error) {
          expected = `(Js.Settled.rejected ⟨${text(outcome.error.name)}, ${text(outcome.error.message)}⟩)`;
        }
        const args = signature.params.map((type, i) => term(type, inputs[i]));
        const run = replay(trace, effects);
        labels.push(`${target} ${show(inputs)}`);
        if (args.includes(undefined) || !run) { lines.push(`#eval IO.println "PROOFCI_DIFF failed ${labels.length - 1}"`); continue; }
        lines.push(`#eval Js.agreeAsync "${labels.length - 1}" (_root_.${signature.lean} ${args.join(" ")} ${run.oracle} ([] : Proofci.Effects.world.Hist)) `
          + `${expected === undefined ? "none" : `(some ${expected})`} ${run.trace}`);
      }
      continue;
    }
    for (let index = 0; index < cases; index += 1) {
      const inputs = signature.params.map(value);
      let expected, threw = false;
      try {
        expected = term(signature.result, fn(...structuredClone(inputs)));
      } catch {
        threw = true;
      }
      const args = signature.params.map((type, i) => term(type, inputs[i]));
      labels.push(`${target} ${show(inputs)}`);
      lines.push(`#eval Js.agree "${labels.length - 1}" (_root_.${signature.lean} ${args.join(" ")}) `
        + (expected === undefined ? "none" : `(some ${expected})`) + ` ${threw}`);
    }
  }
  writeFileSync(join(out, "Differential.lean"), `${lines.join("\n")}\n`);
  writeFileSync(join(out, "cases.json"), JSON.stringify(labels));
  return { skipped };
}

if (process.argv[1]?.endsWith("differential.mjs")) {
  const config = JSON.parse(readFileSync(process.argv[2], "utf8"));
  console.log(JSON.stringify(await differential(config)));
}
