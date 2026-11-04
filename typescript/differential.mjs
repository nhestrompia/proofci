// Runs translated functions in Node on generated inputs and writes a Lean file
// that replays them against the model. The two must agree wherever the model
// returns a value. A disagreement means the translator or the runtime is wrong.
//
// Usage: node differential.mjs <config.json>
//   config: { root, out, module, signatures, files, cases }

import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { pathToFileURL } from "node:url";
import ts from "typescript";

const MAX = Number.MAX_SAFE_INTEGER;
const EDGES = [0, 1, -1, 2, -2, 3, 7, 10, -10, 100, 500, 1000, 9999, 10000, 10001, 94906265, 94906266, 2 ** 31, 2 ** 32, 2 ** 52, MAX - 1, MAX, -MAX];

const TEXTS = ["", "a", "b", "abc", " x ", "A-b", "a,b,c", ",", ",,", "Hello World", "é", "😀", "a😀b", "\ud800", "ÄB", "\t\n", "12", "$&"];

function generator(seed) {
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
      if (value === (type.nothing === "null" ? null : undefined)) return "none";
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

function compile(root, files, out) {
  for (const file of files) {
    const js = ts.transpileModule(readFileSync(join(root, file), "utf8"), {
      compilerOptions: { target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext },
    }).outputText.replace(/(from\s+["'])(\.{1,2}\/[^"']+?)(?:\.[cm]?[jt]s)?(["'])/g, "$1$2.mjs$3");
    const path = join(out, file.replace(/\.ts$/, ".mjs"));
    mkdirSync(dirname(path), { recursive: true });
    writeFileSync(path, js);
  }
}

export async function differential({ root, out, module, signatures, files, cases = 200 }) {
  const compiled = join(out, "js");
  compile(root, files, compiled);
  const lines = [`import ${module}`, "open Aeneas Aeneas.Std Result", ""];
  const skipped = [];
  const labels = [];
  let seed = 1;
  for (const [target, signature] of Object.entries(signatures)) {
    if (!signature.exported) { skipped.push(`${target}: not exported`); continue; }
    const loaded = await import(pathToFileURL(join(compiled, signature.file.replace(/\.ts$/, ".mjs"))));
    const fn = loaded[signature.name];
    const value = generator(seed++);
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
