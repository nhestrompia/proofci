// Runs translated functions in Node on generated inputs and writes a Lean file
// that replays them against the model. The two must agree wherever the model
// returns a value. A disagreement means the translator or the runtime is wrong.
//
// Usage: node differential.mjs <config.json>
//   config: { root, out, module, signatures, files, imports, cases }

import { closeSync, mkdirSync, openSync, readFileSync, realpathSync, writeFileSync, writeSync } from "node:fs";
import { dirname, join, posix, relative } from "node:path";
import { pathToFileURL } from "node:url";
import ts from "typescript";

const MAX = Number.MAX_SAFE_INTEGER;
const DBL_EDGES = [NaN, Infinity, -Infinity, -0, 0.1, 0.2, 0.5, -0.5, 2 ** 53, 2 ** 53 - 1, -(2 ** 53), 5e-324,
  1.7976931348623157e308, Number.EPSILON, 0.49999999999999994, -0.49999999999999994, 1 / 3];
const EDGES = [0, 1, -1, 2, -2, 3, 7, 10, -10, 100, 500, 1000, 9999, 10000, 10001, 94906265, 94906266, 2 ** 31, 2 ** 32, 2 ** 52, MAX - 1, MAX, -MAX];

const TEXTS = ["", "a", "b", "abc", " x ", "A-b", "a,b,c", ",", ",,", "Hello World", "é", "😀", "a😀b", "\ud800", "ÄB", "\t\n", "12", "$&", " 42 ", "-7", "+3", "007", "-0", "1e3", "0x1F", "1.5", "9007199254740993"];

// Code units for generated strings: ASCII, and halves of a surrogate pair that may or may not meet.
const UNITS = ["a", "b", "x", "A", "Z", "0", "7", " ", "\t", "\n", "-", "_", ",", ";", ".", "é", "\ud83d", "\ude00", "😀"];

// Every object of a class or library type the test makes gets its own number, which is also how the Lean
// side names it (`Js.Handle.mk n`). The same number is the same object.
let handles = 0;

// Whether a value of `type` can hold the type it sits in (`{ kind: "recursive" }` names that type).
// Whether a value of `type` can hold a recursive one, through any field (types that hold each
// other recur through a record or union described in full); and whether it must.
const recurs = type => type.kind === "recursive" || ["array", "set", "optional"].includes(type.kind) && recurs(type.item ?? type.inner)
  || type.kind === "map" && recurs(type.value)
  || type.kind === "record" && type.fields.some(f => recurs(f.type))
  || type.kind === "tagged" && type.variants.some(v => v.fields.some(f => recurs(f.type)));
const mustRecur = type => type.kind === "recursive"
  || type.kind === "record" && type.fields.some(f => mustRecur(f.type))
  || type.kind === "tagged" && type.variants.every(v => v.fields.some(f => mustRecur(f.type)));
// How deep a recursive value is generated: below this, a recursive field is empty where it can be.
const DEPTH = 3;

export function generator(seed, literals = {}) {
  let state = seed >>> 0;
  const next = () => {
    state = (state + 0x6d2b79f5) >>> 0;
    let t = state;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
  const pick = list => list[Math.floor(next() * list.length)];
  // Literals the contract's hypotheses name: biased into the pools so a hypothesis
  // like `offset = 20` or `query.tag = "a"` is actually exercised sometimes.
  const numberLiterals = (literals.numbers ?? []).filter(Number.isSafeInteger);
  const stringLiterals = (literals.strings ?? []).filter(s => typeof s === "string");
  const number = () => {
    const shape = next();
    if (shape < 0.45) return Math.floor(next() * 2001) - 1000;
    if (shape < 0.75) return pick(EDGES);
    if (shape < 0.9) return Math.floor(next() * 200_000_001) - 100_000_000;
    return Math.floor((next() - 0.5) * 2 * MAX);
  };
  const dbl = () => {
    const shape = next();
    if (shape < 0.3) return number();
    if (shape < 0.5) return pick(DBL_EDGES);
    if (shape < 0.7) return (next() - 0.5) * 200;
    return next() < 0.5 ? number() / 7 : (next() - 0.5) * 1e308;
  };
  const defs = new Map();
  let depth = 0;
  const deep = type => depth >= DEPTH && recurs(type);
  const value = type => {
    switch (type.kind) {
      case "number": return numberLiterals.length && next() < 0.35 ? pick(numberLiterals) : number();
      case "double": return numberLiterals.length && next() < 0.15 ? pick(numberLiterals) : dbl();
      case "boolean": return next() < 0.5;
      case "bigint": return BigInt(number()) * (next() < 0.2 ? 1000000007n : 1n);
      case "void": return undefined;
      case "generic": return number();
      case "string": return stringLiterals.length && next() < 0.35 ? pick(stringLiterals)
        : next() < 0.5 ? pick(TEXTS) : Array.from({ length: Math.floor(next() * 9) }, () => pick(UNITS)).join("");
      case "map": return new Map(Array.from({ length: Math.floor(next() * 5) }, () => [value(type.key), value(type.value)]));
      case "dict": return Object.fromEntries(Array.from({ length: Math.floor(next() * 5) }, () => [pick(KEYS), value(type.value)]));
      case "set": return new Set(Array.from({ length: Math.floor(next() * 5) }, () => value(type.item)));
      case "array": return Array.from({ length: deep(type.item) || next() < 0.15 ? 0 : Math.floor(next() * (depth ? 4 : 7)) }, () => value(type.item));
      case "optional": return next() < 0.45 || deep(type.inner) ? (type.nothing === "null" ? null : undefined) : value(type.inner);
      case "recursive": {
        depth += 1;
        try { return value(defs.get(type.lean)); } finally { depth -= 1; }
      }
      case "enum": return pick(type.tags).tag;
      case "handle": return { __proofciHandle: handles += 1, __class: type.name };
      case "record": defs.set(type.lean, type); return Object.fromEntries(type.fields.map(f => [f.name, value(f.type)]));
      case "tagged": {
        defs.set(type.lean, type);
        // The translator refuses a recursive type with no variant that ends.
        const ends = type.variants.filter(v => v.fields.every(f => !mustRecur(f.type)));
        const variant = pick(depth >= DEPTH && ends.length ? ends : type.variants);
        return { kind: variant.tag, ...Object.fromEntries(variant.fields.map(f => [f.name, value(f.type)])) };
      }
      default: throw new Error(`no generator for ${type.kind}`);
    }
  };
  return value;
}

const KEYS = ["a", "b", "id", "name", "x1", "Key", "a b", "0", "12", "toString", "__proto__", "é"];
const PROTO = new Set(["__proto__", "__class", "constructor", "hasOwnProperty", "isPrototypeOf", "propertyIsEnumerable",
  "toLocaleString", "toString", "valueOf", "__defineGetter__", "__defineSetter__", "__lookupGetter__", "__lookupSetter__"]);
// The keys `Js.keyOk` allows in a record of dynamic keys.
export const keyOk = k => k !== "" && /^[\x00-\x7f]*$/.test(k) && !/^[0-9]+$/.test(k) && !PROTO.has(k);

// The Lean spelling of a JavaScript value, or undefined if it isn't of `type`.
const onPath = new Set();
export function term(type, value, defs = new Map()) {
  const at = (inner, v) => term(inner, v, defs);
  switch (type.kind) {
    case "number":
      if (!Number.isSafeInteger(value)) return undefined;
      return `(Js.lit (${value === 0 ? 0 : value}))`;
    case "double": {
      if (typeof value !== "number") return undefined;
      const buf = new DataView(new ArrayBuffer(8));
      buf.setFloat64(0, value);
      return `(Js.Dbl.lit 0x${buf.getBigUint64(0).toString(16)})`;
    }
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
      const parts = [...value].map(([k, v]) => [at(type.key, k), at(type.value, v)]);
      return parts.flat().includes(undefined) ? undefined : `[${parts.map(([k, v]) => `(${k}, ${v})`).join(", ")}]`;
    }
    case "dict": {
      if (typeof value !== "object" || value === null || Object.getPrototypeOf(value) !== Object.prototype) return undefined;
      const entries = Object.entries(value);
      if (Object.keys(value).length !== Reflect.ownKeys(value).length || entries.some(([k]) => !keyOk(k))) return undefined;
      const parts = entries.map(([k, v]) => [term({ kind: "string" }, k), term(type.value, v)]);
      return parts.flat().includes(undefined) ? undefined : `([${parts.map(([k, v]) => `(${k}, ${v})`).join(", ")}] : Js.Dict Js.Str _)`;
    }
    case "set": {
      if (!(value instanceof Set)) return undefined;
      const parts = [...value].map(item => at(type.item, item));
      return parts.includes(undefined) ? undefined : `[${parts.join(", ")}]`;
    }
    case "array": {
      if (!Array.isArray(value)) return undefined;
      const parts = value.map(item => at(type.item, item));
      return parts.includes(undefined) ? undefined : `[${parts.join(", ")}]`;
    }
    case "optional": {
      if (value === (type.nothing === "null" ? null : undefined) || (type.both && value == null)) return "none";
      const inner = at(type.inner, value);
      return inner === undefined ? undefined : `(some ${inner})`;
    }
    case "generic":
      return term({ kind: "number" }, value);
    case "handle":
      return Number.isSafeInteger(value?.__proofciHandle) ? `(Js.Handle.mk ${value.__proofciHandle})` : undefined;
    case "enum": {
      const tag = type.tags.find(t => t.tag === value);
      return tag ? `_root_.${type.lean}.${tag.lean}` : undefined;
    }
    // A cycle has no Lean value.
    case "recursive": {
      if (onPath.has(value)) return undefined;
      onPath.add(value);
      try { return at(defs.get(type.lean), value); } finally { onPath.delete(value); }
    }
    case "record": {
      defs.set(type.lean, type);
      if (typeof value !== "object" || value === null) return undefined;
      const parts = type.fields.map(f => at(f.type, value[f.name]));
      if (parts.includes(undefined)) return undefined;
      return `(_root_.${type.lean}.mk ${parts.join(" ")})`;
    }
    case "tagged": {
      defs.set(type.lean, type);
      if (typeof value !== "object" || value === null) return undefined;
      const variant = type.variants.find(v => v.tag === value.kind);
      if (!variant) return undefined;
      const parts = variant.fields.map(f => at(f.type, value[f.name]));
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

// A file's emitted module path: `../other-pkg/x.ts` (a file a workspace package resolved
// outside the package root) is normalized to a path inside `out`, or imports and stand-ins
// would be written and referenced outside it.
const module_ = file => file.replace(/\.tsx?$/, ".mjs").split("/")
  .filter(part => part !== "." && part !== "")
  // `..` becomes `__up` and a literal `__up*` doubles its prefix, so two different
  // source paths can never collide and nothing escapes the output directory.
  .map(part => part === ".." ? "__up" : part.startsWith("__up") ? `__up${part}` : part)
  .join("/");

// The names a top-level statement binds, so a run can keep only the ones its targets need.
function boundNames(statement) {
  const names = new Set();
  const bind = pattern => {
    if (ts.isIdentifier(pattern)) names.add(pattern.text);
    else if (ts.isBindingElement(pattern)) bind(pattern.name);
    else if (ts.isObjectBindingPattern(pattern) || ts.isArrayBindingPattern(pattern)) pattern.elements.forEach(bind);
  };
  if ((ts.isFunctionDeclaration(statement) || ts.isClassDeclaration(statement)) && statement.name) names.add(statement.name.text);
  if (ts.isVariableStatement(statement)) statement.declarationList.declarations.forEach(d => bind(d.name));
  if (ts.isImportDeclaration(statement) && statement.importClause) {
    const clause = statement.importClause;
    if (clause.name) names.add(clause.name.text);
    if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) names.add(clause.namedBindings.name.text);
    else clause.namedBindings?.elements.forEach(e => names.add(e.name.text));
  }
  if (ts.isExportAssignment(statement)) names.add("default");
  // `export {x}`/`export {x as pub}` bind the public names; `export *` binds nothing known.
  if (ts.isExportDeclaration(statement) && statement.exportClause)
    for (const el of statement.exportClause.elements) names.add(el.name.text);
  return names;
}

// Whether an identifier occurrence names a value the module level provides, rather than a
// property key, a label, a declaration's own name or a binding position.
function isReference(node) {
  const parent = node.parent;
  if (!parent) return true;
  if (ts.isPropertyAccessExpression(parent) && parent.name === node) return false;
  if ((ts.isPropertyAssignment(parent) || ts.isEnumMember(parent)) && parent.name === node) return false;
  if (ts.isBindingElement(parent) || ts.isImportSpecifier(parent) || ts.isExportSpecifier(parent)) return false;
  if (ts.isParameter(parent)) return parent.name !== node; // a default like `n = LIMIT` still reads it
  if ((ts.isFunctionDeclaration(parent) || ts.isClassDeclaration(parent) || ts.isVariableDeclaration(parent)
    || ts.isFunctionExpression(parent) || ts.isClassExpression(parent)) && parent.name === node) return false;
  if ((ts.isMethodDeclaration(parent) || ts.isGetAccessorDeclaration(parent) || ts.isSetAccessorDeclaration(parent)
    || ts.isMethodSignature?.(parent)) && parent.name === node) return false;
  if (ts.isLabeledStatement(parent) || ts.isBreakOrContinueStatement(parent)) return false;
  if (ts.isImportClause(parent) || ts.isNamespaceImport(parent) || ts.isImportCall?.(parent)) return false;
  return true;
}

// The names bound inside `root` that hide a module-level one. Over-approximating is safe (it
// only keeps a little more), missing one is not — every binding form a transpiled module holds
// must be covered.
function localBindings(root) {
  const bound = new Set();
  const bind = pattern => {
    if (!pattern) return;
    if (ts.isIdentifier(pattern)) bound.add(pattern.text);
    else if (ts.isBindingElement(pattern)) bind(pattern.name);
    else if (ts.isObjectBindingPattern(pattern) || ts.isArrayBindingPattern(pattern)) pattern.elements.forEach(el => bind(el.name ?? el));
  };
  const walk = node => {
    if ((ts.isFunctionDeclaration(node) || ts.isFunctionExpression(node)) && node.name) bound.add(node.name.text);
    if ((ts.isClassDeclaration(node) || ts.isClassExpression(node)) && node.name) bound.add(node.name.text);
    if (ts.isVariableDeclaration(node)) bind(node.name);
    if (ts.isParameter(node)) bind(node.name);
    if (ts.isCatchClause(node) && node.variableDeclaration) bind(node.variableDeclaration.name);
    if (ts.isBindingElement(node)) bind(node.name);
    ts.forEachChild(node, walk);
  };
  walk(root);
  return bound;
}

// The module-level names a statement needs, and the module-level names it writes.
const SCOPED = node => ts.isBlock(node) || ts.isFunctionLike(node) || ts.isCatchClause(node)
  || ts.isForStatement(node) || ts.isForInOrOfStatement(node);

function dependencies(statement, eagerOnly = false) {
  const needs = new Set(), writes = new Set();
  const lhs = node => {
    for (;;) {
      if (ts.isParenthesizedExpression(node)) { node = node.expression; continue; }
      return node;
    }
  };
  // Function and method bodies (and class field initializers) run lazily — they only
  // count when the whole statement's init-time effect is asked for, not here.
  const lazy = node => ts.isFunctionLike(node) || ts.isMethodDeclaration(node)
    || ts.isGetAccessorDeclaration(node) || ts.isSetAccessorDeclaration(node)
    || ts.isPropertyDeclaration(node);
  const walk = (node, bound) => {
    if (eagerOnly && lazy(node)) return;
    // A callback's parameter shadows a module name only inside the callback: bindings apply
    // per scope, not to the whole statement.
    if (SCOPED(node)) bound = new Set([...bound, ...localBindings(node)]);
    if (ts.isIdentifier(node) && isReference(node) && !bound.has(node.text)) {
      const p = node.parent;
      if ((ts.isBinaryExpression(p) && [ts.SyntaxKind.EqualsToken, ts.SyntaxKind.PlusEqualsToken, ts.SyntaxKind.MinusEqualsToken,
          ts.SyntaxKind.AsteriskEqualsToken, ts.SyntaxKind.SlashEqualsToken].includes(p.operatorToken.kind) && lhs(p.left) === node)
        || ((ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p)) && [ts.SyntaxKind.PlusPlusToken, ts.SyntaxKind.MinusMinusToken].includes(p.operator))) {
        writes.add(node.text);
      } else {
        needs.add(node.text);
      }
    }
    ts.forEachChild(node, child => walk(child, bound));
  };
  walk(statement, new Set());
  // `export {x}`/`export {x as pub}` (no module specifier) reads the local `x`: if
  // the alias is kept but `x`'s declaration is dropped the module cannot load.
  if (ts.isExportDeclaration(statement) && statement.exportClause && !statement.moduleSpecifier)
    for (const el of statement.exportClause.elements) needs.add((el.propertyName ?? el.name).text);
  return { needs, writes };
}

function importedNames(statement) {
  const names = new Set();
  const bindings = ts.isImportDeclaration(statement) ? statement.importClause?.namedBindings : statement.exportClause;
  if (bindings && (ts.isNamedImports(bindings) || ts.isNamedExports(bindings))) {
    for (const element of bindings.elements) names.add((element.propertyName ?? element.name).text);
  }
  names.delete("default");
  return [...names];
}

// Statements whose names `wanted` reaches through the same module: the target function and the
// declarations it transitively uses. Everything else (other functions, classes, one-off setup
// statements) is left out, so a construct the target doesn't call can't crash the run.
// Returns { keep, reason }: when the needed set writes to a name another statement also writes,
// the run can't be isolated without changing what the target sees, and that is a hard reason.
const GLOBALS = new Set(["undefined", "NaN", "Infinity", "globalThis", "arguments", "Math", "JSON",
  "Object", "Array", "Number", "String", "Boolean", "BigInt", "Map", "Set", "Promise", "Error",
  "TypeError", "RangeError", "SyntaxError", "EvalError", "URIError", "AggregateError", "RegExp",
  "Symbol", "Date", "Reflect", "Proxy", "WeakMap", "WeakSet", "WeakRef", "Intl", "console",
  "queueMicrotask", "setTimeout", "setInterval", "clearTimeout", "clearInterval", "structuredClone",
  "fetch", "atob", "btoa", "encodeURIComponent", "decodeURIComponent", "encodeURI", "decodeURI",
  "parseInt", "parseFloat", "isNaN", "isFinite", "ArrayBuffer", "DataView", "Uint8Array", "Int8Array",
  "Uint16Array", "Int16Array", "Uint32Array", "Int32Array", "Float32Array", "Float64Array",
  "BigInt64Array", "BigUint64Array", "SharedArrayBuffer", "Atomics", "FinalizationRegistry",
  "Buffer", "process", "require", "exports", "module", "__dirname", "__filename", "URL",
  "URLSearchParams", "TextEncoder", "TextDecoder", "AbortController", "AbortSignal", "Event",
  "EventTarget", "crypto", "performance", "localStorage", "global"]);

function isolate(statements, wanted) {
  const bound = statements.map(boundNames);
  const deps = statements.map(s => dependencies(s));
  const keep = statements.map(() => false);
  const seen = new Set();
  const kept = new Set();
  const queue = [...wanted];
  while (queue.length) {
    const name = queue.pop();
    if (!seen.has(name)) {
      seen.add(name);
      if (!statements.some((_, i) => bound[i].has(name))) {
        if (!GLOBALS.has(name))
          return { keep, reason: `${JSON.stringify(name)} is needed but is not declared at the module level or a known global` };
      } else {
        for (const i of statements.keys()) {
          if (bound[i].has(name) && !keep[i]) {
            keep[i] = true;
            bound[i].forEach(n => kept.add(n));
            for (const need of deps[i].needs) queue.push(need);
          }
        }
      }
    }
    if (!queue.length) {
      // A dropped statement that mentions a kept name — a read, a call through it, a
      // property write — can change what the target sees (`TABLE.push(1)`,
      // `Object.freeze(CONFIG)`, `LIMITS.max = 5`, `registry.set(k, v)`). It runs in
      // real JavaScript, so it runs here too; if keeping it crashes the run the
      // import error is reported, never silently dropped.
      for (const i of statements.keys()) {
        if (keep[i]) continue;
        // A statement that binds names only counts if its init-time expressions touch a
        // kept name — a never-called function body reading it does not run at load.
        const touched = bound[i].size ? (() => { const d = dependencies(statements[i], true); return [...d.needs, ...d.writes]; })()
          : [...deps[i].needs, ...deps[i].writes];
        if (!touched.some(n => kept.has(n))) continue;
        keep[i] = true;
        bound[i].forEach(n => kept.add(n));
        for (const need of deps[i].needs) queue.push(need);
      }
    }
  }
  return { keep, reason: null };
}

// Files reached by a target run for real. Anything else they import is replaced,
// so the comparison runs only code that was translated, and doesn't depend on
// packages being installed.
export function compile(root, files, imports, out, effects = [], needs = {}) {
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
  const reasons = {};
  const transpiled = new Map();
  const parsedOf = file => {
    if (!transpiled.has(file)) {
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
      transpiled.set(file, js);
    }
    return ts.createSourceFile("out.mjs", transpiled.get(file), ts.ScriptTarget.ES2022, true);
  };
  // Seed each file's set from its own targets, then grow it by what kept statements in other
  // files import from this one: a helper imported by a target elsewhere must not be dropped.
  const wanted = new Map(Object.entries(needs).map(([f, names]) => [f, new Set(names)]));
  const importNeeds = (statement, required) => {
    // The names a kept `import`/`export ... from` reads from its resolved module — only the
    // ones actually required here, so an unused sibling binding can't pull a crashing
    // initializer back into the exporting module.
    const pairs = []; // [local/public name, source-module name]
    if (ts.isImportDeclaration(statement)) {
      const clause = statement.importClause;
      if (!clause) return [];
      if (clause.namedBindings && ts.isNamespaceImport(clause.namedBindings)) return { all: true };
      if (clause.name) pairs.push([clause.name.text, "default"]);
      clause.namedBindings?.elements.forEach(el => pairs.push([el.name.text, (el.propertyName ?? el.name).text]));
    } else {
      // `export {x} from`/`export {x as pub} from`: the public name is read here, the source
      // name (propertyName when present) is what the other module declares.
      if (!statement.exportClause) return { all: true }; // export *
      statement.exportClause.elements.forEach(el => pairs.push([el.name.text, (el.propertyName ?? el.name).text]));
    }
    return { names: pairs.filter(([local]) => required.has(local)).map(([, remote]) => remote), all: false };
  };
  for (let grew = true; grew;) {
    grew = false;
    for (const [file, want] of wanted) {
      if (reasons[file]) continue;
      const parsed = parsedOf(file);
      const { keep, reason } = isolate([...parsed.statements], [...want]);
      if (reason) { reasons[file] = reason; continue; }
      // Names this file requires: its wanted set plus whatever kept statements read.
      const required = new Set(want);
      parsed.statements.forEach((s, i) => {
        if (keep[i]) dependencies(s).needs.forEach(n => required.add(n));
      });
      for (const [i, statement] of parsed.statements.entries()) {
        if (!keep[i] || !statement.moduleSpecifier) continue;
        const resolved = imports[file]?.[statement.moduleSpecifier.text];
        const target = resolved && relative(realRoot, resolved);
        if (!target || !reached.has(target) || !wanted.has(target)) continue;
        const { names, all } = importNeeds(statement, required);
        const add = all ? [...exported.keys()].filter(n => exported.get(n) === target) : names;
        for (const n of add) if (!wanted.get(target).has(n)) { wanted.get(target).add(n); grew = true; }
      }
    }
  }
  for (const file of files) {
    let parsed = parsedOf(file);
    let js = transpiled.get(file);
    // Emit only what this file's targets reach: a construct they don't need (a class the
    // runtime can't evaluate, one-off setup code) can't crash the run.
    const wantedNames = [...(wanted.get(file) ?? [])];
    if (wantedNames.length) {
      const { keep, reason } = isolate([...parsed.statements], wantedNames);
      if (reason) { reasons[file] = reason; continue; }
      const kept = new Set();
      parsed.statements.forEach((s, i) => { if (keep[i]) boundNames(s).forEach(n => kept.add(n)); });
      const needed = new Set(wantedNames);
      // An export that names a dropped binding makes the module fail to load, so only exports
      // of kept names stay; `export *` hides its names and never stays.
      const exportNeeded = s => {
        if (ts.isExportAssignment(s)) return needed.has("default");
        if (!ts.isExportDeclaration(s) || !s.exportClause) return false;
        return s.exportClause.elements.some(el => s.moduleSpecifier ? needed.has(el.name.text) : kept.has((el.propertyName ?? el.name).text));
      };
      js = [...parsed.statements].filter((s, i) => keep[i] || exportNeeded(s)).map(s => s.getText(parsed)).join("\n");
      parsed = ts.createSourceFile("out.mjs", js, ts.ScriptTarget.ES2022, true);
    }
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
  return reasons;
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
    case "dict": return Object.fromEntries(Object.entries(value).map(([k, v]) => [k, emptied(type.value, v, random)]));
    default: return value;
  }
}

// Runs an async function in Node against stand-ins for its outside calls. Each call is answered
// from a random script (a value of the declared type, or a rejection), after a random number of
// turns of the event loop, so the real scheduler is exercised. Returns what happened.
export async function runAsync(fn, inputs, effects, seed) {
  const random = chance(seed);
  // A handle is a stand-in object. A call on it, `h.method(...)`, is the outside call listed for its class
  // and that method, and it is answered like any other. Reading anything else from it gives `undefined`.
  const made = new Map();
  const proxify = x => {
    if (Array.isArray(x)) return x.map(proxify);
    if (x instanceof Map) return new Map([...x].map(([k, v]) => [k, proxify(v)]));
    if (x instanceof Set) return new Set([...x].map(proxify));
    if (x === null || typeof x !== "object") return x;
    if (x.__proofciHandle !== undefined) {
      if (!made.has(x.__proofciHandle)) {
        const target = { __proofciHandle: x.__proofciHandle, __class: x.__class };
        made.set(x.__proofciHandle, new Proxy(target, {
          get: (_, key) => {
            if (key in target) return target[key];
            const effect = typeof key === "string" && effects.find(e => e.call === `${target.__class}#${key}`);
            return effect ? (...args) => globalThis.__proofciWorld(effect.id, [made.get(target.__proofciHandle), ...args]) : undefined;
          },
        }));
      }
      return made.get(x.__proofciHandle);
    }
    return Object.fromEntries(Object.entries(x).map(([k, v]) => [k, proxify(v)]));
  };
  const value = generator(seed + 7919);
  const trace = [];
  globalThis.__proofciWorld = (id, args) => new Promise((resolve, reject) => {
    const effect = effects.find(e => e.id === id);
    const answer = random() < 0.2
      ? { reject: MESSAGES[Math.floor(random() * MESSAGES.length)], kind: ERRORS[Math.floor(random() * ERRORS.length)] }
      : { value: proxify(emptied(effect.returns, value(effect.returns), random)) };
    trace.push({ id, args: effect.params.map((_, i) => args[i]), answer });
    const settle = () => (answer.reject !== undefined ? reject(new globalThis[answer.kind](answer.reject)) : resolve(answer.value));
    const turns = Math.floor(random() * 3);
    if (turns === 0) queueMicrotask(settle); else setTimeout(settle, turns - 1);
  });
  let outcome;
  try {
    outcome = { value: await fn(...proxify(inputs)) };
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

export async function differential({ root, out, module, signatures, files, imports = {}, cases = 200, effects = [], literals = {} }) {
  const compiled = join(out, "js");
  // A call on an object (`Class#method`) has no declaration to replace: the object is the stand-in.
  const named = effects.filter(e => e.call.includes("::"));
  const names = named.map(e => e.call.split("::").at(-1));
  const ambiguous = new Set(names.filter((n, i) => names.indexOf(n) !== i));
  // Per file, the names runs need: each module emits only the targets' transitive dependencies.
  const needs = {};
  for (const signature of Object.values(signatures)) (needs[signature.file] ??= []).push(signature.name);
  const isolated = compile(root, files, imports, compiled, named.filter(e => !ambiguous.has(e.call.split("::").at(-1))), needs);
  const leanOut = openSync(join(out, "Differential.lean"), "w");
  const emit = line => writeSync(leanOut, line + "\n");
  [`import ${module}`, ...(signatures && Object.values(signatures).some(s => s.async) ? ["import ProofciAsync"] : []),
    "open Aeneas Aeneas.Std Result", ""].forEach(emit);
  const witnessOut = openSync(join(out, "inputs.json"), "w");
  writeSync(witnessOut, "{");
  let openTarget = null;
  const witness = (target, args) => {
    if (openTarget !== target) {
      writeSync(witnessOut, `${openTarget === null ? "" : "],"}${JSON.stringify(target)}:[`);
      openTarget = target;
    } else writeSync(witnessOut, ",");
    writeSync(witnessOut, JSON.stringify(args));
  };
  const skipped = [];
  const labels = [];
  let seed = 1;
  for (const [target, signature] of Object.entries(signatures)) {
    if (!signature.exported) { skipped.push(`${target}: not exported`); continue; }
    if (isolated[signature.file]) { skipped.push(`${target}: ${isolated[signature.file]}`); continue; }
    // A generic function is run at `number` for each type parameter, when its bound allows that.
    const generics = [];
    JSON.stringify(signature, (k, v) => { if (k === "declared") return undefined; if (v?.kind === "generic") generics.push(v); return v; });
    if (generics.some(g => !g.numbers)) { skipped.push(`${target}: generic with a bound that \`number\` doesn't meet`); continue; }
    const typeArgs = [...new Set(generics.map(g => g.lean))].map(g => `(${g} := Js.Num) `).join("");
    // Only the target's dependencies were emitted; if the module still fails to load, that is
    // this target's failure, not everyone's.
    const loaded = await import(pathToFileURL(join(compiled, module_(signature.file))))
      .catch(error => { skipped.push(`${target}: the module could not be run: ${error?.message ?? error}`); return null; });
    if (!loaded) continue;
    const fn = loaded[signature.name];
    const value = generator(seed++, literals[target] ?? {});
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
        if (args.includes(undefined) || !run) { emit(`#eval IO.println "PROOFCI_DIFF failed ${labels.length - 1}"`); continue; }
        witness(target, args);
        emit(`#eval Js.agreeAsync "${labels.length - 1}" (_root_.${signature.lean} ${typeArgs}${args.join(" ")} ${run.oracle} ([] : Proofci.Effects.world.Hist)) `
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
      if (args.includes(undefined)) { emit(`#eval IO.println "PROOFCI_DIFF failed ${labels.length - 1}"`); continue; }
      witness(target, args);
      emit(`#eval Js.agree "${labels.length - 1}" (_root_.${signature.lean} ${typeArgs}${args.join(" ")}) `
        + (expected === undefined ? "none" : `(some ${expected})`) + ` ${threw}`);
    }
  }
  writeSync(witnessOut, `${openTarget === null ? "" : "]"}}`);
  closeSync(leanOut); closeSync(witnessOut);
  writeFileSync(join(out, "cases.json"), JSON.stringify(labels));
  return { skipped };
}

if (process.argv[1]?.endsWith("differential.mjs")) {
  const config = JSON.parse(readFileSync(process.argv[2], "utf8"));
  console.log(JSON.stringify(await differential(config)));
}
