// Lists every reason a function can't be translated, not only the first, and
// ranks fixes by how many functions they would free. The real translator stops
// at its first failure, so this wraps it from outside: each wrapper records the
// failure and carries on with a placeholder. The output is only a measurement,
// so nothing here can change what a real translation accepts.
// Usage: node survey/blockers.mjs <repo> <survey.json> <out.json>
import { readFileSync, writeFileSync } from "node:fs";
import ts from "typescript";
import { Scope, Translator, Unsupported, findDeclaration } from "../translate.mjs";
import { workspacePaths } from "./analyze.mjs";

const NAMED_TYPES = /^the type `(any|unknown|object|never|Record<.*|Date|Error|Promise<.*)`.*$/;

// Names vary by repository, so a reason is reduced to its kind.
export const category = message => {
  const text = message.replace(/^[^:]*:\d+: /, "");
  if (NAMED_TYPES.test(text)) return text.replace(NAMED_TYPES, (_, type) => `type ${type.replace(/<.*/, "<>")}`);
  if (text.startsWith("TypeScript error")) return text.replace(/'[^']*'/g, "'_'").replace(/"[^"]*"/g, "'_'").replace(/\d+/g, "N").slice(0, 70);
  // `async`, `AwaitExpression` or `.lastIndexOf`: the name is the finding.
  const construct = text.match(/^`(\.?\w+)` is (not supported yet|only supported on)/);
  if (construct?.[1] === "async" || construct?.[1] === "AwaitExpression") return "async";
  if (construct) return `${construct[1]} ${construct[2]}`;
  const other = text.match(/^the type `(.*)` is not supported yet/s);
  if (other) {
    const type = other[1];
    if (type.includes("=>")) return "function-valued type";
    if (type.includes(" | ")) return "union of other types";
    if (type.startsWith("[")) return "tuple type";
    if (type.startsWith("Promise<")) return "async";
    return "named type (class or library)";
  }
  if (/outside the translated package/.test(text)) return "code outside the translated package";
  return text.replace(/`[^`]*`/g, "`_`").replace(/\d+/g, "N").slice(0, 80);
};

const OUTSIDE = /this call isn't to a function|has no source in the package|outside the translated package/;

function publishedTypes(translator, node) {
  const signature = translator.checker.getResolvedSignature(node);
  if (!signature) return false;
  const types = [...signature.parameters.map(p => translator.checker.getTypeOfSymbolAtLocation(p, node)), signature.getReturnType()];
  try {
    for (const type of types) translator.type(type, node);
    return true;
  } catch (error) {
    if (error instanceof Unsupported) return false;
    throw error;
  }
}

// Each wrapper records into the function being translated.
export function collecting(translator) {
  const blockers = new Map(); // declaration -> Set of reasons
  const calls = new Map();    // declaration -> Set of callees
  const stack = [];
  let probing = false;
  const note = reason => {
    const owner = stack.at(-1);
    if (!owner) return;
    if (!blockers.has(owner)) blockers.set(owner, new Set());
    blockers.get(owner).add(reason);
  };
  const recover = (object, method, fallback) => {
    const original = object[method];
    object[method] = function (...args) {
      try {
        return original.apply(this, args);
      } catch (error) {
        if (probing) throw error; // Asking about a type isn't a finding either.
        // A placeholder can upset later code, which isn't a finding of its own.
        note(error instanceof Unsupported ? category(error.message) : "(follow-on)");
        return fallback.call(this, args);
      }
    };
  };

  // An outside call is only usable through its published types if they translate.
  const fail = translator.fail;
  translator.fail = function (node, message) {
    if (!OUTSIDE.test(message) || !ts.isCallExpression(node)) return fail.call(this, node, message);
    probing = true;
    const usable = publishedTypes(this, node);
    probing = false;
    return fail.call(this, node, `${message} (${usable ? "types translate" : "types don't translate"})`);
  };

  const self = translator;
  recover(self, "checkFile", () => undefined);
  recover(self, "checkDeclaration", () => undefined);
  recover(self, "type", () => "Js.Num");
  recover(self, "describe", () => ({ kind: "number" }));
  // A type is only checked the first time it is met, so each use depends on it
  // the way a call depends on its callee.
  const edge = target => {
    const caller = stack.at(-1);
    if (!caller) return;
    if (!calls.has(caller)) calls.set(caller, new Set());
    calls.get(caller).add(target);
  };
  const declaring = (method, keyOf) => {
    const declare = self[method];
    self[method] = function (...args) {
      const key = keyOf(args);
      edge(key);
      stack.push(key);
      try {
        return declare.apply(this, args);
      } finally {
        stack.pop();
      }
    };
  };
  declaring("declareType", ([declaration]) => declaration);
  declaring("declareAnonymous", ([type]) => type);
  const original = self.declareFunction;
  self.declareFunction = function (declaration) {
    const caller = stack.at(-1);
    if (caller) {
      if (!calls.has(caller)) calls.set(caller, new Set());
      calls.get(caller).add(declaration);
    }
    if (this.functions.has(declaration)) return this.functions.get(declaration).lean;
    stack.push(declaration);
    // The real translator refuses `async` before reading the body, which would
    // hide everything else the function needs. Only this measurement reads on.
    const fn = this.bodyOf(declaration);
    const modifiers = fn?.modifiers;
    if (modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) {
      note("async");
      fn.modifiers = modifiers.filter(m => m.kind !== ts.SyntaxKind.AsyncKeyword);
    }
    try {
      return original.call(this, declaration);
    } catch (error) {
      note(error instanceof Unsupported ? category(error.message) : "(follow-on)");
      this.functions.set(declaration, { lean: "placeholder", pending: false, recursive: false });
      return "placeholder";
    } finally {
      if (fn) fn.modifiers = modifiers;
      stack.pop();
    }
  };
  return { blockers, calls, note };
}

// Scope methods are shared, so they are wrapped once for the whole run.
let active;
function wrapScope() {
  const wrap = (method, fallback) => {
    const original = Scope.prototype[method];
    Scope.prototype[method] = function (...args) {
      try {
        return original.apply(this, args);
      } catch (error) {
        active.note(error instanceof Unsupported ? category(error.message) : "(follow-on)");
        return fallback.call(this, args);
      }
    };
  };
  for (const method of ["expression", "convert", "operand", "numeric", "toText", "valueOf", "condition"]) wrap(method, () => "placeholder");
  for (const method of ["noteWrite", "checkOwnership", "requireFresh", "checkOwnedUse"]) wrap(method, () => undefined);
  wrap("parameter", ([p]) => `(p${p.pos} : Js.Num)`);
  // A statement that fails is skipped, and the rest of the block is still read.
  wrap("block", function ([statements, flow, env]) { return statements.length > 1 ? this.block(statements.slice(1), flow, env) : []; });
}
wrapScope();

// Every function a function reaches through its calls, itself included.
function closure(declaration, calls) {
  const seen = new Set([declaration]);
  const pending = [declaration];
  while (pending.length) {
    for (const callee of calls.get(pending.pop()) ?? []) if (!seen.has(callee)) { seen.add(callee); pending.push(callee); }
  }
  return [...seen];
}

// Everything that stops a function, through its calls.
export function reached(declaration, blockers, calls) {
  const found = new Set(closure(declaration, calls).flatMap(next => [...(blockers.get(next) ?? [])]));
  found.delete("(follow-on)");
  return [...found].sort();
}

export function measure(root, targets, paths = {}) {
  const translator = new Translator(root, targets, paths);
  active = collecting(translator);
  const rows = [];
  for (const target of targets) {
    try {
      const declaration = findDeclaration(translator, target);
      translator.current = [];
      translator.declareFunction(declaration);
      const reach = closure(declaration, active.calls);
      rows.push({ target, blockers: reached(declaration, active.blockers, active.calls), reach: reach.length,
        untyped: reach.filter(d => translator.untyped(d).length).length, self: translator.untyped(declaration) });
    } catch (error) {
      rows.push({ target, blockers: [error instanceof Unsupported ? category(error.message) : "(crash)"] });
    }
  }
  return rows;
}

if (process.argv[1]?.endsWith("blockers.mjs")) {
  const [root, input, out] = process.argv.slice(2);
  const { results } = JSON.parse(readFileSync(input, "utf8"));
  const top = results.filter(r => r.logic && !r.name.includes(".") && r.file.endsWith(".ts") && !r.file.startsWith("/"));
  const rows = measure(root, [...new Set(top.map(r => `${r.file}::${r.name}`))], workspacePaths(root));
  writeFileSync(out, JSON.stringify({ repo: root.split("/").pop(), methods: results.filter(r => r.logic && r.name.includes(".")).length, rows }));
  console.log(root.split("/").pop(), rows.length, rows.filter(r => !r.blockers.length).length);
}
