// Measures how much of a TypeScript code base a planned subset can reach.
//
// A function counts as covered only if everything it transitively calls is
// covered too, because that is what a proof would need. The analysis only
// parses and type-checks; it never runs code from the repository it reads.

import { createHash } from "node:crypto";
import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { dirname, join, relative } from "node:path";
import ts from "typescript";

// Which milestone can handle a feature. Features not listed are always fine.
export const TIER = {
  // Milestone 3
  "param-mutation": 3, "this-state": 3, "async": 3, "callback": 3,
  "ambient-effect": 3, "closure-mutation": 3,
  // Possible, but each library needs a model or a useful proof has nothing to go on
  "package-call": 4, "record-key": 4,
  // Beyond the plan
  "fractional": 9, "alias-risk": 9, "module-state": 9, "dynamic": 9,
  "reflection": 9, "dynamic-key": 9, "regex": 9, "date": 9, "generator": 9,
  "unmodeled-builtin": 9, "unchecked-cast": 9, "advanced-type": 9,
  "coercion": 9, "inheritance": 9,
};

const SKIP_DIR = /(^|\/)(node_modules|dist|build|out|coverage|\.next|\.git|vendor|generated|__generated__|__tests__|__mocks__|__fixtures__|fixtures|mocks?|tests?|e2e|cypress|playwright|stories|storybook|examples?|docs?|migrations?|benchmarks?|scripts)(\/|$)/i;
const SKIP_FILE = /(\.d\.ts|\.(test|spec|e2e|stories|bench|mock|generated|gen|min)\.ts|\.config\.ts)$/i;
const MUTATING = new Set(["push", "pop", "shift", "unshift", "splice", "sort", "reverse", "fill",
  "copyWithin", "set", "add", "delete", "clear"]);
const INTEGER_MATH = new Set(["floor", "ceil", "trunc", "round", "abs", "min", "max", "sign", "imul"]);
const FRACTIONAL_API = new Set(["parseFloat", "toFixed", "toPrecision"]);
const REFLECTION = new Set(["keys", "values", "entries", "assign", "fromEntries", "freeze", "create",
  "defineProperty", "getPrototypeOf", "setPrototypeOf", "getOwnPropertyNames"]);
const AMBIENT = new Set(["console", "process", "window", "document", "localStorage", "sessionStorage",
  "navigator", "fetch", "setTimeout", "setInterval", "clearTimeout", "clearInterval", "crypto",
  "globalThis", "performance", "Buffer", "require"]);
const DYNAMIC = new Set(["eval", "Function", "Proxy", "Reflect", "arguments"]);
const REGEX_STRING = new Set(["match", "matchAll", "replace", "replaceAll", "search", "split"]);
const SIMPLE_STRING = new Set(["length", "slice", "substring", "charAt", "charCodeAt", "codePointAt", "at",
  "indexOf", "lastIndexOf", "includes", "startsWith", "endsWith", "concat", "padStart", "padEnd", "repeat",
  "trim", "trimStart", "trimEnd", "toString", "valueOf", "split", "replace", "replaceAll"]);
const SIMPLE_NUMBER = new Set(["isInteger", "isSafeInteger", "isNaN", "isFinite", "toString", "valueOf"]);
const FRESH = new Set([ts.SyntaxKind.ObjectLiteralExpression, ts.SyntaxKind.ArrayLiteralExpression,
  ts.SyntaxKind.NewExpression]);

// How often each specific construct triggered a feature, across a run.
export const details = {};
const note = (feature, what) => {
  const entry = (details[feature] ??= {});
  entry[what] = (entry[what] ?? 0) + 1;
};

export function listFiles(root, { limit = 1500 } = {}) {
  const found = [];
  const walk = dir => {
    for (const name of readdirSync(dir)) {
      const path = join(dir, name);
      const rel = relative(root, path);
      let stat;
      try { stat = statSync(path); } catch { continue; }
      if (stat.isDirectory()) { if (!SKIP_DIR.test(`${rel}/`)) walk(path); continue; }
      if (name.endsWith(".ts") && !SKIP_FILE.test(name) && !SKIP_DIR.test(rel) && stat.size < 300_000) found.push(path);
    }
  };
  walk(root);
  // A stable sample, so that results can be reproduced.
  const key = p => createHash("sha256").update(relative(root, p)).digest("hex");
  return found.sort((a, b) => key(a).localeCompare(key(b))).slice(0, limit);
}

const ENTRIES = ["src/index.ts", "index.ts", "src/main.ts", "lib/index.ts", "src/index.tsx"];

// Imports between workspace packages and tsconfig aliases, which would
// otherwise look like third-party code because nothing is installed.
export function workspacePaths(root) {
  const paths = {};
  const walk = (dir, depth) => {
    for (const name of readdirSync(dir)) {
      if (name === "node_modules" || name.startsWith(".")) continue;
      const path = join(dir, name);
      let stat;
      try { stat = statSync(path); } catch { continue; }
      if (stat.isDirectory()) { if (depth < 5) walk(path, depth + 1); continue; }
      if (name !== "package.json") continue;
      let manifest;
      try { manifest = JSON.parse(readFileSync(path, "utf8")); } catch { continue; }
      if (typeof manifest.name !== "string") continue;
      const entry = ENTRIES.map(e => join(dir, e)).find(existsSync);
      if (entry) paths[manifest.name] = [entry];
      paths[`${manifest.name}/*`] = [join(dir, "src/*"), join(dir, "*")];
    }
  };
  walk(root, 0);
  for (const name of readdirSync(root)) {
    if (!/^tsconfig.*\.json$/.test(name)) continue;
    const config = ts.readConfigFile(join(root, name), p => readFileSync(p, "utf8")).config;
    const base = join(root, config?.compilerOptions?.baseUrl ?? ".");
    for (const [alias, targets] of Object.entries(config?.compilerOptions?.paths ?? {})) {
      paths[alias] ??= targets.map(target => join(base, target));
    }
  }
  return paths;
}

export function programFor(files, paths = {}) {
  return ts.createProgram(files, {
    paths,
    target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext,
    moduleResolution: ts.ModuleResolutionKind.Bundler, strict: true, noEmit: true,
    skipLibCheck: true, allowJs: false, types: [], experimentalDecorators: true,
  });
}

const unwrap = node => {
  while (ts.isParenthesizedExpression(node) || ts.isNonNullExpression(node)) node = node.expression;
  return node;
};

function rootOf(node) {
  let current = unwrap(node), depth = 0;
  while (ts.isPropertyAccessExpression(current) || ts.isElementAccessExpression(current)) {
    current = unwrap(current.expression);
    depth += 1;
  }
  return { root: current, depth };
}

function isLibrary(program, declaration) {
  const file = declaration.getSourceFile();
  return program.isSourceFileDefaultLibrary(file);
}

function functionLike(declaration) {
  if (!declaration) return undefined;
  if (ts.isFunctionLike(declaration) && declaration.body) return declaration;
  if (ts.isVariableDeclaration(declaration) && declaration.initializer) {
    const init = unwrap(declaration.initializer);
    if (ts.isArrowFunction(init) || ts.isFunctionExpression(init)) return init;
  }
  return undefined;
}

function declarationScope(declaration) {
  let node = declaration.parent;
  while (node && !ts.isFunctionLike(node) && !ts.isSourceFile(node)) node = node.parent;
  return node;
}

function isModuleLevel(declaration) {
  return ts.isSourceFile(declarationScope(declaration));
}

// Features one function's own body uses, and the functions it calls.
export function inspect(program, checker, fn) {
  const features = new Set();
  const callees = new Set();
  let decisions = 0;

  const symbolOf = node => {
    const symbol = checker.getSymbolAtLocation(node);
    if (symbol && symbol.flags & ts.SymbolFlags.Alias) return checker.getAliasedSymbol(symbol);
    return symbol;
  };
  const isObjectLike = node => {
    const type = checker.getTypeAtLocation(node);
    return (type.flags & ts.TypeFlags.Object) !== 0;
  };
  const isBigInt = node => (checker.getTypeAtLocation(node).flags & ts.TypeFlags.BigIntLike) !== 0;

  // Classifies a write to `target`, which may be a nested property path.
  const onWrite = (target, within, contents = false) => {
    const { root, depth: path } = rootOf(target);
    const depth = path + (contents ? 1 : 0);
    if (root.kind === ts.SyntaxKind.ThisKeyword) return features.add("this-state");
    if (!ts.isIdentifier(root)) return features.add("alias-risk");
    const symbol = symbolOf(root);
    const declaration = symbol?.valueDeclaration;
    if (!declaration) return features.add("alias-risk");
    if (isLibrary(program, declaration)) return features.add("ambient-effect");
    if (isModuleLevel(declaration)) return features.add("module-state");
    if (declarationScope(declaration) !== within) features.add("closure-mutation");
    if (ts.isParameter(declaration)) {
      if (depth > 0) features.add("param-mutation");
      return;
    }
    if (ts.isBindingElement(declaration)) {
      if (depth > 0) features.add("alias-risk");
      return;
    }
    if (depth === 0 || !ts.isVariableDeclaration(declaration)) return;
    if (ts.isForOfStatement(declaration.parent.parent)) return features.add("alias-risk");
    const init = declaration.initializer && unwrap(declaration.initializer);
    if (init && !FRESH.has(init.kind) && !ts.isCallExpression(init) && isObjectLike(init)) features.add("alias-risk");
  };

  const onCall = (call, within) => {
    const callee = unwrap(call.expression);
    if (ts.isIdentifier(callee) && DYNAMIC.has(callee.text)) features.add("dynamic");
    const signature = checker.getResolvedSignature(call);
    const declaration = signature?.declaration ?? symbolOf(callee)?.valueDeclaration;
    if (!declaration || ts.isJSDocSignature(declaration)) return features.add("package-call");

    if (isLibrary(program, declaration)) return onLibraryCall(call, callee, within);
    const target = functionLike(declaration);
    if (target) return void callees.add(target);
    // Declared without a body in a declaration file: third-party code.
    if (declaration.getSourceFile().isDeclarationFile || declaration.flags & ts.NodeFlags.Ambient) return features.add("package-call");
    // A callback from the caller or an interface method: a proof can quantify over it.
    features.add("callback");
  };

  const onLibraryCall = (call, callee, within) => {
    if (!ts.isPropertyAccessExpression(callee)) {
      const name = ts.isIdentifier(callee) ? callee.text : "";
      note("library", name);
      if (FRACTIONAL_API.has(name)) features.add("fractional");
      else if (AMBIENT.has(name)) features.add("ambient-effect");
      else if (!["parseInt", "Number", "String", "Boolean", "BigInt", "Array"].includes(name)) features.add("unmodeled-builtin");
      return;
    }
    const method = callee.name.text;
    const receiver = unwrap(callee.expression);
    const label = checker.getApparentType(checker.getTypeAtLocation(receiver)).symbol?.name;
    note("library", `${ts.isIdentifier(receiver) && /^[A-Z]/.test(receiver.text) ? receiver.text : label}.${method}`);
    if (ts.isIdentifier(receiver)) {
      const name = receiver.text;
      if (name === "Math") {
        if (method === "random") return features.add("ambient-effect");
        if (!INTEGER_MATH.has(method)) features.add("fractional");
        return;
      }
      if (name === "Object") {
        if (["keys", "values", "entries"].includes(method) && call.arguments[0]
          && checker.getIndexInfosOfType(checker.getApparentType(checker.getTypeAtLocation(call.arguments[0]))).length) return features.add("record-key");
        if (REFLECTION.has(method)) features.add("reflection");
        return;
      }
      if (name === "JSON" || name === "Reflect") return features.add(name === "JSON" ? "reflection" : "dynamic");
      if (name === "Date") return features.add("date");
      if (name === "Promise") return features.add("async");
      if (AMBIENT.has(name)) return features.add("ambient-effect");
      if (name === "Number" || name === "Array" || name === "BigInt" || name === "String") return;
    }
    const type = checker.getApparentType(checker.getTypeAtLocation(receiver));
    const typeName = type.symbol?.name ?? "";
    if (["Array", "ReadonlyArray", "Map", "ReadonlyMap", "Set", "ReadonlySet"].includes(typeName)) {
      if (MUTATING.has(method)) onWrite(callee.expression, within, true);
      return;
    }
    if (typeName === "String") {
      const argument = call.arguments[0];
      if (REGEX_STRING.has(method) && argument && checker.getTypeAtLocation(argument).symbol?.name === "RegExp") return features.add("regex");
      if (method === "match" || method === "matchAll" || method === "search") return features.add("regex");
      if (!SIMPLE_STRING.has(method)) features.add("unmodeled-builtin");
      return;
    }
    if (typeName === "Number") { if (FRACTIONAL_API.has(method)) features.add("fractional"); else if (!SIMPLE_NUMBER.has(method)) features.add("unmodeled-builtin"); return; }
    if (typeName === "Date") return features.add("date");
    if (typeName === "Promise") return features.add("async");
    if (typeName === "RegExp") return features.add("regex");
    features.add("unmodeled-builtin");
  };

  const visit = (node, scope) => {
    const inner = ts.isFunctionLike(node) ? node : scope;
    switch (node.kind) {
      case ts.SyntaxKind.IfStatement: case ts.SyntaxKind.ConditionalExpression: case ts.SyntaxKind.SwitchStatement:
      case ts.SyntaxKind.ForStatement: case ts.SyntaxKind.ForOfStatement: case ts.SyntaxKind.ForInStatement:
      case ts.SyntaxKind.WhileStatement: case ts.SyntaxKind.DoStatement:
        decisions += 1; break;
      case ts.SyntaxKind.AnyKeyword: note("cast", "any-keyword"); features.add("unchecked-cast"); break;
      case ts.SyntaxKind.AwaitExpression: features.add("async"); break;
      case ts.SyntaxKind.YieldExpression: features.add("generator"); break;
      case ts.SyntaxKind.RegularExpressionLiteral: features.add("regex"); break;
      case ts.SyntaxKind.ThisKeyword: features.add("this-state"); break;
      case ts.SyntaxKind.SuperKeyword: features.add("inheritance"); break;
      case ts.SyntaxKind.ConditionalType: case ts.SyntaxKind.MappedType: features.add("advanced-type"); break;
    }
    if (ts.isForInStatement(node)) features.add("reflection");
    if (ts.isDeleteExpression(node)) features.add("reflection");
    if (ts.isNumericLiteral(node) && !Number.isInteger(Number(node.text))) features.add("fractional");
    if (ts.isIdentifier(node) && !isDeclarationName(node)) onIdentifier(node);
    if (ts.isAsExpression(node) || ts.isTypeAssertionExpression(node)) onCast(node);
    if (ts.isPrefixUnaryExpression(node) || ts.isPostfixUnaryExpression(node)) {
      if (node.operator === ts.SyntaxKind.PlusPlusToken || node.operator === ts.SyntaxKind.MinusMinusToken) onWrite(node.operand, inner);
    }
    if (ts.isBinaryExpression(node)) onBinary(node, inner);
    if (ts.isCallExpression(node)) onCall(node, inner);
    if (ts.isNewExpression(node)) onNew(node);
    if (ts.isElementAccessExpression(node)) onElementAccess(node);
    ts.forEachChild(node, child => visit(child, inner));
  };

  const isDeclarationName = node => {
    const parent = node.parent;
    return (ts.isPropertyAccessExpression(parent) && parent.name === node)
      || (ts.isPropertyAssignment(parent) && parent.name === node)
      || ((ts.isVariableDeclaration(parent) || ts.isParameter(parent) || ts.isBindingElement(parent)) && parent.name === node);
  };

  const onIdentifier = node => {
    if (DYNAMIC.has(node.text)) {
      const declaration = symbolOf(node)?.valueDeclaration;
      if (!declaration || isLibrary(program, declaration)) features.add("dynamic");
      return;
    }
    if (AMBIENT.has(node.text)) {
      const declaration = symbolOf(node)?.valueDeclaration;
      if (!declaration || isLibrary(program, declaration)) features.add("ambient-effect");
    }
  };

  const onCast = node => {
    if (ts.isConstTypeReference(node.type)) return;
    const from = checker.getTypeAtLocation(node.expression);
    const to = checker.getTypeFromTypeNode(node.type);
    if (from.flags & ts.TypeFlags.Any) {
      // Without installed dependencies this may be an unresolved type.
      note("cast", node.expression.kind === ts.SyntaxKind.AsExpression ? "double" : "from-any");
      features.add("unchecked-cast");
    } else if (!checker.isTypeAssignableTo(from, to)) {
      note("cast", "downcast");
      features.add("unchecked-cast");
    }
  };

  const onBinary = (node, scope) => {
    const op = node.operatorToken.kind;
    if (ts.isAssignmentOperator(op)) onWrite(node.left, scope);
    if (op === ts.SyntaxKind.EqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken) {
      const nullCheck = [node.left, node.right].some(side => side.kind === ts.SyntaxKind.NullKeyword
        || (ts.isIdentifier(side) && side.text === "undefined"));
      if (!nullCheck) features.add("coercion");
    }
    if (op === ts.SyntaxKind.InKeyword) features.add("reflection");
    if (op === ts.SyntaxKind.InstanceOfKeyword && !callableClass(node.right)) features.add("reflection");
    if ((op === ts.SyntaxKind.SlashToken || op === ts.SyntaxKind.SlashEqualsToken) && !isBigInt(node)) {
      if (!insideIntegerRounding(node)) features.add("fractional");
    }
    if (op === ts.SyntaxKind.PlusToken) {
      const string = side => (checker.getTypeAtLocation(side).flags & ts.TypeFlags.StringLike) !== 0;
      const number = side => (checker.getTypeAtLocation(side).flags & ts.TypeFlags.NumberLike) !== 0;
      if ((string(node.left) && number(node.right)) || (number(node.left) && string(node.right))) features.add("coercion");
    }
  };

  const callableClass = node => {
    const declaration = symbolOf(node)?.valueDeclaration;
    return Boolean(declaration) && !isLibrary(program, declaration);
  };

  const insideIntegerRounding = node => {
    let current = node.parent;
    while (ts.isParenthesizedExpression(current)) current = current.parent;
    return ts.isCallExpression(current) && current.expression.getText() in { "Math.floor": 1, "Math.ceil": 1, "Math.trunc": 1 };
  };

  const onNew = node => {
    const callee = unwrap(node.expression);
    const signature = checker.getResolvedSignature(node);
    const declaration = signature?.declaration;
    if (ts.isIdentifier(callee)) {
      if (callee.text === "Date") return features.add("date");
      if (callee.text === "RegExp") return features.add("regex");
      if (callee.text === "Proxy" || callee.text === "Function") return features.add("dynamic");
      if (["Map", "Set", "Array", "Error", "TypeError", "RangeError", "WeakMap", "WeakSet"].includes(callee.text)) return;
    }
    if (declaration && !isLibrary(program, declaration) && !ts.isJSDocSignature(declaration)) {
      const target = functionLike(declaration);
      if (target) callees.add(target);
      return;
    }
    const symbol = symbolOf(callee)?.valueDeclaration;
    if (symbol && !isLibrary(program, symbol)) return; // a class with no constructor
    features.add(symbol ? "unmodeled-builtin" : "package-call");
  };

  const onElementAccess = node => {
    const index = checker.getTypeAtLocation(node.argumentExpression);
    if (index.flags & ts.TypeFlags.NumberLike) return;
    const object = checker.getApparentType(checker.getTypeAtLocation(node.expression));
    if (checker.isTupleType?.(object) || checker.isArrayType?.(object)) return;
    if (index.flags & ts.TypeFlags.StringLiteral) return;
    features.add(checker.getIndexInfosOfType(object).length ? "record-key" : "dynamic-key");
  };

  if (fn.body) ts.forEachChild(fn, child => visit(child, fn));
  if (fn.parent && ts.isClassLike(fn.parent) && fn.parent.heritageClauses?.some(h => h.token === ts.SyntaxKind.ExtendsKeyword)) features.add("inheritance");
  if (fn.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) features.add("async");
  return { features, callees, decisions };
}

function exportedFunctions(file, checker) {
  const units = [];
  const exported = node => ts.getCombinedModifierFlags(node) & ts.ModifierFlags.Export;
  for (const statement of file.statements) {
    if (ts.isFunctionDeclaration(statement) && statement.body && exported(statement)) {
      units.push({ name: statement.name?.text ?? "default", node: statement });
    }
    if (ts.isVariableStatement(statement) && exported(statement)) {
      for (const declaration of statement.declarationList.declarations) {
        const target = functionLike(declaration);
        if (target && ts.isIdentifier(declaration.name)) units.push({ name: declaration.name.text, node: target });
      }
    }
    if (ts.isClassDeclaration(statement) && exported(statement)) {
      for (const member of statement.members) {
        const hidden = ts.getCombinedModifierFlags(member) & (ts.ModifierFlags.Private | ts.ModifierFlags.Protected);
        if (ts.isMethodDeclaration(member) && member.body && !hidden) {
          units.push({ name: `${statement.name?.text}.${member.name.getText(file)}`, node: member });
        }
      }
    }
  }
  return units;
}

// Everything a function reaches. Cycles are safe because `seen` is shared.
function cone(start, table) {
  const features = new Set();
  const seen = new Set([start]);
  const stack = [start];
  while (stack.length) {
    const info = table(stack.pop());
    for (const feature of info.features) features.add(feature);
    for (const callee of info.callees) if (!seen.has(callee)) { seen.add(callee); stack.push(callee); }
  }
  return { features, size: seen.size };
}

const IMPURE = new Set(["async", "ambient-effect", "package-call", "this-state", "module-state", "date", "generator"]);

export function tierOf(features) {
  let tier = 2;
  for (const feature of features) tier = Math.max(tier, TIER[feature] ?? 2);
  return tier;
}

export function analyze(program) {
  const checker = program.getTypeChecker();
  const cache = new Map();
  const table = fn => {
    if (!cache.has(fn)) cache.set(fn, inspect(program, checker, fn));
    return cache.get(fn);
  };
  const results = [];
  for (const file of program.getSourceFiles()) {
    if (file.isDeclarationFile || program.isSourceFileFromExternalLibrary(file)) continue;
    for (const unit of exportedFunctions(file, checker)) {
      const { decisions } = table(unit.node);
      const { features, size } = cone(unit.node, table);
      results.push({ file: file.fileName, name: unit.name, logic: decisions > 0, size,
        features: [...features].filter(f => f in TIER).sort(), tier: tierOf(features) });
    }
  }
  return results;
}

export function summarize(results) {
  const logic = results.filter(r => r.logic);
  const within = limit => logic.filter(r => r.tier <= limit).length;
  const blockers = {}, sole = {};
  for (const result of logic) {
    const hard = result.features.filter(f => TIER[f] === 9);
    for (const feature of hard) blockers[feature] = (blockers[feature] ?? 0) + 1;
    if (hard.length === 1) sole[hard[0]] = (sole[hard[0]] ?? 0) + 1;
  }
  // Functions that compute a result from their inputs, the natural proof targets.
  const pure = logic.filter(r => !r.features.some(f => IMPURE.has(f)));
  return { functions: results.length, logic: logic.length, m2: within(2), m3: within(3), models: within(4),
    pure: pure.length, pureM2: pure.filter(r => r.tier <= 2).length, pureM3: pure.filter(r => r.tier <= 3).length,
    blockers, sole };
}

// Which features to add, in order, and how many functions each one unlocks.
export function adoptionOrder(results, steps = 8) {
  let pending = results.filter(r => r.logic).map(r => new Set(r.features.filter(f => TIER[f] === 9)));
  const covered = () => pending.filter(set => set.size === 0).length;
  const total = pending.length;
  const order = [{ feature: "(planned subset)", covered: covered(), total }];
  for (let step = 0; step < steps; step += 1) {
    const candidates = new Set(pending.flatMap(set => [...set]));
    if (!candidates.size) break;
    let best, bestCovered = -1;
    for (const feature of [...candidates].sort()) {
      const count = pending.filter(set => set.size === 0 || (set.size === 1 && set.has(feature))).length;
      if (count > bestCovered) { best = feature; bestCovered = count; }
    }
    pending = pending.map(set => { const next = new Set(set); next.delete(best); return next; });
    order.push({ feature: best, covered: bestCovered, total });
  }
  return order;
}
