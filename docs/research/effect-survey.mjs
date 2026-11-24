// Survey of Effect API usage in a repository, using the TypeScript compiler API.
// Usage: node effect-survey.mjs <repo-root> [dir,dir,...]
//   node docs/research/effect-survey.mjs ~/t3code apps/server,packages,apps/web
//
// Reads every .ts/.tsx file under the given directories (default: the repo root),
// skipping node_modules, .repos, dist/build output and *.test.*/*.spec.* files.
// No dependencies are needed besides the `typescript` package itself: the survey
// is syntactic. It binds each import specifier whose source starts with "effect"
// to its module ("effect/Effect", "effect/Schema", ...) and counts call sites,
// `yield*` inside `Effect.gen`, `pipe(...)` free calls and `.pipe(...)` chains,
// exported functions whose return type mentions Effect, and `Effect` values that
// appear only inside `pipe`/`andThen` style composition.
//
// The output is JSON: per-module member counts, construct counts, and the split
// between pure and Effect-returning exported functions.

import { createRequire } from "node:module";
import { readdirSync, statSync, readFileSync } from "node:fs";
import { join, relative } from "node:path";

// The script has no install of its own: point TS_SURVEY_REQUIRE at a file inside
// an installed node_modules tree (e.g. typescript/node_modules/x or any package.json)
// when "typescript" is not resolvable from this file's location.
const req = createRequire(process.env.TS_SURVEY_REQUIRE ?? import.meta.url);
const ts = req("typescript");

const root = process.argv[2];
const dirs = (process.argv[3] ?? "").split(",").filter(Boolean);

const SKIP_DIR = new Set(["node_modules", ".repos", "dist", "build", ".output", ".tanstack", "coverage", ".next", ".turbo"]);
const SKIP_FILE = /\.(test|spec|stories)\.[tj]sx?$/;

function* walk(dir) {
  let entries;
  try { entries = readdirSync(dir); } catch { return; }
  for (const name of entries) {
    if (SKIP_DIR.has(name)) continue;
    const p = join(dir, name);
    let st;
    try { st = statSync(p); } catch { continue; }
    if (st.isDirectory()) yield* walk(p);
    else if (/\.[tj]sx?$/.test(name) && !name.endsWith(".d.ts") && !SKIP_FILE.test(name)) yield p;
  }
}

const memberCounts = new Map();   // "Effect.gen" -> n call sites
const moduleUse = new Map();      // local name -> { module, imported }  (per file, reset)
const construct = new Map();      // high-level constructs
const files = { total: 0, importingEffect: 0 };
const fnStats = { exportedTotal: 0, exportedEffect: 0, exportedPure: 0, exportedEffectCoreOnly: 0, effectFnsDetail: [] };
// Per-phase split of the core-only exports (see the doc's phase plan):
// phase 1 covers R = never (no service access, no promise bridge);
// phase 2 adds `yield* ServiceTag` / `Effect.service`; phase 3 adds
// `Effect.tryPromise`/`promise`. `needsService` is syntactic: a service
// access call, or `yield* <CapitalizedIdentifier>` (the v4 Context.Service
// tag idiom — a yielded capitalized identifier is a tag, never an Effect API).
const phase = { p1RN: 0, p2WithServices: 0, p3WithPromises: 0 };
// `Effect.fn("n")(function*…, combinator…)` — the curried second call carries
// combinators (catchTag/withSpan/…) besides the generator body.
let fnWithPipeArgs = 0;

// The "core subset" a first Effect translation could cover: sequential composition
// (gen/yield*, fn wrappers, map/flatMap/andThen/tap), construction (succeed/fail/
// sync/try/tryPromise/promise/suspend), typed-error recovery (catch*, orElse*,
// mapError, tapError), aggregation (all/forEach), service access (service/
// provideService/provide) and tracing-side annotations that can drop out
// (log*, annotate*, withSpan). Excluded: concurrency (fork/race/sleep/timeout/
// uninterruptible), scopes/finalizers (acquireRelease/ensuring/scoped), retries
// (retry/repeat/Schedule), Cause/Exit, streaming (Stream), STM-ish state
// (Ref/Deferred/Queue/Semaphore).
const CORE = new Set([
  "Effect.gen", "Effect.fn", "Effect.fnUntraced", "Effect.succeed", "Effect.fail",
  "Effect.sync", "Effect.try", "Effect.tryPromise", "Effect.promise",
  "Effect.map", "Effect.flatMap", "Effect.andThen", "Effect.tap",
  "Effect.tapError", "Effect.catch", "Effect.catchTag", "Effect.catchTags",
  "Effect.catchAll", "Effect.catchIf", "Effect.orElse", "Effect.orElseSucceed",
  "Effect.orElseFail", "Effect.mapError", "Effect.all", "Effect.forEach",
  "Effect.as", "Effect.asVoid", "Effect.zipRight", "Effect.zipLeft",
  "Effect.zipWith", "Effect.suspend", "Effect.service", "Effect.provideService",
  "Effect.provide", "Effect.logDebug", "Effect.logInfo", "Effect.logWarning",
  "Effect.logError", "Effect.annotateLogs", "Effect.annotateCurrentSpan",
  "Effect.withSpan", "Effect.ignore", "Effect.fromOption", "Effect.fromResult",
  "Effect.succeedSome", "Effect.filterOrFail", "Effect.filterOrElse",
  "Effect.flatten", "Effect.option", "Effect.findFirst",
  "Effect.log", "Effect.provideContext", "Effect.orDie", "Effect.die",
  "Effect.dieMessage", "Effect.filterOrDie", "Effect.orElseDie",
]);

const bump = (map, key, n = 1) => map.set(key, (map.get(key) ?? 0) + n);

function propName(node) {
  // a.b.c(...) -> "a.b"; local name resolved via imports later
  if (ts.isPropertyAccessExpression(node)) {
    const left = propName(node.expression);
    return left ? `${left}.${node.name.text}` : null;
  }
  if (ts.isIdentifier(node)) return node.text;
  return null;
}

function isExported(node) {
  // export function/const/let, or a function inside an exported variable statement
  if (node.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)) return true;
  let p = node.parent;
  while (p && (ts.isVariableDeclaration(p) || ts.isVariableDeclarationList(p))) p = p.parent;
  return Boolean(p && ts.isVariableStatement(p) && isExported(p));
}

function returnMentionsEffect(fn) {
  const t = fn.type;
  if (!t) return undefined; // unknown without the checker
  const s = t.getText();
  return /\bEffect\b/.test(s) || /\bEffect\.Effect\b/.test(s);
}

// local name -> qualified "Module.member". Effect v4 style
// `import { Effect } from "effect"` and `import { Schema } from "effect/Schema"`
// both make `Effect`/`Schema` a namespace: `Effect.gen` reports as "Effect.gen".
// `import * as fx from "effect"` reaches the same namespaces one level down:
// `fx.Effect.gen` is "Effect.gen" too.
function makeQualify(bindings) {
  return (path) => {
    const head = path.split(".")[0];
    const b = bindings.get(head);
    if (!b) return null;
    const rest = path.slice(head.length + 1);
    if (!rest) return `${b.moduleName}.${b.imported}`;
    // `fx.Effect.gen` through the `effect` barrel resolves to the `Effect`
    // namespace; a named import (`{ Schema }`) keeps its own prefix instead.
    if (b.imported === "*" && b.moduleName === "effect" && /^[A-Z]/.test(rest)) return rest;
    const ns = /^[A-Z]/.test(b.imported) ? b.imported : b.moduleName;
    return `${ns}.${rest}`;
  };
}

// Qualified names referenced inside `n`, split into `calls` (call-expression
// callees) and `refs` (all references, calls included) — `.pipe(Effect.scoped)`
// is caught even though `Effect.scoped` is never called, while a bare
// `values.map(Effect.succeed)` reference does not make the export
// Effect-returning. A call to `Effect.all`/`Effect.forEach` carrying a
// `concurrency` option is reported as "Effect.concurrent" — outside CORE.
function scanCalls(n, qualify) {
  const calls = new Set();
  const refs = new Set();
  const scan = (m) => {
    if (ts.isYieldExpression(m) && m.expression) {
      const y = m.expression;
      if (ts.isIdentifier(y) && /^[A-Z]/.test(y.text)) {
        refs.add("effect.serviceTagYield");
      } else if (ts.isPropertyAccessExpression(y) && /^[A-Z]/.test(y.name.text)) {
        // `yield* Mac.Mac` / `yield* Digest.Digest`: a service tag reached
        // through a module namespace. Excluded: members that resolve to an
        // Effect API (qualify starts with "Effect.") — those are values.
        const yq = qualify(propName(y) ?? "");
        if (yq === null || !yq.startsWith("Effect.")) refs.add("effect.serviceTagYield");
      }
    }
    if (ts.isCallExpression(m)) {
      const path = propName(m.expression);
      const q = path && qualify(path);
      if (q) {
        const concurrent = (q === "Effect.all" || q === "Effect.forEach")
          && m.arguments.slice(1).some(a => a.getText().includes("concurrency"));
        calls.add(concurrent ? "Effect.concurrent" : q);
        refs.add(concurrent ? "Effect.concurrent" : q);
      }
    } else if (ts.isPropertyAccessExpression(m) || ts.isIdentifier(m)) {
      // skip the head identifier of a property access (`Effect` in `Effect.gen`) —
      // the access itself is recorded as one name.
      if (ts.isIdentifier(m) && m.parent && ts.isPropertyAccessExpression(m.parent)
          && m.parent.expression === m) {
        // fall through to children
      } else {
        const path = propName(m);
        const q = path && qualify(path);
        if (q) refs.add(q);
      }
    }
    ts.forEachChild(m, scan);
  };
  scan(n);
  return { calls, refs };
}

// 2. exported functions: pure vs Effect-returning.
// An exported function counts as Effect-returning when its return type
// mentions Effect, or (unannotated) its body builds an Effect value — either
// way it lands in the same bucket for the survey. For each Effect-returning
// function we also record whether every Effect.* call inside it is in CORE.
function countExports(path, sf, bindings) {
  const qualify = makeQualify(bindings);
  const classify = (n, label, { calls, refs }) => {
    fnStats.exportedTotal++;
    const ret = ts.isFunctionLike(n) ? returnMentionsEffect(n) : undefined;
    // References include type positions (`Effect.Effect`, `Effect.fn.Return`),
    // which must not decide Effect-ness or subset coverage.
    const NON_API = /^(Effect\.Effect|Effect\.(fn|fnUntraced)\.Return|Effect\.Service)$/;
    const isApi = (q) => q.startsWith("Effect.") && !NON_API.test(q);
    const callApis = [...calls].filter(isApi);
    const refApis = [...refs].filter(isApi);
    // "Returns an Effect" means the body *builds* one: an Effect.* call (or the
    // annotation) — a bare reference like `values.map(Effect.succeed)` and a
    // pure `pipe(...)` pipeline don't count.
    const buildsEffect = callApis.length > 0;
    if (ret === true || (ret !== false && buildsEffect)) {
      fnStats.exportedEffect++;
      // Covered by the core subset only when every Effect.* reference is in CORE
      // and the function touches none of the runtime-state / concurrency modules.
      const BLOCKED = /^(Ref|Deferred|Queue|Semaphore|Stream|Scope|Schedule|Fiber|Cause|Exit|SubscriptionRef|PubSub|Layer|Atom|reactivity)\./;
      const blocked = [...refs].some(q => BLOCKED.test(q));
      if (refApis.length && refApis.every(q => CORE.has(q)) && !blocked) {
        fnStats.exportedEffectCoreOnly++;
        const usesService = refApis.some(q =>
          /^(Effect\.(service|provideService|provide|provideContext))$/.test(q))
          || refs.has("effect.serviceTagYield");
        const usesPromise = callApis.some(q => q === "Effect.tryPromise" || q === "Effect.promise");
        if (!usesService && !usesPromise) phase.p1RN++;
        if (!usesPromise) phase.p2WithServices++;
        phase.p3WithPromises++;
      }
      fnStats.effectFnsDetail.push(label);
    } else {
      fnStats.exportedPure++;
    }
  };
  const fnVisit = (n) => {
    const isFn = ts.isFunctionDeclaration(n) || ts.isArrowFunction(n) || ts.isFunctionExpression(n) || ts.isMethodDeclaration(n);
    if (isFn && isExported(n) && (n.name || ts.isVariableDeclaration(n.parent))) {
      classify(n, relative(root, path) + "::" + (n.name?.text ?? n.parent?.name?.text ?? "?"), scanCalls(n.body ?? n, qualify));
    } else if (ts.isVariableDeclaration(n) && n.initializer && isExported(n)
        && !ts.isArrowFunction(n.initializer) && !ts.isFunctionExpression(n.initializer)
        && ts.isCallExpression(n.initializer)) {
      // export const f = Effect.fn("f")(function* ...) / pipe(...)/Effect.gen(...)
      classify(n, relative(root, path) + "::" + (n.name?.text ?? "?"), scanCalls(n.initializer, qualify));
    }
    ts.forEachChild(n, fnVisit);
  };
  fnVisit(sf);
}

function fileEffectCalls(file, sf, bindings) {
  // Collect the set of Effect.* APIs this file uses, to classify its functions.
  const used = new Set();
  ts.forEachChild(sf, function visit(n) {
    if (ts.isCallExpression(n)) {
      const path = propName(n.expression);
      if (path) {
        const head = path.split(".")[0];
        const b = bindings.get(head);
        if (b) used.add(`${b.moduleName}.${path.slice(head.length + 1)}`);
      }
    }
    ts.forEachChild(n, visit);
  });
  return used;
}

function surveyFile(path, sf) {
  // 1. bind imports from "effect*" modules
  const bindings = new Map(); // local name -> { moduleName, imported }
  let importsEffect = false;
  for (const st of sf.statements) {
    if (!ts.isImportDeclaration(st) || !ts.isStringLiteral(st.moduleSpecifier)) continue;
    const mod = st.moduleSpecifier.text;
    if (mod !== "effect" && !mod.startsWith("effect/")) continue;
    importsEffect = true;
    const c = st.importClause;
    if (!c) continue;
    const modShort = mod === "effect" ? "effect" : mod.slice("effect/".length);
    if (c.name) bindings.set(c.name.text, { moduleName: modShort, imported: "default" });
    if (c.namedBindings) {
      if (ts.isNamespaceImport(c.namedBindings)) {
        bindings.set(c.namedBindings.name.text, { moduleName: modShort, imported: "*" });
      } else {
        for (const el of c.namedBindings.elements) {
          bindings.set(el.name.text, { moduleName: modShort, imported: (el.propertyName ?? el.name).text });
        }
      }
    }
  }
  bump(construct, "files", 1);
  // Exported functions are counted for every file, importing or not: a file
  // with no effect import contributes its exports to the non-Effect bucket.
  countExports(path, sf, bindings);
  if (!importsEffect) return;
  bump(construct, "files_importing_effect", 1);
  files.importingEffect++;

  const qualify = makeQualify(bindings);

  const usedByFile = new Set();
  const visit = (n) => {
    // call sites: Effect.gen(...), Schema.decode(...), tag members, pipe(...)
    if (ts.isCallExpression(n)) {
      const expr = n.expression;
      if (ts.isPropertyAccessExpression(expr) && expr.name.text === "pipe") {
        bump(construct, "dot_pipe_chain", 1);
      }
      const path = propName(expr);
      const q = path && qualify(path);
      if (q) {
        bump(memberCounts, q, 1);
        usedByFile.add(q);
        if (q === "Effect.gen") {
          // count yield* inside the generator argument
          const g = n.arguments[0];
          let yields = 0;
          const cy = (m) => {
            if (ts.isYieldExpression(m)) yields++;
            ts.forEachChild(m, cy);
          };
          if (g) ts.forEachChild(g, cy);
          bump(construct, "Effect.gen_bodies", 1);
          bump(construct, "yield_star_in_gen", yields);
        }
      } else if (path === "pipe" || (bindings.has("pipe") && ts.isIdentifier(expr) && expr.text === "pipe")) {
        bump(construct, "pipe_free_call", 1);
      }
      // `Effect.fn("n")(gen, combinator…)`: the outer call's callee is itself
      // a call (`Effect.fn("n")`), so it never produces a qualified `q` —
      // detect it by resolving the *inner* callee.
      if (ts.isCallExpression(expr)) {
        const innerPath = propName(expr.expression);
        const iq = innerPath && qualify(innerPath);
        if ((iq === "Effect.fn" || iq === "Effect.fnUntraced") && n.arguments.length > 1) fnWithPipeArgs++;
      }
    }
    // yield* outside gen bodies still counts as Effect generator syntax
    if (ts.isYieldExpression(n)) bump(construct, "yield_total", 1);
    // class X extends (Data|Schema).TaggedError / Schema.TaggedStruct / Effect.Service / Context.Tag
    if (ts.isClassDeclaration(n)) {
      for (const h of n.heritageClauses ?? []) {
        for (const t of h.types) {
          const path = propName(t.expression);
          const q = path && qualify(path);
          if (q) { bump(memberCounts, `extends ${q}`, 1); usedByFile.add(q); }
        }
      }
    }
    ts.forEachChild(n, visit);
  };
  visit(sf);


  // 3. file-level core-subset classification: does the file use only CORE Effect.* APIs?
  const effectApis = [...usedByFile].filter(q => q.startsWith("Effect."));
  if (effectApis.length && effectApis.every(q => CORE.has(q))) bump(construct, "files_core_only", 1);
}

const roots = dirs.length ? dirs.map(d => join(root, d)) : [root];
for (const r of roots) {
  for (const f of walk(r)) {
    files.total++;
    let sf;
    try { sf = ts.createSourceFile(f, readFileSync(f, "utf8"), ts.ScriptTarget.Latest, true, f.endsWith("x") ? ts.ScriptKind.TSX : ts.ScriptKind.TS); }
    catch { continue; }
    surveyFile(f, sf);
  }
}

// core-subset coverage over Effect-returning functions is computed by the caller from
// memberCounts; files_core_only above is the file-level analogue.
const out = {
  files,
  construct: Object.fromEntries([...construct].sort((a, b) => b[1] - a[1])),
  members: Object.fromEntries([...memberCounts].sort((a, b) => b[1] - a[1])),
  exportedFunctions: { total: fnStats.exportedTotal, effect: fnStats.exportedEffect, nonEffect: fnStats.exportedPure, effectCoreOnly: fnStats.exportedEffectCoreOnly },
  phases: { phase1_noServices_noPromises: phase.p1RN, phase1_2_withServices: phase.p2WithServices, phase1_3_withPromises: phase.p3WithPromises },
  effectFnWithPipeArgs: fnWithPipeArgs,
  effectFnsSample: fnStats.effectFnsDetail.slice(0, 400),
};
console.log(JSON.stringify(out, null, 1));
