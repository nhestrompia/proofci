// Resolves `typeof X.Type` / Schema-class type references in exported-function
// signatures and classifies what the TypeScript checker says they are:
// structural records, literal unions, Schema.Class instances, intersections
// (brands), transformations, or unresolved.
// Usage: TS_SURVEY_REQUIRE=<pkg.json> node schema-types-survey.mjs <repo-root> [dirs]
// Requires the `effect` package resolvable from <repo-root> (e.g. a symlink at
// <repo-root>/node_modules/effect) or Schema types resolve to `any`.

import { createRequire } from "node:module";
import { readdirSync, statSync } from "node:fs";
import { join } from "node:path";

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

const files = [];
const roots = dirs.length ? dirs.map(d => join(root, d)) : [root];
for (const r of roots) for (const f of walk(r)) files.push(f);

const program = ts.createProgram(files, {
  target: ts.ScriptTarget.ESNext,
  module: ts.ModuleKind.NodeNext,
  moduleResolution: ts.ModuleResolutionKind.NodeNext,
  strict: true,
  skipLibCheck: true,
  noEmit: true,
  noResolve: false,
});
const checker = program.getTypeChecker();

const classes = new Map(); // category -> count
const bump = (k) => classes.set(k, (classes.get(k) ?? 0) + 1);
const samples = new Map();
const remember = (k, v) => { if (!samples.has(k)) samples.set(k, v); };

function isSchemaClassDecl(decl) {
  if (!decl || !ts.isClassDeclaration(decl)) return false;
  return (decl.heritageClauses ?? []).some(h =>
    h.types.some(t => /^(Schema|Data|Effect)\./.test(t.expression.getText())));
}

function classifyType(t) {
  if (t.flags & ts.TypeFlags.Any || t.flags & ts.TypeFlags.Unknown) return "unresolved (any/unknown)";
  if (t.isUnion()) {
    const lits = t.types.every(u =>
      u.isLiteral() || (u.flags & ts.TypeFlags.Undefined) || (u.flags & ts.TypeFlags.Void)
      || (u.flags & ts.TypeFlags.Null) || (u.flags & ts.TypeFlags.BooleanLiteral));
    return lits ? "literal union" : "union (non-literal members)";
  }
  if (t.isIntersection()) return "intersection (brand? transform?)";
  if (t.flags & (ts.TypeFlags.String | ts.TypeFlags.Number | ts.TypeFlags.Boolean
      | ts.TypeFlags.StringLiteral | ts.TypeFlags.NumberLiteral | ts.TypeFlags.BooleanLiteral
      | ts.TypeFlags.BigInt | ts.TypeFlags.ESSymbol)) return "primitive";
  if (t.flags & ts.TypeFlags.Object || t.flags & ts.TypeFlags.NonPrimitive) {
    const sym = t.getSymbol() ?? t.aliasSymbol;
    const decls = sym?.declarations ?? [];
    if (decls.some(isSchemaClassDecl)) return "Schema.Class / TaggedError instance";
    if (decls.some(d => ts.isClassDeclaration(d))) return "class instance";
    if (t.getCallSignatures().length > 0 || t.getConstructSignatures().length > 0) return "callable/constructor";
    if (t.getProperties().length > 0 || t.getStringIndexType() || t.getNumberIndexType()) return "structural record";
    return "other object";
  }
  if (t.isTypeParameter?.()) return "type parameter";
  return "other";
}

// Does this annotation reference a Schema-derived type? Covers the common
// indirection `type X = typeof X.Type`/`Schema.Schema<...>`/alias chains:
// resolve the annotation, then look at the type's own declarations — a class
// extending Schema.*, or a TypeAliasDeclaration whose body is a
// `typeof X.Type`/`X.Type`/`Schema.*` reference.
function declIsSchemaDerived(decl) {
  if (!decl) return false;
  if (isSchemaClassDecl(decl)) return true;
  if (ts.isTypeAliasDeclaration(decl)) return /\btypeof\s+\w+\.(Type|Encoded)\b|\b\w+\.(Type|Encoded)\b|\bSchema\./.test(decl.type.getText());
  if (ts.isInterfaceDeclaration(decl) || ts.isTypeParameterDeclaration(decl)) return false;
  if (ts.isClassDeclaration(decl)) return isSchemaClassDecl(decl);
  return false;
}

function annotationIsSchemaDerived(node) {
  if (/\btypeof\s+\w+\.(Type|Encoded)\b|\bSchema\.(Type|Struct|Class|Union|Literal|optional|brand|TaggedError|TaggedStruct|declare|fromBrand|Schema)\b/.test(node.getText())) return true;
  const t = checker.getTypeAtLocation(node);
  const syms = [t.symbol, t.aliasSymbol].filter(Boolean);
  return syms.some(s => (s.declarations ?? []).some(declIsSchemaDerived));
}

let schemaSites = 0, totalSites = 0;
for (const f of files) {
  const sf = program.getSourceFile(f);
  if (!sf) continue;
  const visit = (n) => {
    const isFn = ts.isFunctionDeclaration(n) || ts.isArrowFunction(n)
      || ts.isFunctionExpression(n) || ts.isMethodDeclaration(n);
    if (isFn && (n.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)
        || (n.parent && ts.isVariableDeclaration(n.parent)
            && n.parent.parent?.parent?.modifiers?.some(m => m.kind === ts.SyntaxKind.ExportKeyword)))) {
      const nodes = [...(n.parameters ?? []).map(p => p.type), n.type].filter(Boolean);
      for (const tn of nodes) {
        totalSites++;
        if (!annotationIsSchemaDerived(tn)) continue;
        schemaSites++;
        const t = checker.getTypeAtLocation(tn);
        const cat = classifyType(t);
        bump(cat);
        remember(cat, `${f.replace(root + "/", "")} :: ${tn.getText().slice(0, 80)} -> ${checker.typeToString(t).slice(0, 80)}`);
      }
    }
    ts.forEachChild(n, visit);
  };
  visit(sf);
}

console.log(JSON.stringify({
  signatureSites: totalSites,
  schemaDerivedSites: schemaSites,
  categories: Object.fromEntries([...classes].sort((a, b) => b[1] - a[1])),
  samples: Object.fromEntries(samples),
}, null, 1));
