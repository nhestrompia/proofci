// Every reason the real translator stops an async function, not only the first, over a repository's
// top-level async logic functions. It is the async study's cut-off probe (DESIGN.md, "Evidence: what async
// alone buys") run on the real async translation: each awaited call to a function is listed as an effect with
// its own signature, the most a policy could do, and every other limit is counted by `survey/blockers.mjs`.
// The input is the census of the async study (classify.mjs). Only the translator decides.
// usage: node probe-reasons.mjs <repo root> <census.json> <out.json>
import { readFileSync, realpathSync, writeFileSync } from "node:fs";
import { relative, sep } from "node:path";
import ts from "../../typescript/node_modules/typescript/lib/typescript.js";
const W = new URL("../../typescript/", import.meta.url).pathname;
const T = await import(`${W}translate.mjs`);
const B = await import(`${W}survey/blockers.mjs`);
const { workspacePaths } = await import(`${W}survey/analyze.mjs`);
const [root, census, out] = process.argv.slice(2);

let counter = 0;
const original = T.Scope.prototype.effectFor;
T.Scope.prototype.effectFor = function (callee, node) {
  // A call on an object (a handle) is listed as a `method` effect with its own signature, as a policy could.
  if (ts.isPropertyAccessExpression(callee)) {
    const receiver = this.checker.getTypeAtLocation(callee.expression);
    const owner = receiver.flags & ts.TypeFlags.Object ? this.t.handleOf?.(receiver) : undefined;
    const signature = owner && this.checker.getResolvedSignature(node);
    const key = owner && `${owner}#${callee.name.text}`;
    if (key && signature && this.checker.getReturnTypeOfSignature(signature).symbol?.name === "Promise" && this.t.methodEffects && !this.t.methodEffects.has(key)) {
      this.t.methodEffects.set(key, { id: `auto${counter++}`, method: key, signature: this.checker.signatureToString(signature), kind: "read" });
    }
  }
  const listed = original.call(this, callee, node);
  if (listed || !ts.isIdentifier(callee)) return listed;
  let symbol = this.checker.getSymbolAtLocation(callee);
  if (!symbol) return undefined;
  const outside = this.outsideName(callee);
  if (symbol.flags & ts.SymbolFlags.Alias) symbol = this.checker.getAliasedSymbol(symbol);
  const declaration = symbol.valueDeclaration ?? symbol.declarations?.[0];
  let key = outside;
  if (declaration && !declaration.getSourceFile().isDeclarationFile) {
    const name = ts.isFunctionDeclaration(declaration) ? declaration.name?.text
      : ts.isVariableDeclaration(declaration) && ts.isIdentifier(declaration.name) ? declaration.name.text : undefined;
    if (name) key = `${relative(this.t.root, realpathSync(declaration.getSourceFile().fileName)).split(sep).join("/")}::${name}`;
  }
  const signature = this.checker.getResolvedSignature(node);
  if (!key || !signature || this.checker.getReturnTypeOfSignature(signature).symbol?.name !== "Promise") return undefined;
  const entry = { id: `auto${counter++}`, call: key, signature: this.checker.signatureToString(signature), kind: "read" };
  this.t.effects.set(key, entry);
  return { key, entry };
};

const rows = JSON.parse(readFileSync(census, "utf8"));
const targets = rows.filter(r => r.exported && r.async && r.logic && r.kind === "function" && r.file.endsWith(".ts") && !r.file.startsWith("/") && !r.name.includes("."));
const keys = [...new Set(targets.map(r => `${r.file}::${r.name}`))];
const result = B.measure(root, keys, workspacePaths(root), { keepAsync: true });
const byKey = new Map(result.map(r => [r.target, r]));
writeFileSync(out, JSON.stringify({ rows: targets.map(r => ({ id: r.id, repo: r.repo, file: r.file, name: r.name, ...byKey.get(`${r.file}::${r.name}`) })) }));
const free = result.filter(r => r.blockers && !r.blockers.length).length;
console.log(root.split("/").pop(), keys.length, "no blocker:", free);
