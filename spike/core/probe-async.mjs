// How many of a repository's top-level async logic functions the real translator accepts.
// MODE=none: nothing listed under `effects`, as in a repository that has not written a policy.
// MODE=all:  every awaited call that resolves to a function is listed with its own signature, which is
//            the most a policy could do. Calls that aren't to a function the translator can see still stop it.
// The input is the census of typescript-support's async study (classify.mjs); only the translator decides.
// usage: MODE=none|all node probe-async.mjs <repo root> <census.json> <out.json>
import { readFileSync, realpathSync, writeFileSync } from "node:fs";
import { relative, sep } from "node:path";
import ts from "../../typescript/node_modules/typescript/lib/typescript.js";
const W = new URL("../../typescript/", import.meta.url).pathname;
const T = await import(`${W}translate.mjs`);
const { workspacePaths } = await import(`${W}survey/analyze.mjs`);
const MODE = process.env.MODE ?? "none";
const [root, census, out] = process.argv.slice(2);

if (MODE === "all") {
  let counter = 0;
  const original = T.Scope.prototype.effectFor;
  T.Scope.prototype.effectFor = function (callee, node) {
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
    if (!key || !signature) return undefined;
    // Only a call that returns a promise is an effect; the signature is listed as the compiler reports it.
    const entry = { id: `auto${counter++}`, call: key, signature: this.checker.signatureToString(signature), kind: "read" };
    this.t.effects.set(key, entry);
    return { key, entry };
  };
}

const rows = JSON.parse(readFileSync(census, "utf8"));
const targets = rows.filter(r => r.exported && r.async && r.logic && r.kind === "function" && r.file.endsWith(".ts") && !r.file.startsWith("/") && !r.name.includes("."));
const keys = [...new Set(targets.map(r => `${r.file}::${r.name}`))];
const translator = new T.Translator(root, keys, workspacePaths(root));
const result = {};
for (const requireTypes of [false, true]) {
  translator.requireTypes = requireTypes;
  for (const key of keys) {
    translator.functions = new Map(); translator.current = []; translator.order = []; translator.types = new Map();
    translator.constants = new Map(); translator.anonymous = new Map(); translator.effectOps = new Map(); translator.assumed = new Map();
    translator.typeOwners = new Map(); translator.argsBy = new Map(); translator.effectsBy = new Map();
    let reason = null;
    try {
      const declaration = T.findDeclaration(translator, key);
      translator.declareFunction(declaration);
    } catch (error) {
      if (!(error instanceof T.Unsupported)) reason = `(crash) ${String(error.message).slice(0, 80)}`;
      else reason = error.message.replace(/^[^:]*:\d+: /, "").replace(/`[^`]*`/g, "`_`").replace(/\d+/g, "N").slice(0, 90);
    }
    (result[key] ??= {})[requireTypes ? "typed" : "free"] = reason;
  }
}
writeFileSync(out, JSON.stringify({ mode: MODE, repo: root.split("/").pop(), rows: targets.map(r => ({ id: r.id, key: `${r.file}::${r.name}`, ...result[`${r.file}::${r.name}`] })) }));
const accepted = Object.values(result).filter(r => r.typed === null).length;
console.log(root.split("/").pop(), MODE, keys.length, "accepted:", accepted, "(types not required:", Object.values(result).filter(r => r.free === null).length + ")");
