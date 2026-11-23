// Say which exported functions of a package the translator accepts, and why it
// refuses the others. For coding agents: run this before writing a guarantee to
// know what can be named in proofci.yaml. Reads and type-checks the code, never
// runs it.
//
// Usage: node probe.mjs <config.json>
//   config: { root, module, repository, assumes, effects }
// Prints a JSON result on stdout.

import { readFileSync, realpathSync } from "node:fs";
import { relative, sep } from "node:path";
import ts from "typescript";
import { OPTIONS, translate } from "./translate.mjs";
import { workspacePaths } from "./paths.mjs";

// Exported function declarations and exported `const f = (...) => ...`: what a
// manifest target can name. Class methods and re-exports can't, so they are
// left out rather than reported as refused.
function targets(root, program) {
  const exported = node => Boolean(ts.getCombinedModifierFlags(node) & ts.ModifierFlags.Export);
  const functionNames = statement => {
    if (ts.isFunctionDeclaration(statement) && statement.body && statement.name) return [statement.name.text];
    if (ts.isVariableStatement(statement)) {
      return statement.declarationList.declarations
        .filter(d => ts.isIdentifier(d.name) && d.initializer
          && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer)))
        .map(d => d.name.text);
    }
    return [];
  };
  const found = [];
  for (const file of program.getSourceFiles()) {
    if (file.isDeclarationFile || program.isSourceFileDefaultLibrary(file)
        || program.isSourceFileFromExternalLibrary(file)) continue;
    const path = relative(root, realpathSync(file.fileName)).split(sep).join("/");
    if (path.startsWith("..")) continue;
    const declared = new Map();
    const exportedNames = new Set();
    for (const statement of file.statements) {
      for (const name of functionNames(statement)) {
        declared.set(name, statement);
        if (exported(statement)) exportedNames.add(name);
      }
      // `export { f }` exports a declaration that carries no modifier of its own.
      // `export type { f }` and `export { type f }` export only its type.
      if (ts.isExportDeclaration(statement) && !statement.moduleSpecifier && !statement.isTypeOnly
          && ts.isNamedExports(statement.exportClause)) {
        for (const element of statement.exportClause.elements) {
          if (!element.isTypeOnly) exportedNames.add((element.propertyName ?? element.name).text);
        }
      }
    }
    for (const name of exportedNames) {
      if (declared.has(name)) found.push(`${path}::${name}`);
    }
  }
  return found.sort();
}

export function probe({ root, module, repository, assumes, effects }) {
  const files = ts.sys.readDirectory(root, [".ts"], undefined, undefined);
  const program = ts.createProgram(files, { ...OPTIONS, paths: workspacePaths(repository ?? root) });
  const list = targets(root, program);
  const result = translate({ root, module: module ?? "Probe", targets: list, repository: repository ?? root,
    paths: workspacePaths(repository ?? root), requireTypes: true, assumes: assumes ?? [], effects: effects ?? [] });
  return { module: result.module, functions: list.map(function_ => ({
    function: function_,
    translated: !(function_ in result.failures),
    ...(result.failures[function_] ? { reason: result.failures[function_] } : {}),
  })), ...(result.fatal ? { fatal: result.fatal } : {}) };
}

if (process.argv[1]?.endsWith("probe.mjs")) {
  const config = JSON.parse(readFileSync(process.argv[2], "utf8"));
  console.log(JSON.stringify(probe(config)));
}
