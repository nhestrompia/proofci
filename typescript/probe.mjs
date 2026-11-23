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
  const found = [];
  for (const file of program.getSourceFiles()) {
    if (file.isDeclarationFile || program.isSourceFileDefaultLibrary(file)
        || program.isSourceFileFromExternalLibrary(file)) continue;
    const path = relative(root, realpathSync(file.fileName)).split(sep).join("/");
    if (path.startsWith("..")) continue;
    for (const statement of file.statements) {
      if (ts.isFunctionDeclaration(statement) && statement.body && statement.name && exported(statement)) {
        found.push(`${path}::${statement.name.text}`);
      } else if (ts.isVariableStatement(statement) && exported(statement)) {
        for (const declaration of statement.declarationList.declarations) {
          const init = declaration.initializer;
          if (ts.isIdentifier(declaration.name) && init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init))) {
            found.push(`${path}::${declaration.name.text}`);
          }
        }
      }
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
