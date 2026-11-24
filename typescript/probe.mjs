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
import { OPTIONS, Unsupported, translate } from "./translate.mjs";
import { workspacePaths } from "./paths.mjs";
import { refusalCode } from "./hints.mjs";

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

const options = (root, module, repository, assumes, effects) => ({
  root, module: module ?? "Probe", repository: repository ?? root,
  paths: workspacePaths(repository ?? root), requireTypes: true,
  assumes: assumes ?? [], effects: effects ?? [],
  // stubs: false — a probe lists refusals rather than keeping the contract
  // elaborating, so a refusal is never upgraded to a fatal.
  stubs: false });

const crashReason = error =>
  `translator crash: ${String(error?.message ?? error).split("\n")[0]}\n`
  + "How to fix: this is a translator bug, not your code — please report it; "
  + "the rest of the package still scans";

export function probe({ root, module, repository, assumes, effects, translate: run = translate }) {
  const files = ts.sys.readDirectory(root, [".ts"], undefined, undefined);
  const program = ts.createProgram(files, { ...OPTIONS, paths: workspacePaths(repository ?? root) });
  const list = targets(root, program);
  let result;
  try {
    result = run({ ...options(root, module, repository, assumes, effects), targets: list });
  } catch (error) {
    // A refusal raised outside any one function's translation is about the
    // package itself (a file it can't read, a program-wide problem): every
    // function is refused with that reason instead of the scan failing.
    if (error instanceof Unsupported) {
      result = { module: module ?? "Probe", failures: Object.fromEntries(list.map(t => [t, error.message])) };
    } else {
      // A crash (e.g. a TypeScript debug failure on one file's syntax) is not a
      // refusal: retry file by file so the broken file is reported as refused
      // with the `translator-crash` code and the rest of the scan still runs.
      const byFile = new Map();
      for (const target of list) {
        const file = target.split("::")[0];
        byFile.set(file, [...(byFile.get(file) ?? []), target]);
      }
      const failures = {};
      for (const group of byFile.values()) {
        try {
          const single = run({ ...options(root, module, repository, assumes, effects), targets: group });
          Object.assign(failures, single.failures);
          // A fatal the group produced on its own belongs to this file.
          if (single.fatal) for (const target of group) failures[target] ??= single.fatal;
        } catch (again) {
          if (again instanceof Unsupported) {
            for (const target of group) failures[target] = again.message;
          } else {
            for (const target of group) failures[target] = crashReason(again);
          }
        }
      }
      result = { module: module ?? "Probe", failures };
    }
  }
  const functions = list.map(function_ => ({
    function: function_,
    translated: !(function_ in result.failures),
    ...(result.failures[function_]
      ? { reason: result.failures[function_], code: refusalCode(result.failures[function_]) } : {}),
  }));
  const byCode = {};
  for (const f of functions) if (!f.translated) byCode[f.code] = (byCode[f.code] ?? 0) + 1;
  const translated = functions.filter(f => f.translated).length;
  return { module: result.module, functions,
    summary: { total: functions.length, translated, refused: functions.length - translated, by_code: byCode },
    ...(result.fatal ? { fatal: result.fatal } : {}) };
}

if (process.argv[1]?.endsWith("probe.mjs")) {
  const config = JSON.parse(readFileSync(process.argv[2], "utf8"));
  console.log(JSON.stringify(probe(config)));
}
