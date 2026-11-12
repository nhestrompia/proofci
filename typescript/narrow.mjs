// Narrowing `any` in an effect's signature.
//
// An outside call whose published signature says `any` (`(id: string): Promise<any>`) cannot be translated:
// the type of its answer is unknown. The policy may write the answer's type itself, in the entry's
// `narrowed` field:
//
//   - id: getLink
//     call: src/db.ts::getLink
//     signature: "(id: string): Promise<any>"            # exactly what the compiler reports for the call
//     narrowed: "(id: string): Promise<Link | null>"     # what the proof assumes the call answers
//     kind: read
//
// Nothing about the call is proved: the narrowing is a claim about code that is not read, and the report
// lists it as an assumption of every guarantee that reaches the call. Where the claim is false the proof
// says nothing about that run, exactly as for any other outside answer that breaks a hypothesis.
//
// What this module does is keep the claim honest in form:
//   * `signature` must still be what the compiler reports for the unchanged source, so a change to the
//     callee's type is seen;
//   * `narrowed` may differ from `signature` only where the written type of a parameter or of the return
//     contains `any`, and has the same parameters, optionality and rest;
//   * the program the translator reads sees the callee as `narrowed` says, so that every use of an answer
//     (a variable that holds it, a field read from it) has the narrowed type with no cast.
//
// The callee's source is rewritten in the compiler's view only (never on disk): its declaration becomes a
// body-less function of the narrowed signature. This works for a function of the project (`path/file.ts::fn`).
// A function of an installed package keeps its own types, and a package that is not installed is declared
// from the policy anyway, so there `narrowed` is simply the declaration.

import { readFileSync } from "node:fs";
import { join } from "node:path";
import ts from "typescript";

const plain = text => text.replace(/\s+/g, " ").trim();
const ANY = /\bany\b/;

// `(params): ret` as a function declaration, or nothing if it is not one.
function parseSignature(text) {
  const file = ts.createSourceFile("signature.ts", `declare function f${text};`, ts.ScriptTarget.Latest, true);
  const declaration = file.statements[0];
  if (file.parseDiagnostics?.length || !declaration || !ts.isFunctionDeclaration(declaration) || declaration.typeParameters?.length || !declaration.type) return undefined;
  return declaration;
}

// Why `narrowed` is not a legitimate narrowing of `signature`, or nothing.
export function narrowingProblem(signature, narrowed) {
  if (!ANY.test(signature)) return "`narrowed` is given, but the signature has no `any` to narrow";
  const from = parseSignature(signature), to = parseSignature(narrowed);
  if (!from) return "`signature` could not be read as a signature";
  if (!to) return "`narrowed` must be a signature with a written return type, for example `(id: string): Promise<Link | null>`";
  if (from.parameters.length !== to.parameters.length) return "`narrowed` must have the same parameters as `signature`";
  const same = (a, b, what) => (plain(a) === plain(b) || ANY.test(a) ? undefined : `\`narrowed\` changes ${what}, which is not \`any\``);
  for (const [i, parameter] of from.parameters.entries()) {
    const other = to.parameters[i];
    if (parameter.name.getText() !== other.name.getText() || Boolean(parameter.questionToken) !== Boolean(other.questionToken)
      || Boolean(parameter.dotDotDotToken) !== Boolean(other.dotDotDotToken) || Boolean(parameter.initializer) !== Boolean(other.initializer)) {
      return `\`narrowed\` changes the parameter \`${parameter.name.getText()}\` beyond its type`;
    }
    const problem = same(parameter.type?.getText() ?? "any", other.type?.getText() ?? "any", `the type of \`${parameter.name.getText()}\``);
    if (problem) return problem;
  }
  return same(from.type.getText(), to.type.getText(), "the return type");
}

// The compiler's view of the project files whose functions are narrowed: file name -> source text.
export function narrowedSources(root, effects) {
  const edits = new Map(); // path -> [{ start, end, text }]
  for (const entry of effects) {
    if (!entry.narrowed || !entry.call) continue;
    const [module, fn] = entry.call.split("::");
    if (!/\.[cm]?tsx?$/.test(module) || narrowingProblem(entry.signature, entry.narrowed)) continue;
    const path = join(root, module);
    let text;
    try { text = readFileSync(path, "utf8"); } catch { continue; }
    const file = ts.createSourceFile(path, text, ts.ScriptTarget.Latest, true);
    const body = " { throw new Error(\"outside\"); }";
    for (const statement of file.statements) {
      if (ts.isFunctionDeclaration(statement) && statement.name?.text === fn) {
        const words = (statement.modifiers ?? []).filter(m => m.kind !== ts.SyntaxKind.AsyncKeyword).map(m => m.getText());
        edits.set(path, [...edits.get(path) ?? [], { start: statement.getStart(file), end: statement.end, text: `${[...words, "function"].join(" ")} ${fn}${entry.narrowed}${body}` }]);
      } else if (ts.isVariableStatement(statement)) {
        for (const declaration of statement.declarationList.declarations) {
          if (!ts.isIdentifier(declaration.name) || declaration.name.text !== fn || !declaration.initializer) continue;
          const start = declaration.type ? declaration.name.end : declaration.initializer.getStart(file);
          edits.set(path, [...edits.get(path) ?? [], { start, end: declaration.end, text: `${declaration.type ? " = " : ""}function${entry.narrowed}${body}` }]);
        }
      }
    }
  }
  const sources = new Map();
  for (const [path, list] of edits) {
    let text = readFileSync(path, "utf8");
    for (const edit of list.sort((a, b) => b.start - a.start)) text = text.slice(0, edit.start) + edit.text + text.slice(edit.end);
    sources.set(path, text);
  }
  return sources;
}

// A compiler host that serves `sources` in place of the files on disk.
export function withSources(host, sources) {
  if (!sources.size) return host;
  const { getSourceFile, readFile } = host;
  host.getSourceFile = (name, languageVersion, ...rest) => (sources.has(name) ? ts.createSourceFile(name, sources.get(name), languageVersion, true) : getSourceFile.call(host, name, languageVersion, ...rest));
  host.readFile = name => (sources.has(name) ? sources.get(name) : readFile.call(host, name));
  return host;
}
