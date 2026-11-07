// Translates a checked subset of TypeScript into Lean, in the shape Aeneas uses
// for Rust: every function returns `Result T`, so the same proof tools apply.
//
// A construct that isn't understood is rejected, never approximated, and only
// what the target functions reach has to be in the subset. This program reads
// source files and type-checks them. It never runs them.
//
// Usage: node translate.mjs <config.json>
//   config: { root, module, targets: ["src/ledger.ts::transfer"], out }
// Writes <out>/<module>.lean and prints a JSON result on stdout.

import { existsSync, readFileSync, realpathSync, writeFileSync } from "node:fs";
import { createHash } from "node:crypto";
import { dirname, join, relative, sep } from "node:path";
import ts from "typescript";
import { protectedPaths } from "./paths.mjs";

export class Unsupported extends Error {}

// Every word Lean reads as syntax once Aeneas is imported, so that `name` can still
// be a field. `lean-tokens.json` is Lean's token table; regenerate it when Aeneas
// changes (see docs/development.md). Words listed below it aren't all tokens, but
// would change what the generated code means.
const LEAN_TOKENS = JSON.parse(readFileSync(new URL("./lean-tokens.json", import.meta.url), "utf8"));
const LEAN_KEYWORDS = new Set([...LEAN_TOKENS, "at", "by", "calc", "class", "deriving", "do", "else", "end", "export", "extends",
  "fun", "from", "have", "if", "import", "in", "infix", "instance", "let", "macro", "match", "mut", "namespace",
  "notation", "of", "open", "prefix", "private", "protected", "public", "section", "set_option", "show", "structure",
  "syntax", "then", "theorem", "this", "to", "try", "universe", "unless", "using", "variable", "where", "with",
  "abbrev", "axiom", "def", "example", "fix", "for", "forall", "inductive", "lemma", "mutual", "nomatch", "opaque",
  "return", "suffices", "termination_by", "decreasing_by", "Type", "Sort", "Prop", "true", "false", "none", "some"]);

// Translation reads `xs[i]` as possibly undefined. Most projects don't compile
// with that on, so their code is judged by what they do compile with, and a read
// the project assumes is present stops the model when it isn't.
const LENIENT = { noUncheckedIndexedAccess: false, exactOptionalPropertyTypes: false };

export const OPTIONS = {
  target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext,
  moduleResolution: ts.ModuleResolutionKind.Bundler, strict: true, noEmit: true,
  noUncheckedIndexedAccess: true, exactOptionalPropertyTypes: true, noImplicitReturns: true,
  noFallthroughCasesInSwitch: true, skipLibCheck: true, allowJs: false, types: [],
  allowImportingTsExtensions: true,
};


const COMPILER_SWITCH = /@ts-(ignore|expect-error|nocheck)/;
const SHADOW_EXTENSIONS = [".js", ".mjs", ".cjs", ".jsx"];
const ROUNDING = { floor: "floorDiv", ceil: "ceilDiv", trunc: "truncDiv" };
const ARITHMETIC = {
  [ts.SyntaxKind.PlusToken]: "add", [ts.SyntaxKind.MinusToken]: "sub", [ts.SyntaxKind.AsteriskToken]: "mul",
  [ts.SyntaxKind.SlashToken]: "div", [ts.SyntaxKind.PercentToken]: "rem",
};
const ORDER = {
  [ts.SyntaxKind.LessThanToken]: "<", [ts.SyntaxKind.LessThanEqualsToken]: "≤",
  [ts.SyntaxKind.GreaterThanToken]: ">", [ts.SyntaxKind.GreaterThanEqualsToken]: "≥",
};

const COMPOUND = {
  [ts.SyntaxKind.PlusEqualsToken]: ts.SyntaxKind.PlusToken, [ts.SyntaxKind.MinusEqualsToken]: ts.SyntaxKind.MinusToken,
  [ts.SyntaxKind.AsteriskEqualsToken]: ts.SyntaxKind.AsteriskToken, [ts.SyntaxKind.SlashEqualsToken]: ts.SyntaxKind.SlashToken,
  [ts.SyntaxKind.PercentEqualsToken]: ts.SyntaxKind.PercentToken,
};

const ONE = ts.factory.createNumericLiteral(1); // the step of `++` and `--`

const isUpdate = node => node.operator === ts.SyntaxKind.PlusPlusToken || node.operator === ts.SyntaxKind.MinusMinusToken;

const MUTATING = new Set(["push", "pop", "shift", "unshift", "reverse", "sort", "splice", "fill", "copyWithin", "set", "add", "delete", "clear"]);

// What `node` writes to, if it is a write. A method call writes to its receiver.
const writeTarget = node => {
  if (ts.isBinaryExpression(node) && ts.isAssignmentOperator(node.operatorToken.kind)) return node.left;
  if ((ts.isPrefixUnaryExpression(node) || ts.isPostfixUnaryExpression(node)) && isUpdate(node)) return node.operand;
  if (ts.isCallExpression(node) && ts.isPropertyAccessExpression(unwrap(node.expression))) {
    const callee = unwrap(node.expression);
    if (MUTATING.has(callee.name.text)) return callee.expression;
  }
  return undefined;
};

// The variable a write lands in: `x` for `x`, `x.y` and `x[i]`.
const rootOf = node => {
  node = unwrap(node);
  while (ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node) || ts.isNonNullExpression(node)) {
    node = unwrap(node.expression);
  }
  return node;
};

const name = text => {
  if (!/^[A-Za-z_][A-Za-z0-9_]*$/.test(text)) throw new Unsupported(`the name \`${text}\` has no Lean spelling yet`);
  return LEAN_KEYWORDS.has(text) ? `«${text}»` : text;
};

// A local with one of these names would change what the generated code means.
const RESERVED_LOCALS = new Set(["none", "some", "Js", "Result", "Aeneas", "Std", "Option", "Bool", "decide", "_root_"]);

const local = text => {
  if (RESERVED_LOCALS.has(text)) throw new Unsupported(`a variable can't be called \`${text}\` yet`);
  return name(text);
};

const unwrap = node => {
  while (ts.isParenthesizedExpression(node)) node = node.expression;
  return node;
};

export class Translator {
  constructor(root, targets, paths = {}, repository = root, assumes = []) {
    this.root = realpathSync(root);
    this.repository = realpathSync(repository);
    this.files = [...new Set(targets.map(t => join(this.root, t.split("::")[0])))];
    for (const file of this.files) {
      if (!existsSync(file)) throw new Unsupported(`${relative(this.root, file)} does not exist`);
    }
    const build = options => this.assumedProgram(options, assumes);
    this.program = build({ ...OPTIONS, paths });
    this.checker = this.program.getTypeChecker();
    this.lenient = build({ ...OPTIONS, ...LENIENT, paths });
    this.anonymous = new Map(); // key -> shape of an inline object type
    this.types = new Map();      // declaration, or instantiation key -> { lean, text }
    this.shaped = [];            // every type given a Lean shape, with where it was met
    this.typeOwners = new Map(); // Lean name -> the declaration that took it
    this.packages = new Map();   // package.json path -> { name, version }, for declared types
    this.functions = new Map();  // declaration -> { lean, text } (null while in progress)
    this.constants = new Map();
    this.fileChecks = new Map();
    this.order = [];
    this.assumes = new Map(assumes.map(a => [a.call, a.signature])); // `module::name` -> its listed signature
    this.assumed = new Map();   // `module::name` -> its Lean name
    this.assumedBy = new Map(); // declaration -> what it relies on, through its calls
    this.current = [];
  }

  fail(node, message) {
    const file = node.getSourceFile();
    const { line } = file.getLineAndCharacterOfPosition(node.getStart(file));
    return new Unsupported(`${relative(this.root, file.fileName)}:${line + 1}: ${message}`);
  }

  // ---------------------------------------------------------------- files

  // What the runtime would load must be what is translated, and nothing in
  // the file may change that behind the translation's back.
  checkFile(file) {
    if (!this.fileChecks.has(file)) {
      let problem = null;
      try {
        this.inspectFile(file);
      } catch (error) {
        if (!(error instanceof Unsupported)) throw error;
        problem = error;
      }
      this.fileChecks.set(file, problem);
    }
    // A problem with a file applies to every function in it, not only the first.
    const problem = this.fileChecks.get(file);
    if (problem) throw problem;
  }

  inspectFile(file) {
    const path = realpathSync(file.fileName);
    if (file.isDeclarationFile || !(path === this.repository || path.startsWith(this.repository + sep))) {
      throw new Unsupported(`${file.fileName} is outside the translated package`);
    }
    const stem = path.replace(/\.ts$/, "");
    for (const extension of SHADOW_EXTENSIONS) {
      if (existsSync(stem + extension)) {
        throw new Unsupported(`${relative(this.root, stem + extension)} sits beside the TypeScript source, `
          + "so the program may load it instead");
      }
    }
    if (/@ts-nocheck/.test(file.text)) {
      throw new Unsupported(`${relative(this.root, path)} turns off compiler errors with \`@ts-nocheck\``);
    }
    for (const statement of file.statements) this.checkTopLevel(statement);
  }

  // Only what a function reaches has to be in the subset, so an unrelated import
  // or error elsewhere in the file doesn't matter. This judges one declaration.
  checkDeclaration(declaration) {
    // A comment before `const` belongs to the whole statement.
    const node = ts.isVariableDeclaration(declaration) && ts.isVariableStatement(declaration.parent.parent)
      ? declaration.parent.parent : declaration;
    const file = node.getSourceFile();
    const text = file.text.slice(node.getFullStart(), node.end);
    if (COMPILER_SWITCH.test(text)) throw this.fail(node, "this code turns off compiler errors with a `@ts-` comment");
    const relaxed = this.lenient.getSourceFile(file.fileName);
    const problems = [...this.lenient.getSyntacticDiagnostics(relaxed), ...this.lenient.getSemanticDiagnostics(relaxed)]
      .filter(d => d.start !== undefined && d.start >= node.getFullStart() && d.start < node.end);
    if (problems.length) {
      const first = problems[0];
      const line = file.getLineAndCharacterOfPosition(first.start).line + 1;
      throw new Unsupported(`${relative(this.root, realpathSync(file.fileName))}:${line}: TypeScript error: `
        + ts.flattenDiagnosticMessageText(first.messageText, " "));
    }
  }

  // Module code runs on import. Translated functions assume the built-ins are
  // the real ones, so a file they come from must not replace or extend one.
  checkTopLevel(statement) {
    if (ts.isImportDeclaration(statement) && !statement.importClause) {
      throw this.fail(statement, "an import that exists only for its side effects");
    }
    const walk = node => {
      const target = ts.isBinaryExpression(node) && ts.isAssignmentOperator(node.operatorToken.kind) ? node.left : undefined;
      if (target && this.touchesBuiltin(target)) throw this.fail(node, "this code replaces a built-in, which changes what translated code means");
      if (ts.isCallExpression(node)) {
        const callee = node.expression.getText();
        const first = node.arguments[0];
        if (["Object.defineProperty", "Object.defineProperties", "Object.assign", "Object.setPrototypeOf", "Reflect.set", "Reflect.defineProperty"].includes(callee)
          && first && this.touchesBuiltin(first)) {
          throw this.fail(node, "this code replaces a built-in, which changes what translated code means");
        }
      }
      ts.forEachChild(node, walk);
    };
    walk(statement);
  }

  // `Math.floor`, `Array.prototype.map`, `globalThis.Math` and the like.
  touchesBuiltin(node) {
    let current = unwrap(node);
    if (/\.prototype\b|\bglobalThis\b/.test(current.getText())) return true;
    while (ts.isPropertyAccessExpression(current) || ts.isElementAccessExpression(current)) current = unwrap(current.expression);
    if (!ts.isIdentifier(current)) return false;
    const declaration = this.checker.getSymbolAtLocation(current)?.valueDeclaration;
    return Boolean(declaration) && this.program.isSourceFileDefaultLibrary(declaration.getSourceFile());
  }

  namespace(file) {
    const relativePath = relative(this.root, realpathSync(file.fileName)).replace(/\.ts$/, "");
    return relativePath.split(sep).map(part => part.replace(/[^A-Za-z0-9_]/g, "_").replace(/^(\d)/, "_$1")).map(name).join(".");
  }

  leanName(node, text) {
    return `${this.namespace(node.getSourceFile())}.${name(text)}`;
  }

  // ---------------------------------------------------------------- types

  // Returns a Lean type, as text.
  type(type, node) {
    const { TypeFlags } = ts;
    if (type.flags & TypeFlags.NumberLike) return "Js.Num";
    if (type.flags & TypeFlags.BooleanLike) return "Bool";
    if (type.flags & TypeFlags.BigIntLike) return "Int";
    if (type.flags & TypeFlags.Void) return "Unit";
    if (type.flags & TypeFlags.StringLike) return "Js.Str";
    if (this.checker.isArrayType(type)) return `(List ${this.type(this.checker.getTypeArguments(type)[0], node)})`;
    const collection = this.collection(type);
    if (collection) {
      const [key, value] = collection.args.map(arg => this.type(arg, node));
      const keyed = ["Js.Num", "Js.Str", "Bool", "Int"].includes(key) || this.shape(collection.args[0])?.kind === "enum";
      if (!keyed) throw this.fail(node, "only numbers, strings, booleans and string-literal unions can be keys for now");
      return collection.kind === "Map" ? `(Js.Dict ${key} ${value})` : `(List ${key})`;
    }
    if (type.isUnion() && type.types.every(t => t.flags & TypeFlags.NumberLike)) return "Js.Num";
    if (type.isUnion() && type.types.every(t => t.flags & TypeFlags.BigIntLike)) return "Int";
    if (this.bound(type)) return this.type(this.bound(type), node);
    if (type.flags & TypeFlags.TypeParameter) return name(type.symbol.name);
    if (type.isUnion()) {
      const parts = type.types.filter(t => !(t.flags & (TypeFlags.Null | TypeFlags.Undefined)));
      if (parts.length < type.types.length) {
        const rest = parts.length === 1 ? parts[0] : this.checker.getNonNullableType(type);
        return `(Option ${this.type(rest, node)})`;
      }
      if (!type.aliasSymbol && parts.every(t => t.flags & TypeFlags.StringLike)) return "Js.Str";
    }
    const symbol = type.aliasSymbol ?? type.symbol;
    const declaration = symbol?.declarations?.[0];
    const library = declaration && this.program.isSourceFileDefaultLibrary(declaration.getSourceFile());
    if (declaration && !library && (ts.isInterfaceDeclaration(declaration) || ts.isTypeAliasDeclaration(declaration))) {
      return `_root_.${this.declareType(declaration, type, node)}`;
    }
    if (type.flags & TypeFlags.Object && (symbol?.name === "__type" || symbol?.name === "__object")) {
      return `_root_.${this.declareAnonymous(type, node).lean}`;
    }
    throw this.fail(node, `the type \`${this.checker.typeToString(type)}\` is not supported yet`);
  }

  // An inline object type becomes a structure named after its shape, so that the
  // same shape written twice is one Lean type.
  declareAnonymous(type, node) {
    const fields = this.fields(type, node).map(f => ({ ...f, lean: this.fieldType(f) }));
    if (!fields.length) throw this.fail(node, "empty records are not supported");
    const key = fields.map(f => `${f.name}:${f.lean}`).sort().join(",");
    if (!this.anonymous.has(key)) {
      const hash = createHash("sha256").update(key).digest("hex").slice(0, 10);
      const lean = `Proofci.Inline.R${hash}`;
      const lines = fields.map(f => `  ${name(f.name)} : ${f.lean}`);
      const text = [`structure ${lean} where`, ...lines, "deriving DecidableEq, Repr"].join("\n");
      this.anonymous.set(key, { lean, kind: "record", fields: fields.map(f => f.name) });
      this.order.push(text);
      this.shaped.push({ type, node });
    }
    return this.anonymous.get(key);
  }

  fieldType(field) {
    const lean = this.type(field.type, field.node);
    return field.node.questionToken && !lean.startsWith("(Option ") ? `(Option ${lean})` : lean;
  }

  // The package a declaration file ships in, by the nearest manifest with a name.
  packageOf(file) {
    const path = realpathSync(file.fileName);
    if (!(path === this.repository || path.startsWith(this.repository + sep))) {
      throw new Unsupported(`${file.fileName} is outside the translated package`);
    }
    for (let dir = dirname(path); dir.startsWith(this.repository); dir = dirname(dir)) {
      const manifest = join(dir, "package.json");
      if (!existsSync(manifest)) continue;
      if (!this.packages.has(manifest)) {
        const { name: package_, version } = JSON.parse(readFileSync(manifest, "utf8"));
        this.packages.set(manifest, package_ ? { name: package_, version, dir } : null);
      }
      if (this.packages.get(manifest)) return this.packages.get(manifest);
    }
    return undefined;
  }

  // A type in a declaration file has no code of its own, so what a file check
  // looks for can't be there. Its fields are a claim about values, as they are
  // for any declared type. The name leaves out the version and the install
  // layout, so a guarantee about the type survives a package update or a
  // different package manager, as long as the type keeps its shape.
  leanTypeName(declaration) {
    const file = declaration.getSourceFile();
    const found = file.isDeclarationFile ? this.packageOf(file) : undefined;
    if (!found) return this.leanName(declaration, declaration.name.text);
    const inside = relative(found.dir, realpathSync(file.fileName)).replace(/\.d\.[cm]?ts$/, "");
    const parts = [...found.name.split("/"), ...inside.split(sep)]
      .map(part => part.replace(/[^A-Za-z0-9_]/g, "_").replace(/^(\d)/, "_$1")).map(name);
    return `Proofci.Package.${parts.join(".")}.${name(declaration.name.text)}`;
  }

  // `T extends { to: string }` is read at its bound, so its fields can be read. The bridge
  // still checks the body, and a caller passing a wider type simply won't elaborate.
  bound(type) {
    if (!(type.flags & ts.TypeFlags.TypeParameter)) return undefined;
    const bound = this.checker.getBaseConstraintOfType(type);
    if (!bound || bound === type || !(bound.flags & ts.TypeFlags.Object) || this.checker.isArrayType(bound)) return undefined;
    if (bound.getCallSignatures().length || !this.checker.getPropertiesOfType(bound).length) return undefined;
    return bound;
  }

  generics(fn) {
    return (fn.typeParameters ?? [])
      .filter(t => !this.bound(this.checker.getTypeAtLocation(t)))
      .map(t => `{${name(t.name.text)} : Type} [DecidableEq ${name(t.name.text)}]`);
  }

  // Each use of a generic type is its own Lean type, so `Page<string>` and
  // `Page<number>` are separate structures. Nothing else needs an argument.
  instantiation(declaration, type, node) {
    if (!declaration.typeParameters?.length) return { key: declaration, suffix: "" };
    const argumentTypes = type.aliasTypeArguments ?? (type.objectFlags & ts.ObjectFlags.Reference ? this.checker.getTypeArguments(type) : []);
    const given = argumentTypes.slice(0, declaration.typeParameters.length);
    if (given.length !== declaration.typeParameters.length) throw this.fail(node, "this use of a generic type has no arguments to read");
    if (given.some(arg => arg.flags & ts.TypeFlags.TypeParameter)) throw this.fail(node, "a generic type over a type parameter is not supported yet");
    const text = given.map(arg => this.type(arg, node)).join(",");
    const hash = createHash("sha256").update(text).digest("hex").slice(0, 10);
    return { key: `${this.leanTypeName(declaration)}<${text}>`, suffix: `_${hash}` };
  }

  declareType(declaration, type, node = declaration) {
    const { key, suffix } = this.instantiation(declaration, type, node);
    if (this.types.has(key)) {
      const known = this.types.get(key);
      if (!known) throw this.fail(declaration, "recursive types are not supported yet");
      return known.lean;
    }
    const file = declaration.getSourceFile();
    if (file.isDeclarationFile) this.packageOf(file);
    else {
      this.checkFile(file);
      this.checkDeclaration(declaration);
    }
    const lean = `${this.leanTypeName(declaration)}${suffix}`;
    // Two installed versions of a package can both declare a type at this name.
    if ((this.typeOwners.get(lean) ?? declaration) !== declaration) {
      throw this.fail(declaration, `two declarations of \`${declaration.name.text}\` would share a Lean name`);
    }
    this.typeOwners.set(lean, declaration);
    this.types.set(key, null);
    let shape;
    if (type.isUnion()) shape = this.declareUnion(declaration, type, lean);
    else shape = this.declareRecord(declaration, type, lean);
    this.types.set(key, { lean, ...shape });
    this.shaped.push({ type, node });
    this.order.push(shape.text);
    return lean;
  }

  fields(type, declaration) {
    if (this.checker.getIndexInfosOfType(type).length) throw this.fail(declaration, "index signatures are not supported yet");
    return this.checker.getPropertiesOfType(type).map(property => {
      const node = property.valueDeclaration;
      if (!node || !(ts.isPropertySignature(node) || ts.isPropertyAssignment(node) || ts.isShorthandPropertyAssignment(node))) {
        throw this.fail(declaration, `\`${property.name}\` is not a plain field`);
      }
      return { name: property.name, type: this.checker.getTypeOfSymbolAtLocation(property, node), node };
    });
  }

  declareRecord(declaration, type, lean) {
    if (!(type.flags & ts.TypeFlags.Object)) throw this.fail(declaration, "this type is not supported yet");
    const fields = this.fields(type, declaration);
    if (!fields.length) throw this.fail(declaration, "empty records are not supported");
    const lines = fields.map(f => `  ${name(f.name)} : ${this.fieldType(f)}`);
    return { kind: "record", fields: fields.map(f => f.name),
      text: [`structure ${lean} where`, ...lines, "deriving DecidableEq, Repr"].join("\n") };
  }

  // A union of string literals is an enumeration. A union of records tagged by
  // a shared `kind` field is an inductive type with one constructor each.
  declareUnion(declaration, type, lean) {
    if (type.types.every(t => t.isStringLiteral())) {
      const tags = type.types.map(t => t.value);
      return { kind: "enum", tags,
        text: [`inductive ${lean} where`, ...tags.map(t => `  | ${name(t)}`), "deriving DecidableEq, Repr", "",
          `def ${lean}.toJsStr : ${lean} → Js.Str`, ...tags.map(t => `  | .${name(t)} => ${leanString(t)}`)].join("\n") };
    }
    const variants = type.types.map(member => {
      if (!(member.flags & ts.TypeFlags.Object)) throw this.fail(declaration, "unions must be tagged records");
      const fields = this.fields(member, declaration);
      const tag = fields.find(f => f.name === "kind");
      if (!tag || !tag.type.isStringLiteral()) throw this.fail(declaration, "union members need a string `kind` field");
      return { tag: tag.type.value, fields: fields.filter(f => f.name !== "kind") };
    });
    const lines = variants.map(v => `  | ${name(v.tag)} ${v.fields.map(f => `(${name(f.name)} : ${this.type(f.type, f.node)})`).join(" ")}`);
    return { kind: "tagged", variants: variants.map(v => ({ tag: v.tag, fields: v.fields.map(f => f.name) })),
      text: [`inductive ${lean} where`, ...lines, "deriving DecidableEq, Repr"].join("\n") };
  }

  // `Map<K, V>` or `Set<K>`, from the standard library rather than a lookalike.
  collection(type) {
    const name_ = type.symbol?.name;
    if (name_ !== "Map" && name_ !== "Set" && name_ !== "ReadonlyMap" && name_ !== "ReadonlySet") return undefined;
    const declaration = type.symbol.declarations?.[0];
    if (!declaration || !this.program.isSourceFileDefaultLibrary(declaration.getSourceFile())) return undefined;
    return { kind: name_.replace("Readonly", ""), args: this.checker.getTypeArguments(type) };
  }

  // A description of a type, for generating and reading values of it.
  describe(type, node) {
    const lean = this.type(type, node);
    if (lean === "Js.Num") return { kind: "number" };
    if (lean === "Bool") return { kind: "boolean" };
    if (lean === "Int") return { kind: "bigint" };
    if (lean === "Unit") return { kind: "void" };
    if (lean === "Js.Str") return { kind: "string" };
    if (this.checker.isArrayType(type)) return { kind: "array", item: this.describe(this.checker.getTypeArguments(type)[0], node) };
    if (this.bound(type)) return this.describe(this.bound(type), node);
    if (type.flags & ts.TypeFlags.TypeParameter) return { kind: "generic", name: type.symbol.name };
    if (type.isUnion() && this.nullish(type)) {
      const nothing = type.types.some(t => t.flags & ts.TypeFlags.Null) ? "null" : "undefined";
      return { kind: "optional", nothing, both: type.types.filter(t => t.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined)).length > 1, inner: this.describe(this.checker.getNonNullableType(type), node) };
    }
    const collection = this.collection(type);
    if (collection?.kind === "Map") return { kind: "map", key: this.describe(collection.args[0], node), value: this.describe(collection.args[1], node) };
    if (collection) return { kind: "set", item: this.describe(collection.args[0], node) };
    const shape = this.shape(type);
    const fields = owner => this.fields(owner, node).map(f => {
      const described = this.describe(f.type, f.node);
      const optional = f.node.questionToken && described.kind !== "optional";
      return { name: f.name, lean: name(f.name), type: optional ? { kind: "optional", nothing: "undefined", inner: described } : described };
    });
    if (shape.kind === "enum") return { kind: "enum", lean: shape.lean, tags: shape.tags.map(t => ({ tag: t, lean: name(t) })) };
    if (shape.kind === "record") return { kind: "record", lean: shape.lean, fields: fields(type) };
    return { kind: "tagged", lean: shape.lean, variants: type.types.map(member => {
      const all = fields(member);
      const tag = all.find(f => f.name === "kind");
      const literal = this.fields(member, node).find(f => f.name === "kind").type.value;
      return { tag: literal, lean: name(literal), fields: all.filter(f => f !== tag) };
    }) };
  }

  nullish(type) {
    return type.types.some(t => t.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined));
  }

  signature(declaration) {
    const fn = this.bodyOf(declaration);
    const signature = this.checker.getSignatureFromDeclaration(fn);
    return {
      file: relative(this.root, realpathSync(declaration.getSourceFile().fileName)),
      exported: Boolean(ts.getCombinedModifierFlags(declaration) & ts.ModifierFlags.Export),
      name: declaration.name.text,
      lean: this.functions.get(declaration).lean,
      params: fn.parameters.map(p => {
        const described = this.describe(this.checker.getTypeAtLocation(p), p);
        return p.initializer && described.kind !== "optional" ? { kind: "optional", nothing: "undefined", inner: described } : described;
      }),
      result: this.describe(this.checker.getReturnTypeOfSignature(signature), fn),
    };
  }

  shape(type) {
    const symbol = type.aliasSymbol ?? type.symbol;
    if (symbol?.name === "__type" || symbol?.name === "__object") return this.declareAnonymous(type, symbol.declarations?.[0]);
    const declaration = symbol?.declarations?.[0];
    if (!declaration) return undefined;
    return this.types.get(declaration.typeParameters?.length ? this.instantiation(declaration, type, declaration).key : declaration);
  }

  // ------------------------------------------------------------ constants

  literal(node) {
    node = unwrap(node);
    if (ts.isNumericLiteral(node)) return Number(node.text);
    if (ts.isBigIntLiteral(node)) return undefined;
    if (ts.isPrefixUnaryExpression(node) && node.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(unwrap(node.operand))) {
      return -Number(unwrap(node.operand).text);
    }
    return undefined;
  }

  number(value, node) {
    if (!Number.isSafeInteger(value)) throw this.fail(node, `the number ${value} is not a safe integer`);
    return `(Js.Num.mk (${value}) (of_decide_eq_true rfl) (of_decide_eq_true rfl))`;
  }

  // ------------------------------------------------------------ functions

  // Only module-level functions: a local one could capture local variables.
  resolve(node) {
    if (!node) return undefined;
    if (ts.isFunctionDeclaration(node) && ts.isSourceFile(node.parent)) return node;
    if (ts.isVariableDeclaration(node) && ts.isSourceFile(node.parent.parent.parent)) return node;
    return undefined;
  }

  // The action doesn't install dependencies, so a listed call's module may be
  // missing. Its declaration then comes from the policy, which a pull request
  // can't change. An installed module keeps its own types, and they must match.
  assumedProgram(options, assumes) {
    const missing = new Map();
    for (const { call, signature } of assumes) {
      const [module, fn] = call.split("::");
      if (ts.resolveModuleName(module, this.files[0], options, ts.sys).resolvedModule) continue;
      missing.set(module, [...missing.get(module) ?? [], `  export function ${fn}${signature};`]);
    }
    if (!missing.size) return ts.createProgram(this.files, options);
    const path = join(this.root, "__proofci_assumed__.d.ts");
    const text = [...missing].map(([module, lines]) => `declare module ${JSON.stringify(module)} {\n${lines.join("\n")}\n}`).join("\n");
    const host = ts.createCompilerHost(options);
    const { getSourceFile, fileExists, readFile } = host;
    host.getSourceFile = (name, ...rest) => (name === path ? ts.createSourceFile(name, text, ts.ScriptTarget.Latest) : getSourceFile.call(host, name, ...rest));
    host.fileExists = name => name === path || fileExists.call(host, name);
    host.readFile = name => (name === path ? text : readFile.call(host, name));
    return ts.createProgram([...this.files, path], options, host);
  }

  // What a function leaves to inference, as the types it should write. A written
  // type is the contract a reviewer sees, and inference would change it silently.
  // Callbacks written in place take their types from the call, so aren't checked.
  untyped(declaration) {
    const fn = this.bodyOf(declaration);
    if (!fn || declaration.type) return [];
    const missing = fn.parameters.filter(p => !p.type)
      .map(p => `\`${p.name.getText()}: ${this.checker.typeToString(this.checker.getTypeAtLocation(p))}\``);
    if (fn.type) return missing;
    const signature = this.checker.getSignatureFromDeclaration(fn);
    return [...missing, `a return type of \`${this.checker.typeToString(this.checker.getReturnTypeOfSignature(signature))}\``];
  }

  bodyOf(declaration) {
    if (ts.isFunctionDeclaration(declaration)) return declaration;
    const init = declaration.initializer && unwrap(declaration.initializer);
    if (init && (ts.isArrowFunction(init) || ts.isFunctionExpression(init))) return init;
    return undefined;
  }

  // Declares a function and everything it reaches, callees first.
  declareFunction(declaration) {
    const known = this.functions.get(declaration);
    if (known?.pending) {
      if (this.current.at(-1) !== declaration) throw this.fail(declaration, "mutual recursion is not supported yet");
      known.recursive = true;
      return known.lean;
    }
    if (known) return known.lean;
    this.checkFile(declaration.getSourceFile());
    this.checkDeclaration(declaration);
    const fn = this.bodyOf(declaration);
    if (!fn || !fn.body) throw this.fail(declaration, "this function has no body to translate");
    const missing = this.requireTypes ? this.untyped(declaration) : [];
    if (missing.length) throw this.fail(declaration, `add ${missing.join(" and ")}: functions a guarantee reaches must write out their types`);
    if (fn.asteriskToken) throw this.fail(fn, "generators are not supported");
    if (fn.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) throw this.fail(fn, "`async` is not supported yet");
    const lean = this.leanName(declaration, declaration.name.text);
    const entry = { lean, pending: true, recursive: false };
    this.functions.set(declaration, entry);
    this.current.push(declaration);
    const signature = this.checker.getSignatureFromDeclaration(fn);
    const returns = this.checker.getReturnTypeOfSignature(signature);
    const scope = new Scope(this, fn);
    const prologue = [];
    const env = new Map();
    const params = fn.parameters.map((p, index) => scope.parameter(p, index, prologue, env));
    const generics = this.generics(fn);
    const result = this.type(returns, fn);
    const flow = scope.functionFlow(returns, result);
    const statements = ts.isBlock(fn.body) ? [...fn.body.statements] : [ts.factory.createReturnStatement(fn.body)];
    const body = [...prologue, ...(ts.isBlock(fn.body) ? scope.block(statements, flow, env) : scope.returning(fn.body, flow, env))];
    const lines = [`def ${lean} ${[...generics, ...params].join(" ")} : Result ${result} := do`, ...body.map(l => `  ${l}`)];
    if (entry.recursive) lines.push("partial_fixpoint");
    this.current.pop();
    entry.pending = false;
    this.order.push(lines.join("\n"));
    return lean;
  }

  // An outside call the policy lists. Opaque, so a proof holds for any function of
  // this type, and it can only say more through a hypothesis in the contract.
  declareAssumed(key, signature, node) {
    const known = this.assumed.get(key);
    if (known) return known;
    const [module, fn] = key.split("::");
    const parts = signature.getParameters().map(p => this.type(this.checker.getTypeOfSymbolAtLocation(p, node), node));
    const result = this.type(signature.getReturnType(), node);
    if (result === "Unit") throw this.fail(node, `\`${key}\` returns nothing, so it can only be called for its effects`);
    const lean = `Proofci.Assumed.${module.replace(/[^A-Za-z0-9]+/g, "_")}.${name(fn)}`;
    const body = `${parts.map(() => "fun _ => ").join("")}Result.fail .undef`;
    this.order.push(`opaque ${lean} : ${[...parts, `Result ${result}`].join(" → ")} := ${body}`);
    this.assumed.set(key, lean);
    return lean;
  }

  // Records what the function being translated relies on.
  noteAssumed(keys) {
    const owner = this.current.at(-1);
    if (!owner) return;
    if (!this.assumedBy.has(owner)) this.assumedBy.set(owner, new Set());
    for (const key of keys) this.assumedBy.get(owner).add(key);
  }

  // A failed target stays as a bare declaration, so that the contract still
  // elaborates and the other targets are judged. Its theorems are never run.
  stub(declaration) {
    const fn = this.bodyOf(declaration);
    const signature = this.checker.getSignatureFromDeclaration(fn);
    const scope = new Stub(this, fn);
    const generics = this.generics(fn);
    const params = [...generics, ...fn.parameters.map((p, index) => scope.parameter(p, index, [], new Map()))];
    const result = this.type(this.checker.getReturnTypeOfSignature(signature), fn);
    const lean = this.leanName(declaration, declaration.name.text);
    this.order.push(`axiom ${lean} ${params.join(" ")} : Result ${result}`);
    return lean;
  }

  declareConstant(declaration) {
    if (this.constants.has(declaration)) return this.constants.get(declaration);
    this.checkFile(declaration.getSourceFile());
    this.checkDeclaration(declaration);
    if (!(declaration.parent.flags & ts.NodeFlags.Const)) throw this.fail(declaration, "reading a module-level `let` or `var`");
    const lean = this.leanName(declaration, declaration.name.text);
    const value = this.literal(declaration.initializer);
    if (value !== undefined) {
      this.order.push(`def ${lean} : Js.Num := ${this.number(value, declaration)}`);
      this.constants.set(declaration, { lean, pure: true });
      return this.constants.get(declaration);
    }
    // Anything else is computed once on import, which a `Result` constant models.
    const scope = new Scope(this, declaration);
    const type = this.checker.getTypeAtLocation(declaration.name);
    const leanType = this.type(type, declaration);
    const lines = [];
    const result = scope.convert(declaration.initializer, type, new Map(), lines);
    this.order.push([`def ${lean} : Result ${leanType} := do`, ...[...lines, `Result.ok ${result}`].map(l => `  ${l}`)].join("\n"));
    this.constants.set(declaration, { lean, pure: false });
    return this.constants.get(declaration);
  }
}

// Only the signature of a failed target: its body may be what failed.
class Stub {
  constructor(translator, fn) { this.t = translator; this.checker = translator.checker; this.fn = fn; }

  parameter(p, index) {
    const type = this.checker.getTypeAtLocation(p);
    const lean = this.t.type(type, p);
    if (p.initializer) return `(${ts.isIdentifier(p.name) ? `${p.name.text}_arg` : `arg${index}`} : (Option ${lean}))`;
    return `(${ts.isIdentifier(p.name) ? local(p.name.text) : `arg${index}`} : ${lean})`;
  }
}

// Translates one function body. `env` maps a variable's symbol to how it reads
// in the current branch, which is how narrowing reaches the Lean output.
export class Scope {
  constructor(translator, fn) {
    this.t = translator;
    this.checker = translator.checker;
    this.fn = fn;
    this.counter = 0;
    this.names = new Set();
    this.taken = new Set(); // Lean names used so far in this function
    const walk = (node, nested) => {
      if (ts.isIdentifier(node)) this.names.add(node.text);
      const write = writeTarget(node);
      if (write && !this.isBuiltinReceiver(node, write)) this.noteWrite(write, nested, ts.isCallExpression(node));
      ts.forEachChild(node, child => walk(child, nested || (ts.isFunctionLike(node) && node !== fn && !this.isForEachBody(node))));
    };
    this.owned = new Set();
    walk(fn, false);
    this.checkOwnership();
  }

  // `xs.forEach(x => { ... })` as a statement is a `for...of` loop in other words.
  isForEachBody(node) {
    if (!(ts.isArrowFunction(node) || ts.isFunctionExpression(node))) return false;
    const call = node.parent;
    return ts.isCallExpression(call) && ts.isExpressionStatement(call.parent) && call.arguments[0] === node
      && ts.isPropertyAccessExpression(unwrap(call.expression)) && unwrap(call.expression).name.text === "forEach"
      && node.parameters.length === 1 && this.isArray(unwrap(call.expression).expression);
  }

  // A method that merely shares a name with a mutating one, such as a call to
  // a user's own `set`, is judged as a call, not as a write.
  isBuiltinReceiver(node, write) {
    if (!ts.isCallExpression(node)) return false;
    return !this.isArray(write) && !this.isCollection(write);
  }

  isArray(node) {
    return this.checker.isArrayType(this.typeOf(node));
  }

  isString(node) { return (this.typeOf(node).flags & ts.TypeFlags.StringLike) !== 0; }

  isCollection(node) { return Boolean(this.t.collection(this.typeOf(node))); }

  // Writing through a name is only safe if no other name can see the value, so
  // that a value in Lean behaves like the object in JavaScript. A changed object
  // must start as a new value, and may only be read, returned or copied.
  checkOwnership() {
    for (const symbol of this.owned) {
      const declaration = symbol.valueDeclaration;
      if (!ts.isVariableDeclaration(declaration) || !declaration.initializer) {
        throw this.t.fail(declaration, `\`${symbol.name}\` is changed in place, but it may be shared with the caller`);
      }
      if (ts.isForOfStatement(declaration.parent.parent)) {
        throw this.t.fail(declaration, `\`${symbol.name}\` is an element of an array that is changed in place`);
      }
      this.requireFresh(declaration.initializer, symbol);
    }
    const walk = node => {
      if (ts.isIdentifier(node)) {
        const symbol = this.symbol(node);
        if (this.owned.has(symbol) && symbol.valueDeclaration !== node.parent) this.checkOwnedUse(node, symbol);
      }
      if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.EqualsToken && ts.isIdentifier(unwrap(node.left))) {
        const symbol = this.symbol(unwrap(node.left));
        if (this.owned.has(symbol)) this.requireFresh(node.right, symbol);
      }
      const looped = ts.isForOfStatement(node) ? [node.expression, node.statement]
        : this.isForEachBody(node) ? [unwrap(node.parent.expression).expression, node.body] : null;
      if (looped) {
        const iterated = rootOf(looped[0]);
        if (ts.isIdentifier(iterated) && this.owned.has(this.symbol(iterated)) && this.assignedIn([looped[1]]).includes(this.symbol(iterated))) {
          throw this.t.fail(node, "changing an array while looping over it is not supported");
        }
      }
      ts.forEachChild(node, walk);
    };
    walk(this.fn);
  }

  requireFresh(node, symbol) {
    node = unwrap(node);
    const fresh = ts.isArrayLiteralExpression(node) || ts.isObjectLiteralExpression(node)
      || (ts.isNewExpression(node) && this.isCollection(node))
      || (ts.isCallExpression(node) && ts.isPropertyAccessExpression(unwrap(node.expression))
        && ["slice", "map", "filter", "concat"].includes(unwrap(node.expression).name.text) && this.isArray(unwrap(node.expression).expression));
    if (!fresh) throw this.t.fail(node, `\`${symbol.name}\` is changed in place, so it must start as a new array or object`);
  }

  checkOwnedUse(node, symbol) {
    const parent = node.parent;
    const read = (ts.isPropertyAccessExpression(parent) && parent.expression === node)
      || (ts.isElementAccessExpression(parent) && parent.expression === node)
      || (ts.isElementAccessExpression(parent) && parent.argumentExpression === node)
      || (ts.isForOfStatement(parent) && parent.expression === node)
      || ts.isReturnStatement(parent) || ts.isSpreadElement(parent)
      || (ts.isBinaryExpression(parent) && parent.left === node && ts.isAssignmentOperator(parent.operatorToken.kind));
    if (read) return;
    // Primitive values aren't shared, so reading them is always fine.
    if (!(this.typeOf(node).flags & ts.TypeFlags.Object)) return;
    throw this.t.fail(node, `\`${symbol.name}\` is changed in place, so it can't be passed around or stored here`);
  }

  noteWrite(target, nested, method) {
    target = unwrap(target);
    const root = rootOf(target);
    if (nested) throw this.t.fail(target, "assignment inside a nested function is not supported yet");
    if (!ts.isIdentifier(root)) throw this.t.fail(target, "this write is not supported yet");
    const symbol = this.symbol(root);
    const declaration = symbol?.valueDeclaration;
    if (!declaration || this.isModuleLevel(declaration)) throw this.t.fail(target, "assignment to module-level state");
    if (method && !ts.isIdentifier(target)) throw this.t.fail(target, "changing a nested array is not supported yet");
    if (root !== target || method) {
      if (ts.isPropertyAccessExpression(target) && !ts.isIdentifier(unwrap(target.expression))) throw this.t.fail(target, "writing to a nested field is not supported yet");
      if (ts.isElementAccessExpression(target) && !ts.isIdentifier(unwrap(target.expression))) throw this.t.fail(target, "writing to a nested element is not supported yet");
      this.owned.add(symbol);
    }
  }

  // A parameter, as Lean sees it. A default or a destructuring pattern is applied
  // at the top of the function, in `prologue`.
  parameter(p, index, prologue, env) {
    if (p.dotDotDotToken) throw this.t.fail(p, "rest parameters are not supported yet");
    const type = this.checker.getTypeAtLocation(p);
    if (ts.isIdentifier(p.name)) {
      const symbol = this.symbol(p.name);
      local(p.name.text);
      if (!p.initializer) {
        this.taken.add(this.rebind(symbol, env));
        return `(${this.current(symbol, env)} : ${this.t.type(type, p)})`;
      }
      const argument = `${p.name.text}_arg`;
      this.taken.add(argument);
      const inner = [];
      const fallback = this.convert(p.initializer, type, env, inner);
      prologue.push(`let ${this.rebind(symbol, env)} ← match ${argument} with`, "  | some value => Result.ok value",
        "  | none => do", ...inner.map(l => `    ${l}`), `    Result.ok ${fallback}`);
      return `(${argument} : (Option ${this.t.type(type, p)}))`;
    }
    if (!ts.isObjectBindingPattern(p.name) || p.initializer) throw this.t.fail(p, "this parameter shape is not supported yet");
    const argument = `arg${index}`;
    this.taken.add(argument);
    for (const element of p.name.elements) {
      if (element.dotDotDotToken || element.initializer || !ts.isIdentifier(element.name)) throw this.t.fail(element, "only plain destructuring is supported for now");
      const field = element.propertyName?.getText() ?? element.name.text;
      prologue.push(`let ${this.rebind(this.symbol(element.name), env)} ← Result.ok (${argument}.${name(field)})`);
    }
    return `(${argument} : ${this.t.type(type, p)})`;
  }

  functionFlow(returns, result) {
    const isVoid = result === "Unit";
    return {
      returns, result,
      fall: () => {
        if (!isVoid) throw this.t.fail(this.fn, "a path reaches the end of the function without `return`");
        return ["Result.ok ()"];
      },
      ret: value => [`Result.ok ${value}`],
    };
  }

  // A path that ends by joining the code after a branch. Only `vars` change.
  joinFlow(vars, outer) {
    return {
      returns: outer.returns, result: outer.result,
      fall: env => [`Result.ok ${this.tuple(vars, env)}`],
      ret: null,
    };
  }

  // Aeneas's `do` can't elaborate a name rebound in a nested block, so nothing
  // is ever shadowed: each assignment makes a new name, and `env` tracks which
  // name is current for a variable on this path.
  current(symbol, env) {
    return env.get(symbol)?.lean ?? local(symbol.name);
  }

  rebind(symbol, env, extra = {}) {
    const base = local(symbol.name);
    let lean = base;
    for (let version = 1; this.taken.has(lean) || (lean !== base && this.names.has(lean)); version += 1) {
      lean = base.startsWith("«") ? `${symbol.name}_v${version}` : `${base}_${version}`;
    }
    this.taken.add(lean);
    // What was learned about its fields no longer holds.
    for (const key of [...env.keys()]) {
      if (typeof key === "string" && (key.startsWith(`field:${symbol.name}.`))) env.delete(key);
    }
    const { tag, bound } = env.get(symbol) ?? {};
    env.set(symbol, { tag, bound, ...extra, lean });
    return lean;
  }

  tuple(vars, env) {
    if (!vars.length) return "()";
    const names = vars.map(v => this.current(v, env));
    return names.length === 1 ? names[0] : `(${names.join(", ")})`;
  }

  // Binds `vars` to new names in `env`, for the code after a join.
  pattern(vars, env) {
    if (!vars.length) return "_";
    const names = vars.map(v => this.rebind(v, env));
    return names.length === 1 ? names[0] : `(${names.join(", ")})`;
  }

  tupleType(vars, node) {
    if (!vars.length) return "Unit";
    return vars.map(v => v.leanType ?? this.t.type(this.declaredType(v, node), node)).join(" × ");
  }

  // Variables declared outside `nodes` and written inside them, in a stable order.
  assignedIn(nodes, declaredInside = () => false) {
    const found = new Map();
    const walk = node => {
      if (ts.isFunctionLike(node) && !this.isForEachBody(node)) return;
      const write = writeTarget(node);
      if (write && !this.isBuiltinReceiver(node, write)) {
        const symbol = this.symbol(rootOf(write));
        if (symbol && !this.isWithin(symbol, nodes) && !declaredInside(symbol)) found.set(symbol.name, symbol);
      }
      ts.forEachChild(node, walk);
    };
    nodes.filter(Boolean).forEach(walk);
    return [...found.keys()].sort().map(key => found.get(key));
  }

  isWithin(symbol, nodes) {
    const declaration = symbol.valueDeclaration;
    return nodes.some(node => node && declaration.pos >= node.pos && declaration.end <= node.end
      && declaration.getSourceFile() === node.getSourceFile());
  }

  // Does this contain a `return`, `break` or `continue` that leaves it?
  jumps(node) {
    if (!node) return false;
    let found = false;
    const walk = (current, loop, breakable) => {
      if (found || ts.isFunctionLike(current)) return;
      if (ts.isReturnStatement(current)) found = true;
      else if (ts.isBreakStatement(current) && !breakable) found = true;
      else if (ts.isContinueStatement(current) && !loop) found = true;
      else {
        const inLoop = loop || ts.isIterationStatement(current, false);
        const inBreakable = breakable || ts.isIterationStatement(current, false) || ts.isSwitchStatement(current);
        ts.forEachChild(current, child => walk(child, inLoop, inBreakable));
      }
    };
    walk(node, false, false);
    return found;
  }

  fresh() {
    let candidate;
    do { candidate = `tmp${++this.counter}`; } while (this.names.has(candidate));
    return candidate;
  }

  symbol(node) {
    // In `{ a }`, the name is both a property and a read of the variable `a`.
    const symbol = node.parent && ts.isShorthandPropertyAssignment(node.parent)
      ? this.checker.getShorthandAssignmentValueSymbol(node.parent)
      : this.checker.getSymbolAtLocation(node);
    return symbol && symbol.flags & ts.SymbolFlags.Alias ? this.checker.getAliasedSymbol(symbol) : symbol;
  }

  typeOf(node) {
    return this.checker.getTypeAtLocation(node);
  }

  isNumber(node) {
    const type = this.typeOf(node);
    return (type.flags & ts.TypeFlags.NumberLike) !== 0 || (type.isUnion() && type.types.every(t => t.flags & ts.TypeFlags.NumberLike));
  }
  // A string, or an unnamed union of strings, which `type` also calls `Js.Str`.
  isText(node) {
    const type = this.typeOf(node);
    return this.isString(node) || (type.isUnion() && !type.aliasSymbol && type.types.every(t => t.flags & ts.TypeFlags.StringLike));
  }
  // The Lean type of `type`, when it has one.
  leanOf(type, node) {
    try {
      return this.t.type(type, node);
    } catch (error) {
      if (error instanceof Unsupported) return undefined;
      throw error;
    }
  }
  // Which nullish values a type allows.
  nothing(type) {
    const kinds = type.isUnion() ? type.types.filter(t => t.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined)) : [];
    if (kinds.length > 1) return "both";
    return kinds[0]?.flags & ts.TypeFlags.Null ? "null" : kinds.length ? "undefined" : undefined;
  }
  isBoolean(node) { return (this.typeOf(node).flags & ts.TypeFlags.BooleanLike) !== 0; }
  isBigInt(node) {
    return (this.typeOf(node).flags & ts.TypeFlags.BigIntLike) !== 0;
  }
  isUndefined(node) {
    return ts.isIdentifier(node) && node.text === "undefined" && !this.symbol(node)?.valueDeclaration;
  }

  isNull(node) {
    node = unwrap(node);
    return node.kind === ts.SyntaxKind.NullKeyword || this.isUndefined(node);
  }

  // The declared type of a variable, ignoring narrowing.
  declaredType(symbol, node) {
    return this.checker.getTypeOfSymbolAtLocation(symbol, symbol.valueDeclaration ?? node);
  }

  // The type a variable or field is stored as. An earlier test can narrow an
  // enumeration to one member, and TypeScript then reports a plain literal.
  storedType(node) {
    if (ts.isIdentifier(node)) {
      const symbol = this.symbol(node);
      if (symbol?.valueDeclaration) return this.declaredType(symbol, node);
    }
    if (ts.isPropertyAccessExpression(node)) {
      const field = this.typeOf(node.expression).getProperty(node.name.text);
      if (field) return this.checker.getTypeOfSymbol(field);
    }
    return this.typeOf(node);
  }

  // ------------------------------------------------------------ statements

  // Lines for `statements`, followed by whatever `flow` does at the end. Local
  // bindings are written `let x ← Result.ok v`: Aeneas's `do` can't elaborate a
  // plain `let` inside a loop body, and `step*` removes these for free.
  block(statements, flow, env) {
    if (!statements.length) return flow.fall(env);
    const [first, ...rest] = statements;
    if (ts.isBlock(first)) {
      // Inner declarations go out of scope, which Lean's shadowing can't express
      // once code follows the block, so a block with declarations must join.
      const declares = first.statements.some(ts.isVariableStatement);
      if (declares && rest.length && !this.exits(first)) return this.joined(first, rest, flow, env);
      return this.block([...first.statements, ...rest], flow, env);
    }
    if (ts.isEmptyStatement(first)) return this.block(rest, flow, env);
    if (ts.isReturnStatement(first)) {
      if (!flow.ret) throw this.t.fail(first, "`return` here is not supported yet");
      if (flow.discard) {
        const lines = [];
        if (first.expression) this.expression(first.expression, env, lines);
        return [...lines, ...flow.ret("()", env)];
      }
      if (!first.expression) {
        if (flow.result !== "Unit") throw this.t.fail(first, "`return` without a value");
        return flow.ret("()", env);
      }
      return this.returning(first.expression, flow, env);
    }
    if (ts.isThrowStatement(first)) return this.throwing(first);
    if (ts.isBreakStatement(first) || ts.isContinueStatement(first)) {
      if (first.label) throw this.t.fail(first, "labels are not supported");
      const leave = ts.isBreakStatement(first) ? flow.brk : flow.cont;
      if (!leave) throw this.t.fail(first, "this `break` or `continue` is not supported yet");
      return leave(env);
    }
    if (ts.isVariableStatement(first)) return this.variable(first, rest, flow, env);
    if (ts.isExpressionStatement(first) && ts.isCallExpression(unwrap(first.expression))
      && unwrap(first.expression).arguments[0] && this.isForEachBody(unwrap(unwrap(first.expression).arguments[0]))) {
      return this.forEach(first, unwrap(first.expression), rest, flow, env);
    }
    if (ts.isExpressionStatement(first)) return this.effect(first, rest, flow, env);
    if (ts.isIfStatement(first)) return this.conditional(first, rest, flow, env);
    if (ts.isSwitchStatement(first)) return this.switching(first, rest, flow, env);
    if (ts.isTryStatement(first)) return this.attempt(first, rest, flow, env);
    if (ts.isForOfStatement(first)) return this.forOf(first, rest, flow, env);
    if (ts.isForStatement(first)) return this.forLoop(first, rest, flow, env);
    if (ts.isWhileStatement(first)) return this.whileLoop(first, rest, flow, env);
    throw this.t.fail(first, `\`${ts.SyntaxKind[first.kind]}\` is not supported yet`);
  }

  // Runs `node` as its own sequence, then continues with `rest`.
  joined(node, rest, flow, env) {
    if (this.jumps(node)) throw this.t.fail(node, "a nested block that returns is not supported yet");
    const vars = this.assignedIn([node]);
    const inner = this.block([...node.statements], this.joinFlow(vars, flow), new Map(env));
    const after = new Map(env);
    return [`let ${this.pattern(vars, after)} ← do`, ...this.indent(inner), ...this.block(rest, flow, after)];
  }

  returning(node, flow, env) {
    const lines = [];
    const value = this.convert(node, flow.returns, env, lines);
    return [...lines, ...flow.ret(value, env)];
  }

  // A thrown value stops the function. `.panic` is only ever produced here, which
  // is how `try` tells a thrown exception from leaving the model.
  throwing(statement) {
    const thrown = unwrap(statement.expression);
    let simple = ts.isNewExpression(thrown);
    const walk = node => {
      if (ts.isCallExpression(node) || (node !== thrown && ts.isNewExpression(node))) simple = false;
      ts.forEachChild(node, walk);
    };
    walk(thrown);
    if (!simple) throw this.t.fail(statement, "only `throw new SomeError(...)` is supported for now");
    return ["Result.fail .panic"];
  }

  variable(statement, rest, flow, env) {
    if (!(statement.declarationList.flags & ts.NodeFlags.BlockScoped)) throw this.t.fail(statement, "`var` is not supported");
    const lines = [];
    const next = new Map(env);
    for (const declaration of statement.declarationList.declarations) {
      if (!declaration.initializer) throw this.t.fail(declaration, "a declaration without a value");
      if (ts.isIdentifier(declaration.name)) {
        const symbol = this.symbol(declaration.name);
        const value = this.convert(declaration.initializer, this.declaredType(symbol, declaration.name), next, lines);
        lines.push(`let ${this.rebind(symbol, next)} ← Result.ok (${value})`);
        continue;
      }
      if (!ts.isObjectBindingPattern(declaration.name)) throw this.t.fail(declaration, "array destructuring is not supported yet");
      const source = this.expression(declaration.initializer, next, lines);
      for (const element of declaration.name.elements) {
        if (element.dotDotDotToken || element.initializer || !ts.isIdentifier(element.name)) {
          throw this.t.fail(element, "only plain destructuring is supported for now");
        }
        const field = element.propertyName?.getText() ?? element.name.text;
        lines.push(`let ${this.rebind(this.symbol(element.name), next)} ← Result.ok (${source}.${name(field)})`);
      }
    }
    return [...lines, ...this.block(rest, flow, next)];
  }

  // An expression used as a statement: an assignment, an update or a call.
  effect(statement, rest, flow, env) {
    const node = unwrap(statement.expression);
    const lines = [];
    const next = new Map(env);
    if (ts.isBinaryExpression(node) && ts.isAssignmentOperator(node.operatorToken.kind)) {
      this.assign(node, next, lines);
    } else if (ts.isPrefixUnaryExpression(node) || ts.isPostfixUnaryExpression(node)) {
      if (!isUpdate(node)) throw this.t.fail(node, "this statement has no effect");
      const target = unwrap(node.operand);
      const op = node.operator === ts.SyntaxKind.PlusPlusToken ? ts.SyntaxKind.PlusToken : ts.SyntaxKind.MinusToken;
      this.update(target, op, ONE, next, lines);
    } else if (ts.isCallExpression(node)) {
      if (!this.mutation(node, next, lines)) this.expression(node, next, lines);
    } else {
      throw this.t.fail(node, "this statement is not supported yet");
    }
    return [...lines, ...this.block(rest, flow, next)];
  }

  // `xs.push(v)` and friends, used as statements on an owned array.
  mutation(node, env, lines) {
    const callee = unwrap(node.expression);
    if (!ts.isPropertyAccessExpression(callee) || !MUTATING.has(callee.name.text)) return false;
    if (this.isCollection(callee.expression)) return this.collectionWrite(callee, node, env, lines);
    if (!this.isArray(callee.expression)) return false;
    const receiver = unwrap(callee.expression);
    const symbol = this.symbol(receiver);
    const list = this.current(symbol, env);
    const item = this.checker.getTypeArguments(this.checker.getApparentType(this.typeOf(receiver)))[0];
    const items = () => `[${node.arguments.map(a => this.convert(a, item, env, lines)).join(", ")}]`;
    let value;
    switch (callee.name.text) {
      case "push": value = `${list} ++ ${items()}`; break;
      case "unshift": value = `${items()} ++ ${list}`; break;
      case "pop": value = `${list}.dropLast`; break;
      case "shift": value = `${list}.tail`; break;
      case "reverse": value = `${list}.reverse`; break;
      default: throw this.t.fail(node, `\`${callee.name.text}\` is not supported yet`);
    }
    lines.push(`let ${this.rebind(symbol, env)} ← Result.ok (${value})`);
    return true;
  }

  collectionWrite(callee, node, env, lines) {
    const receiver = unwrap(callee.expression);
    const symbol = this.symbol(receiver);
    const current = this.current(symbol, env);
    const { kind, args: types } = this.t.collection(this.typeOf(receiver));
    const args = node.arguments;
    const arg = index => this.convert(args[index], types[index], env, lines);
    let value;
    if (kind === "Map" && callee.name.text === "set") value = `Js.dictSet ${current} ${arg(0)} ${arg(1)}`;
    else if (kind === "Map" && callee.name.text === "delete") value = `Js.dictDelete ${current} ${arg(0)}`;
    else if (kind === "Set" && callee.name.text === "add") value = `Js.setAdd ${current} ${arg(0)}`;
    else if (kind === "Set" && callee.name.text === "delete") value = `Js.setDelete ${current} ${arg(0)}`;
    else if (callee.name.text === "clear") value = "[]";
    else throw this.t.fail(node, `\`${callee.name.text}\` is not supported yet`);
    lines.push(`let ${this.rebind(symbol, env)} ← Result.ok (${value})`);
    return true;
  }

  // `x.field = v` and `xs[i] = v` on an owned value.
  writeInto(node, env, lines) {
    const target = unwrap(node.left);
    if (node.operatorToken.kind !== ts.SyntaxKind.EqualsToken) throw this.t.fail(node, "only `=` is supported on a field or element for now");
    const owner = unwrap(target.expression);
    const symbol = this.symbol(owner);
    const current = this.current(symbol, env);
    if (ts.isElementAccessExpression(target)) {
      const item = this.checker.getTypeArguments(this.checker.getApparentType(this.typeOf(owner)))[0];
      const value = this.convert(node.right, item, env, lines);
      const index = this.numeric(target.argumentExpression, env, lines);
      lines.push(`let ${this.rebind(symbol, env)} ← Js.setAt ${current} ${index} ${value}`);
      return;
    }
    const property = this.checker.getPropertyOfType(this.typeOf(owner), target.name.text);
    const slot = this.checker.getTypeOfSymbolAtLocation(property, property.valueDeclaration);
    const value = this.convert(node.right, slot, env, lines);
    lines.push(`let ${this.rebind(symbol, env)} ← Result.ok ({ ${current} with ${name(target.name.text)} := ${value} } : ${this.t.type(this.typeOf(owner), owner)})`);
  }

  assign(node, env, lines) {
    const target = unwrap(node.left);
    if (!ts.isIdentifier(target)) return this.writeInto(node, env, lines);
    const symbol = this.symbol(target);
    if (env.get(symbol)?.present) throw this.t.fail(node, "assigning to a variable inside its own null check is not supported yet");
    const op = node.operatorToken.kind;
    if (op === ts.SyntaxKind.EqualsToken) {
      const value = this.convert(node.right, this.declaredType(symbol, target), env, lines);
      lines.push(`let ${this.rebind(symbol, env)} ← Result.ok (${value})`);
      return;
    }
    const base = COMPOUND[op];
    if (!base) throw this.t.fail(node, "this assignment operator is not supported yet");
    this.update(target, base, node.right, env, lines);
  }

  update(target, op, operand, env, lines) {
    if (!ts.isIdentifier(target)) throw this.t.fail(target, "assigning to a field or element is not supported yet");
    const left = this.expression(target, env, lines);
    const value = this.arithmetic(op, target, left, operand, env, lines);
    lines.push(`let ${this.rebind(this.symbol(target), env)} ← Result.ok (${value})`);
  }

  // Paths that end by returning, breaking or throwing.
  exits(node) {
    if (ts.isReturnStatement(node) || ts.isThrowStatement(node) || ts.isBreakStatement(node) || ts.isContinueStatement(node)) return true;
    if (ts.isBlock(node)) return node.statements.some(s => this.exits(s));
    if (ts.isIfStatement(node)) return Boolean(node.elseStatement) && this.exits(node.thenStatement) && this.exits(node.elseStatement);
    return false;
  }

  // A test whose left side narrows, such as `x !== null && x.y > 0`, is two
  // nested tests, so that the right side and the branch see the narrowed value.
  splitTest(test, env, arm) {
    test = unwrap(test);
    if (ts.isBinaryExpression(test) && test.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken) {
      const narrowed = this.narrowing(test.left, env);
      if (narrowed) return narrowed((onPath, next) => (onPath ? this.splitTest(test.right, next, arm) : arm(false, next)));
    }
    if (ts.isBinaryExpression(test) && test.operatorToken.kind === ts.SyntaxKind.BarBarToken) {
      const narrowed = this.narrowing(test.left, env);
      if (narrowed) return narrowed((onPath, next) => (onPath ? arm(true, next) : this.splitTest(test.right, next, arm)));
    }
    const narrowed = this.narrowing(test, env);
    if (narrowed) return narrowed(arm);
    const lines = [];
    const condition = this.condition(test, env, lines);
    return [...lines, `if ${condition} then`, ...this.indent(arm(true, env)), "else", ...this.indent(arm(false, env))];
  }

  splits(test) {
    test = unwrap(test);
    return ts.isBinaryExpression(test) && (test.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken || test.operatorToken.kind === ts.SyntaxKind.BarBarToken)
      && Boolean(this.narrowing(test.left, new Map()));
  }

  conditional(statement, rest, flow, env) {
    const whenTrue = statement.thenStatement;
    const whenFalse = statement.elseStatement;
    const trueExits = this.exits(whenTrue);
    const falseExits = whenFalse ? this.exits(whenFalse) : false;
    const narrowed = this.splits(statement.expression)
      ? arm => this.splitTest(statement.expression, env, arm)
      : this.narrowing(statement.expression, env);

    // Neither branch leaves, so both can join the code that follows.
    if (!trueExits && !falseExits && rest.length && !this.jumps(whenTrue) && !this.jumps(whenFalse)) {
      const vars = this.assignedIn([whenTrue, whenFalse]);
      const join = this.joinFlow(vars, flow);
      const arm = (onPath, branchEnv) => {
        const chosen = onPath ? whenTrue : whenFalse;
        return this.block(chosen ? [chosen] : [], join, new Map(branchEnv));
      };
      if (narrowed) {
        const arms = narrowed(arm);
        const after = new Map(env);
        return [`let ${this.pattern(vars, after)} ← do`, ...this.indent(arms), ...this.block(rest, flow, after)];
      }
      const lines = [];
      const test = this.condition(statement.expression, env, lines);
      const thenLines = arm(true, env), elseLines = arm(false, env);
      const after = new Map(env);
      return [...lines, `let ${this.pattern(vars, after)} ← if ${test} then`, ...this.indent(this.indent(thenLines)),
        "  else", ...this.indent(this.indent(elseLines)), ...this.block(rest, flow, after)];
    }

    // Otherwise each branch continues with its own copy of what follows.
    const thenPath = trueExits ? [whenTrue] : [whenTrue, ...rest];
    const elsePath = falseExits ? [whenFalse] : [...(whenFalse ? [whenFalse] : []), ...rest];
    const arm = (onPath, branchEnv) => this.block(onPath ? thenPath : elsePath, flow, new Map(branchEnv));
    if (narrowed) return narrowed(arm);
    const lines = [];
    const test = this.condition(statement.expression, env, lines);
    return [...lines, `if ${test} then`, ...this.indent(arm(true, env)), "else", ...this.indent(arm(false, env))];
  }

  // `try`: the catch block runs only for a thrown exception. A value that left
  // the model stays a failure, so it can't be mistaken for one.
  attempt(statement, rest, flow, env) {
    if (statement.finallyBlock) throw this.t.fail(statement, "`finally` is not supported yet");
    const clause = statement.catchClause;
    if (clause.variableDeclaration && this.usedIn(clause.variableDeclaration, clause.block)) {
      throw this.t.fail(clause, "reading the caught value is not supported yet");
    }
    const attempted = statement.tryBlock;
    if (this.assignedIn([attempted]).length) {
      throw this.t.fail(attempted, "assigning to an outer variable inside `try` is not supported yet");
    }
    const bothReturn = this.jumps(attempted) || this.jumps(clause.block);
    let inner = flow, vars = null;
    if (!bothReturn) {
      vars = this.assignedIn([clause.block]);
      inner = this.joinFlow(vars, flow);
    } else if (!this.exits(attempted) || !this.exits(clause.block)) {
      throw this.t.fail(statement, "`try` must either always return or never return for now");
    }
    const body = [...this.indent(this.block([...attempted.statements], inner, new Map(env))),
      ") (do", ...this.indent(this.block([...clause.block.statements], inner, new Map(env))), ")"];
    if (!vars) return ["Js.attempt (do", ...body];
    const after = new Map(env);
    return [`let ${this.pattern(vars, after)} ← Js.attempt (do`, ...body, ...this.block(rest, flow, after)];
  }

  usedIn(declaration, node) {
    const symbol = declaration.symbol ?? this.checker.getSymbolAtLocation(declaration.name);
    let used = false;
    const walk = current => {
      if (ts.isIdentifier(current) && this.symbol(current) === symbol) used = true;
      ts.forEachChild(current, walk);
    };
    walk(node);
    return used;
  }

  // ----------------------------------------------------------------- loops

  // `step` builds one iteration, given the flow for its body. `leaving` is what
  // the code after the loop can see, which excludes a `for` loop's counters.
  emitLoop(statement, vars, rest, flow, env, step, leaving = vars) {
    const returns = this.jumpsOut(statement);
    const inside = new Map(env);
    const pattern = vars.length ? this.pattern(vars, inside) : "()";
    const stateType = this.tupleType(vars, statement);
    const afterType = this.tupleType(leaving, statement);
    const leave = stepEnv => (returns
      ? `Result.ok (.done (.inr ${this.tuple(leaving, stepEnv)}))`
      : `Result.ok (.done ${this.tuple(leaving, stepEnv)})`);
    const again = stepEnv => [`Result.ok (.cont ${this.tuple(vars, stepEnv)})`];
    const body = {
      returns: flow.returns, result: flow.result,
      fall: null, cont: null, brk: stepEnv => [leave(stepEnv)],
      ret: value => [returns ? `Result.ok (.done (.inl ${value}))` : `Result.ok (.done ${value})`],
    };
    const lines = step(body, inside, leave, again);
    const result = returns ? `Sum (${flow.result}) (${afterType})` : afterType;
    const header = `(Aeneas.Std.loop (fun (state : ${stateType}) => match state with | ${pattern} => do`;
    const call = [header, ...this.indent(lines), `) ${this.tuple(vars, env)} : Result (${result}))`];
    const after = new Map(env);
    if (!returns) return [`let ${this.pattern(leaving, after)} ← ${call[0]}`, ...call.slice(1), ...this.block(rest, flow, after)];
    if (!flow.ret) throw this.t.fail(statement, "`return` here is not supported yet");
    const value = this.fresh();
    const carried = this.fresh();
    return [`let ${value} ← ${call[0]}`, ...call.slice(1), `match ${value} with`,
      `| .inl ${carried} =>`, ...this.indent(flow.ret(carried)),
      `| .inr ${this.pattern(leaving, after)} =>`, ...this.indent(this.block(rest, flow, after))];
  }

  jumpsOut(statement) {
    let found = false;
    const walk = node => {
      if (ts.isFunctionLike(node)) return;
      if (ts.isReturnStatement(node)) found = true;
      ts.forEachChild(node, walk);
    };
    walk(statement);
    return found;
  }

  whileLoop(statement, rest, flow, env) {
    const vars = this.assignedIn([statement]);
    return this.emitLoop(statement, vars, rest, flow, env, (body, inside, leave, again) => {
      const lines = [];
      const test = this.condition(statement.expression, inside, lines);
      const inner = this.block([statement.statement], { ...body, fall: again, cont: again }, new Map(inside));
      return [...lines, `if ${test} then`, ...this.indent(inner), "else", `  ${leave(inside)}`];
    });
  }

  forLoop(statement, rest, flow, env) {
    const initializer = statement.initializer;
    if (!initializer || !ts.isVariableDeclarationList(initializer)) throw this.t.fail(statement, "a `for` loop needs a declaration");
    if (!(initializer.flags & ts.NodeFlags.BlockScoped)) throw this.t.fail(statement, "`var` is not supported");
    if (!statement.condition || !statement.incrementor) throw this.t.fail(statement, "a `for` loop needs a condition and an update");
    const lines = [];
    const start = new Map(env);
    for (const declaration of initializer.declarations) {
      if (!ts.isIdentifier(declaration.name) || !declaration.initializer) throw this.t.fail(declaration, "a `for` loop needs plain declarations");
      const symbol = this.symbol(declaration.name);
      const value = this.convert(declaration.initializer, this.declaredType(symbol, declaration.name), start, lines);
      lines.push(`let ${this.rebind(symbol, start)} ← Result.ok (${value})`);
    }
    // The counters live in the loop's state, but nothing after the loop sees them.
    const counters = this.declaredBy(initializer).filter(symbol => this.isWrittenIn(symbol, statement));
    const outer = this.assignedIn([statement]);
    const code = this.emitLoop(statement, [...counters, ...outer], rest, flow, start, (body, inside, leave, again) => {
      const head = [];
      const test = this.condition(statement.condition, inside, head);
      const advance = stepEnv => {
        const lines2 = [];
        const next = new Map(stepEnv);
        const change = unwrap(statement.incrementor);
        if (ts.isBinaryExpression(change)) this.assign(change, next, lines2);
        else if ((ts.isPrefixUnaryExpression(change) || ts.isPostfixUnaryExpression(change)) && isUpdate(change)) {
          const op = change.operator === ts.SyntaxKind.PlusPlusToken ? ts.SyntaxKind.PlusToken : ts.SyntaxKind.MinusToken;
          this.update(unwrap(change.operand), op, ONE, next, lines2);
        } else throw this.t.fail(change, "this `for` update is not supported yet");
        return [...lines2, ...again(next)];
      };
      const inner = this.block([statement.statement], { ...body, fall: advance, cont: advance }, new Map(inside));
      return [...head, `if ${test} then`, ...this.indent(inner), "else", `  ${leave(inside)}`];
    }, outer);
    return [...lines, ...code];
  }

  declaredBy(list) {
    return list.declarations.map(d => this.symbol(d.name));
  }

  isWrittenIn(symbol, node) {
    let found = false;
    const walk = current => {
      const write = writeTarget(current);
      if (write && this.symbol(rootOf(write)) === symbol) found = true;
      ts.forEachChild(current, walk);
    };
    walk(node);
    return found;
  }

  forEach(statement, call, rest, flow, env) {
    const callback = unwrap(call.arguments[0]);
    if (!ts.isIdentifier(callback.parameters[0].name)) throw this.t.fail(callback, "only a plain parameter is supported here for now");
    const body = ts.isBlock(callback.body) ? callback.body : ts.factory.createExpressionStatement(callback.body);
    if (!ts.isBlock(callback.body)) body.parent = callback;
    return this.walkArray(statement, unwrap(call.expression).expression, callback.parameters[0].name, body, rest, flow, env, true);
  }

  forOf(statement, rest, flow, env) {
    if (statement.awaitModifier) throw this.t.fail(statement, "`for await` is not supported");
    const iterated = this.isArray(statement.expression) || this.t.collection(this.typeOf(statement.expression))?.kind === "Set";
    if (!iterated) throw this.t.fail(statement.expression, "`for...of` is only supported on arrays and sets for now");
    const declaration = statement.initializer.declarations?.[0];
    if (!declaration || !ts.isIdentifier(declaration.name)) throw this.t.fail(statement, "`for...of` needs a plain variable for now");
    return this.walkArray(statement, statement.expression, declaration.name, statement.statement, rest, flow, env, false);
  }

  walkArray(statement, array, variable, loopBody, rest, flow, env, isCallback) {
    const lines = [];
    const start = new Map(env);
    const iterated = this.expression(array, start, lines);
    const remaining = { name: this.fresh(), leanType: this.t.type(this.typeOf(array), statement) };
    start.set(remaining, { lean: remaining.name });
    this.taken.add(remaining.name);
    lines.push(`let ${remaining.name} ← Result.ok (${iterated})`);
    const outer = this.assignedIn([statement]);
    const element = this.symbol(variable);
    const code = this.emitLoop(statement, [remaining, ...outer], rest, flow, start, (body, inside, leave, again) => {
      const next = new Map(inside);
      const head = this.rebind(element, next);
      const tail = this.fresh();
      next.set(remaining, { lean: tail });
      // In a callback, `return` only ends this call.
      const loopFlow = { ...body, fall: again, cont: again, ...(isCallback ? { ret: (_value, stepEnv) => again(stepEnv), brk: null, discard: true } : {}) };
      const inner = this.block([loopBody], loopFlow, next);
      return [`match ${this.current(remaining, inside)} with`, `| [] =>`, `  ${leave(inside)}`, `| ${head} :: ${tail} =>`, ...this.indent(inner)];
    }, outer);
    return [...lines, ...code];
  }

  indent(lines) { return lines.map(l => `  ${l}`); }

  // `x === null` and `x !== null` on a variable become a `match`, so that the
  // branch where it is present sees the plain value.
  narrowing(test, env) {
    test = unwrap(test);
    if (ts.isPrefixUnaryExpression(test) && test.operator === ts.SyntaxKind.ExclamationToken) {
      const inner = this.narrowing(test.operand, env);
      return inner && (arm => inner((onPath, branchEnv) => arm(!onPath, branchEnv)));
    }
    // `if (x)` on a nullable object: objects are always truthy.
    if (ts.isIdentifier(test) && this.nullable(this.declaredType(this.symbol(test), test))) {
      const inner = this.checker.getNonNullableType(this.declaredType(this.symbol(test), test));
      if (inner.flags & ts.TypeFlags.Object) {
        const symbol = this.symbol(test);
        return arm => {
          const next = new Map(env);
          const lean = this.rebind(symbol, next, { present: true });
          return [`match ${this.current(symbol, env)} with`, "| none =>", ...this.indent(arm(false, env)), `| some ${lean} =>`, ...this.indent(arm(true, next))];
        };
      }
    }
    const truthy = this.truthyNarrowing(test, env);
    if (truthy) return truthy;
    if (!ts.isBinaryExpression(test)) return undefined;
    const op = test.operatorToken.kind;
    const equal = op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.EqualsEqualsToken;
    const different = op === ts.SyntaxKind.ExclamationEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken;
    if (!equal && !different) return undefined;
    const [variable, other] = this.isNull(test.right) ? [unwrap(test.left), test.right] : [unwrap(test.right), test.left];
    if (!this.isNull(other)) return undefined;
    if (this.isFieldPath(variable)) return this.narrowField(variable, other, op, equal, env);
    if (!ts.isIdentifier(variable)) throw this.t.fail(test, "only a variable or field can be tested against null for now");
    const symbol = this.symbol(variable);
    // `===` tells null from undefined, and a type only ever allows one of them
    // here, so testing for the other one is always false.
    const strict = op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsEqualsToken;
    const allowed = this.declaredType(symbol, variable);
    const wanted = this.isUndefined(unwrap(other)) ? ts.TypeFlags.Undefined : ts.TypeFlags.Null;
    const kinds = allowed.isUnion() ? allowed.types.filter(t => t.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined)).length : 0;
    if (strict && !(allowed.isUnion() && allowed.types.some(t => t.flags & wanted))) {
      throw this.t.fail(test, "this null check is always false, because the type allows the other nullish value");
    }
    if (strict && kinds > 1) throw this.t.fail(test, "`===` can't tell `null` from `undefined` here; use `== null`");
    const lean = this.current(symbol, env);
    return arm => {
      const next = new Map(env);
      const inner = this.rebind(symbol, next, { present: true });
      return [`match ${lean} with`, "| none =>", ...this.indent(arm(equal, env)), `| some ${inner} =>`, ...this.indent(arm(!equal, next))];
    };
  }

  // `if (x)` on an optional string, number or field: a present value can still be
  // falsy, so the test comes first and the value is only read on the truthy side.
  truthyNarrowing(test, env) {
    const field = ts.isPropertyAccessExpression(test) && this.isFieldPath(test);
    if (!ts.isIdentifier(test) && !field) return undefined;
    const declared = ts.isIdentifier(test) ? this.declaredType(this.symbol(test), test) : this.typeOf(test);
    if (!declared.isUnion() || !this.nullable(declared)) return undefined;
    const lines = [];
    const value = this.expression(test, env, lines);
    if (lines.length) return undefined;
    const condition = this.present(value, this.checker.getNonNullableType(declared), test);
    return arm => {
      const next = new Map(env);
      let lean;
      if (ts.isIdentifier(test)) lean = this.rebind(this.symbol(test), next, { present: true });
      else {
        lean = this.fresh();
        next.set(this.fieldKey(test), { lean });
      }
      return [`if ${condition} then`, ...this.indent([`let ${lean} ← Js.unwrap ${value}`, ...arm(true, next)]), "else", ...this.indent(arm(false, env))];
    };
  }

  // `a.b.c`, with no calls, so reading it twice can't change anything.
  isFieldPath(node) {
    node = unwrap(node);
    if (!ts.isPropertyAccessExpression(node) || node.questionDotToken) return false;
    const owner = unwrap(node.expression);
    return ts.isIdentifier(owner) || this.isFieldPath(owner);
  }

  fieldKey(node) { return `field:${unwrap(node).getText()}`; }

  narrowField(field, other, op, equal, env) {
    const strict = op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsEqualsToken;
    const declared = this.typeOf(field);
    const kinds = declared.isUnion() ? declared.types.filter(t => t.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined)) : [];
    const wanted = this.isUndefined(unwrap(other)) ? ts.TypeFlags.Undefined : ts.TypeFlags.Null;
    if (!kinds.length) throw this.t.fail(field, "this field can't be null here");
    if (strict && !kinds.some(t => t.flags & wanted)) throw this.t.fail(field, "this null check is always false, because the type allows the other nullish value");
    if (strict && kinds.length > 1) throw this.t.fail(field, "`===` can't tell `null` from `undefined` here; use `== null`");
    const lines = [];
    const value = this.expression(field, env, lines);
    if (lines.length) throw this.t.fail(field, "this null check is not supported yet");
    return arm => {
      const next = new Map(env);
      const fresh = this.fresh();
      next.set(this.fieldKey(field), { lean: fresh });
      return [`match ${value} with`, "| none =>", ...this.indent(arm(equal, env)), `| some ${fresh} =>`, ...this.indent(arm(!equal, next))];
    };
  }

  switching(statement, rest, flow, env) {
    const subject = unwrap(statement.expression);
    let owner, shape;
    if (ts.isPropertyAccessExpression(subject) && subject.name.text === "kind" && ts.isIdentifier(subject.expression)) {
      owner = subject.expression;
      shape = this.declareFor(owner);
      if (shape?.kind !== "tagged") throw this.t.fail(statement, "`switch` on `.kind` needs a tagged union");
    } else if (ts.isIdentifier(subject)) {
      owner = subject;
      shape = this.declareFor(owner);
      if (shape?.kind !== "enum") throw this.t.fail(statement, "`switch` needs a tagged union or string-literal union");
    } else {
      throw this.t.fail(statement, "`switch` needs a tagged union or string-literal union");
    }
    const tags = shape.kind === "tagged" ? shape.variants.map(v => v.tag) : shape.tags;
    const arms = new Map();
    let fallback, pending = [];
    for (const clause of statement.caseBlock.clauses) {
      if (!ts.isDefaultClause(clause)) {
        const label = unwrap(clause.expression);
        if (!ts.isStringLiteral(label)) throw this.t.fail(clause, "case labels must be string literals");
        pending.push(label.text);
      }
      if (!clause.statements.length) {
        if (ts.isDefaultClause(clause)) throw this.t.fail(clause, "an empty `default` is not supported yet");
        continue;
      }
      const statements = [...clause.statements];
      const last = statements.at(-1);
      if (ts.isBreakStatement(last) && !last.label) statements.pop();
      else if (!this.exits(last) && clause !== statement.caseBlock.clauses.at(-1)) {
        throw this.t.fail(clause, "falling through to the next case is not supported");
      }
      if (statements.some(s => this.containsBreak(s))) throw this.t.fail(clause, "only a final `break` is supported in a case");
      for (const tag of pending) arms.set(tag, statements);
      if (ts.isDefaultClause(clause)) fallback = statements;
      pending = [];
    }
    const symbol = this.symbol(owner);
    const lines = [`match ${this.current(symbol, env)} with`];
    for (const tag of tags) {
      const statements = arms.get(tag) ?? fallback ?? [];
      const path = [...statements, ...rest];
      if (shape.kind === "enum") {
        lines.push(`| .${name(tag)} =>`, ...this.indent(this.block(path, flow, new Map(env))));
        continue;
      }
      const fields = shape.variants.find(v => v.tag === tag).fields;
      const bound = new Map(fields.map(f => [f, this.fresh()]));
      const next = new Map(env);
      next.set(symbol, { ...next.get(symbol), tag, bound });
      lines.push(`| .${name(tag)} ${[...bound.values()].join(" ")} =>`, ...this.indent(this.block(path, flow, next)));
    }
    return lines;
  }

  containsBreak(node) {
    let found = false;
    const walk = (current, inner) => {
      if (ts.isFunctionLike(current)) return;
      if (ts.isBreakStatement(current) && !inner) found = true;
      const nested = inner || ts.isIterationStatement(current, false) || ts.isSwitchStatement(current);
      ts.forEachChild(current, child => walk(child, nested));
    };
    walk(node, false);
    return found;
  }

  declareFor(node) {
    const type = this.declaredType(this.symbol(node), node);
    this.t.type(type, node);
    return this.t.shape(type);
  }

  // ----------------------------------------------------------- expressions

  // Reads `node` as `target`, wrapping it when a plain value flows into a
  // nullable slot. Two different named types are never treated as compatible,
  // because TypeScript's structural typing would let extra fields through.
  convert(node, target, env, lines) {
    node = unwrap(node);
    if (this.isNull(node)) {
      if (!this.nullable(target)) throw this.t.fail(node, "`null` where the type doesn't allow it");
      return "none";
    }
    if (ts.isObjectLiteralExpression(node)) return this.wrapIf(target, this.record(node, target, env, lines), node);
    if (ts.isArrayLiteralExpression(node)) return this.wrapIf(target, this.arrayLiteral(node, target, env, lines), node);
    if (ts.isConditionalExpression(node)) return this.ternary(node, env, lines, target);
    if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken) return this.nullish(node, env, lines, target);
    if (this.isChoice(node)) return this.choice(node, env, lines, target);
    if (ts.isNewExpression(node) && this.isCollection(node)) return this.wrapIf(target, this.newCollection(node, target, env, lines), node);
    if (ts.isStringLiteralLike(node)) {
      const plain = this.nullable(target) ? this.checker.getNonNullableType(target) : target;
      const lean = this.t.type(plain, node);
      if (lean !== "Js.Str") return this.wrapIf(target, `(.${name(node.text)} : ${lean})`, node);
    }
    const value = this.expression(node, env, lines);
    const from = this.t.type(this.narrowedType(node, env), node);
    const to = this.t.type(target, node);
    if (from === to) return value;
    if (to === `(Option ${from})`) return `(some ${value})`;
    // Compiled without index checks, the project assumes this value is present.
    if (from === `(Option ${to})`) return this.bind(`Js.unwrap ${value}`, lines);
    throw this.t.fail(node, `a \`${this.checker.typeToString(this.typeOf(node))}\` is used as a \`${this.checker.typeToString(target)}\`, which is not supported yet`);
  }

  optionalSlot(slot) {
    return this.nullable(slot) ? slot : this.checker.getUnionType?.([slot, this.checker.getUndefinedType()]) ?? slot;
  }

  arrayLiteral(node, target, env, lines) {
    const type = this.nullable(target) ? this.checker.getNonNullableType(target) : target;
    if (!this.checker.isArrayType(type)) throw this.t.fail(node, "tuples are not supported yet");
    return this.arrayItems(node, this.checker.getTypeArguments(type)[0], type, env, lines);
  }

  arrayItems(node, item, type, env, lines) {
    const parts = [];
    let run = [];
    const flush = () => { if (run.length) parts.push(`[${run.join(", ")}]`); run = []; };
    for (const element of node.elements) {
      if (ts.isOmittedExpression(element)) throw this.t.fail(element, "arrays with holes are not supported");
      if (ts.isSpreadElement(element)) {
        flush();
        const set = this.t.collection(this.typeOf(element.expression))?.kind === "Set";
        if (!this.isArray(element.expression) && !set) throw this.t.fail(element, "only arrays and sets can be spread for now");
        parts.push(set ? this.expression(element.expression, env, lines) : this.convert(element.expression, type, env, lines));
      } else {
        run.push(this.convert(element, item, env, lines));
      }
    }
    flush();
    if (!parts.length) return `([] : (List ${this.t.type(item, node)}))`;
    return `(${parts.join(" ++ ")})`;
  }

  newCollection(node, target, env, lines) {
    const type = this.nullable(target) ? this.checker.getNonNullableType(target) : target;
    const args = node.arguments ?? [];
    const lean = this.t.type(type, node); // Checks the keys: objects compare by identity.
    if (!args.length) return `([] : ${lean})`;
    if (this.t.collection(type).kind !== "Set" || args.length !== 1 || !this.isArray(args[0])) {
      throw this.t.fail(node, "only an empty `new Map()`, or `new Set()` on an array, is supported for now");
    }
    // Written out in place, the items take the set's key type, which may be an enumeration.
    const items = unwrap(args[0]);
    const list = ts.isArrayLiteralExpression(items)
      ? this.arrayItems(items, this.t.collection(type).args[0], this.typeOf(items), env, lines)
      : this.convert(items, this.typeOf(items), env, lines);
    return `(Js.setOf ${list})`;
  }

  // The type of what `node` reads, given the branch it is in.
  narrowedType(node, env) {
    if (ts.isIdentifier(node)) {
      const symbol = this.symbol(node);
      const state = env.get(symbol);
      if (symbol?.valueDeclaration && !state) return this.declaredType(symbol, node);
    }
    return this.typeOf(node);
  }

  nullable(type) {
    return type.isUnion() && type.types.some(t => t.flags & (ts.TypeFlags.Null | ts.TypeFlags.Undefined));
  }

  wrapIf(target, value, node) {
    return this.nullable(target) ? `(some ${value})` : value;
  }

  record(node, target, env, lines) {
    const type = this.nullable(target) ? this.checker.getNonNullableType(target) : target;
    this.t.type(type, node);
    const shape = this.t.shape(type);
    if (!shape) throw this.t.fail(node, "an object literal needs a declared type");
    const fields = new Map();
    let base;
    for (const property of node.properties) {
      if (ts.isSpreadAssignment(property)) {
        if (node.properties[0] !== property) throw this.t.fail(property, "a spread must come first");
        base = this.expression(property.expression, env, lines);
      } else if (ts.isPropertyAssignment(property) && (ts.isIdentifier(property.name) || ts.isStringLiteral(property.name))) {
        fields.set(property.name.text, property.initializer);
      } else if (ts.isShorthandPropertyAssignment(property)) {
        fields.set(property.name.text, property.name);
      } else {
        throw this.t.fail(property, "this kind of property is not supported yet");
      }
    }
    if (shape.kind === "record") {
      const properties = this.checker.getPropertiesOfType(type);
      const parts = [];
      for (const property of properties) {
        const value = fields.get(property.name);
        if (!value) {
          if (!base && property.flags & ts.SymbolFlags.Optional) parts.push(`${name(property.name)} := none`);
          continue;
        }
        const slot = this.checker.getTypeOfSymbolAtLocation(property, property.valueDeclaration);
        const declared = property.flags & ts.SymbolFlags.Optional ? this.optionalSlot(slot) : slot;
        parts.push(`${name(property.name)} := ${this.convert(value, declared, env, lines)}`);
      }
      const leanType = this.t.type(type, node);
      return base ? `({ ${base} with ${parts.join(", ")} } : ${leanType})` : `({ ${parts.join(", ")} } : ${leanType})`;
    }
    if (shape.kind !== "tagged" || base) throw this.t.fail(node, "this object literal is not supported yet");
    const tagNode = fields.get("kind");
    if (!tagNode || !ts.isStringLiteralLike(unwrap(tagNode))) throw this.t.fail(node, "a union value needs a literal `kind`");
    const tag = unwrap(tagNode).text;
    const variant = shape.variants.find(v => v.tag === tag);
    const member = type.types.find(t => this.checker.getTypeOfSymbolAtLocation(t.getProperty("kind"), node).value === tag);
    const parts = variant.fields.map(field => {
      const property = member.getProperty(field);
      return this.convert(fields.get(field), this.checker.getTypeOfSymbolAtLocation(property, property.valueDeclaration), env, lines);
    });
    return `(.${name(tag)} ${parts.join(" ")})`;
  }

  // Binds what must be computed and returns an expression with no effects.
  expression(node, env, lines) {
    node = unwrap(node);
    this.lines = lines;
    if (ts.isNumericLiteral(node)) return this.t.number(Number(node.text), node);
    if (ts.isBigIntLiteral(node)) return `(${node.text.slice(0, -1).replace(/_/g, "")} : Int)`;
    if (node.kind === ts.SyntaxKind.TrueKeyword) return "true";
    if (node.kind === ts.SyntaxKind.FalseKeyword) return "false";
    if (ts.isIdentifier(node)) return this.identifier(node, env);
    if (ts.isPropertyAccessExpression(node)) return this.property(node, env, lines);
    if (ts.isArrayLiteralExpression(node)) return this.arrayLiteral(node, this.typeOf(node), env, lines);
    if (ts.isElementAccessExpression(node)) {
      if (this.isString(node.expression)) return `(Js.charAt? ${this.expression(node.expression, env, lines)} ${this.numeric(node.argumentExpression, env, lines)})`;
      if (!this.isArray(node.expression)) throw this.t.fail(node, "`[]` is only supported on arrays for now");
      if (node.questionDotToken) throw this.t.fail(node, "`?.` is not supported yet");
      return `(Js.at_ ${this.expression(node.expression, env, lines)} ${this.numeric(node.argumentExpression, env, lines)})`;
    }
    if (ts.isNonNullExpression(node)) return this.nonNull(node, env, lines);
    if (ts.isCallExpression(node)) return this.call(node, env, lines);
    if (ts.isConditionalExpression(node)) return this.ternary(node, env, lines);
    if (ts.isBinaryExpression(node) && node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken) return this.nullish(node, env, lines);
    if (ts.isSatisfiesExpression(node) || ts.isAsExpression(node)) {
      if (ts.isAsExpression(node) && ts.isConstTypeReference(node.type)) return this.expression(node.expression, env, lines);
      throw this.t.fail(node, "type assertions are not supported yet");
    }
    if (ts.isStringLiteralLike(node)) return this.text(node.text);
    if (ts.isTemplateExpression(node)) return this.template(node, env, lines);
    if (ts.isNewExpression(node) && this.isCollection(node)) return this.newCollection(node, this.typeOf(node), env, lines);
    if (ts.isPrefixUnaryExpression(node)) {
      if (node.operator === ts.SyntaxKind.ExclamationToken) return `(decide (${this.condition(node, env, lines)}))`;
      if (node.operator === ts.SyntaxKind.MinusToken) {
        const literal = this.t.literal(node);
        if (literal !== undefined) return this.t.number(literal, node);
        if (this.isBigInt(node.operand)) return `(-${this.expression(node.operand, env, lines)})`;
        return this.bind(`Js.neg ${this.numeric(node.operand, env, lines)}`, lines);
      }
      throw this.t.fail(node, "this operator is not supported");
    }
    if (ts.isBinaryExpression(node)) {
      const op = node.operatorToken.kind;
      if (ARITHMETIC[op]) return this.arithmetic(op, node.left, this.operand(node.left, env, lines), node.right, env, lines);
      if (this.isChoice(node)) return this.choice(node, env, lines);
      return `(decide (${this.condition(node, env, lines)}))`;
    }
    throw this.t.fail(node, `\`${ts.SyntaxKind[node.kind]}\` is not supported yet`);
  }

  isChoice(node) {
    if (!ts.isBinaryExpression(node)) return false;
    const op = node.operatorToken.kind;
    return (op === ts.SyntaxKind.AmpersandAmpersandToken || op === ts.SyntaxKind.BarBarToken) && !(this.isBoolean(node.left) && this.isBoolean(node.right));
  }

  // `a || b` and `a && b` as values: the result is one side or the other.
  choice(node, env, lines, target) {
    const type = target ?? this.typeOf(node);
    const and = node.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken;
    const left = unwrap(node.left);
    const leftValue = branchEnv => {
      const inner = [];
      const value = this.wrapIf(type, this.expression(left, branchEnv, inner), left);
      return [...inner, `Result.ok ${value}`];
    };
    const rightValue = branchEnv => {
      const inner = [];
      const value = this.convert(node.right, type, branchEnv, inner);
      return [...inner, `Result.ok ${value}`];
    };
    const fresh = this.fresh();
    const narrowed = this.narrowing(left, env);
    const falsy = this.nullable(this.typeOf(left)) ? () => ["Result.ok none"] : leftValue;
    if (narrowed) {
      const arms = narrowed((onPath, next) => (and ? (onPath ? rightValue(next) : falsy(next)) : (onPath ? leftValue(next) : rightValue(next))));
      lines.push(`let ${fresh} ← do`, ...this.indent(arms));
      return fresh;
    }
    // The test and the result both read the left side, so it must be safe to read twice.
    if (!ts.isIdentifier(left) && !this.isFieldPath(left)) throw this.t.fail(node, "the left side of this `&&` or `||` must be a variable or field for now");
    if (this.nullable(this.typeOf(left))) throw this.t.fail(node, "this `&&` or `||` is not supported here yet");
    const test = this.condition(left, env, lines);
    const [whenTrue, whenFalse] = and ? [rightValue(env), leftValue(env)] : [leftValue(env), rightValue(env)];
    lines.push(`let ${fresh} ← if ${test} then`, ...this.indent(this.indent(whenTrue)), "  else", ...this.indent(this.indent(whenFalse)));
    return fresh;
  }

  operand(node, env, lines) {
    if (this.isBigInt(node) || this.isString(node)) return this.expression(node, env, lines);
    return this.numeric(node, env, lines);
  }

  arithmetic(op, leftNode, left, rightNode, env, lines) {
    if (this.isString(leftNode)) {
      if (op !== ts.SyntaxKind.PlusToken || rightNode === ONE || !this.isString(rightNode)) throw this.t.fail(leftNode, "`+` between a string and another type is not supported");
      return `(${left} ++ ${this.expression(rightNode, env, lines)})`;
    }
    const bigint = this.isBigInt(leftNode);
    if (rightNode !== ONE && bigint !== this.isBigInt(rightNode)) throw this.t.fail(rightNode, "mixing `number` and `bigint`");
    const right = rightNode === ONE ? (bigint ? "(1 : Int)" : this.t.number(1, leftNode)) : this.operand(rightNode, env, lines);
    if (!bigint) return this.bind(`Js.${ARITHMETIC[op]} ${left} ${right}`, lines);
    if (op === ts.SyntaxKind.SlashToken) return this.bind(`Js.bdiv ${left} ${right}`, lines);
    if (op === ts.SyntaxKind.PercentToken) return this.bind(`Js.brem ${left} ${right}`, lines);
    const symbol = { [ts.SyntaxKind.PlusToken]: "+", [ts.SyntaxKind.MinusToken]: "-", [ts.SyntaxKind.AsteriskToken]: "*" }[op];
    return `(${left} ${symbol} ${right})`;
  }

  bind(text, lines) {
    const fresh = this.fresh();
    lines.push(`let ${fresh} ← ${text}`);
    return fresh;
  }

  numeric(node, env, lines) {
    if (!this.isNumber(node)) throw this.t.fail(node, "only `number` operands are supported here");
    return this.expression(node, env, lines);
  }

  // A string literal, as code units when it can't be written in Lean source.
  text(value) {
    return leanString(value);
  }

  template(node, env, lines) {
    const parts = [this.text(node.head.text)];
    for (const span of node.templateSpans) {
      parts.push(this.toText(span.expression, env, lines), this.text(span.literal.text));
    }
    return `(${parts.join(" ++ ")})`;
  }

  // How a value prints inside a template.
  toText(node, env, lines) {
    const type = this.typeOf(node);
    const missing = this.nothing(type);
    if (missing === "both") throw this.t.fail(node, "a value that may be `null` or `undefined` can't go in a template, because it isn't known which word prints");
    const show = this.printer(this.checker.getNonNullableType(this.storedType(node)), type, node);
    const value = this.expression(node, env, lines);
    if (missing) return `(Js.show${missing === "null" ? "Null" : "Undef"} ${show ?? "id"} ${value})`;
    return show ? `(${show} ${value})` : value;
  }

  // The Lean function that prints a value of `stored`, or nothing for a string.
  // `type` is what the value narrowed to, which can be a union of literals.
  printer(stored, type, node) {
    const lean = this.leanOf(stored, node);
    if (lean?.startsWith("_root_.") && this.t.shape(stored)?.kind === "enum") return `${lean}.toJsStr`;
    const plain = this.leanOf(this.checker.getNonNullableType(type), node);
    switch (plain) {
      case "Js.Str": return undefined;
      case "Js.Num": return "Js.numStr";
      case "Int": return "Js.intStr";
      case "Bool": return "Js.boolStr";
      default: throw this.t.fail(node, "only strings, numbers, booleans and their optional forms can go in a template for now");
    }
  }

  identifier(node, env) {
    if (node.text === "undefined") return "none";
    const symbol = this.symbol(node);
    const declaration = symbol?.valueDeclaration;
    if (!declaration) throw this.t.fail(node, `\`${node.text}\` is not declared in the translated code`);
    if (this.isModuleLevel(declaration)) {
      const constant = this.t.declareConstant(declaration);
      return constant.pure ? `_root_.${constant.lean}` : this.bind(`_root_.${constant.lean}`, this.lines);
    }
    if (ts.isFunctionDeclaration(declaration)) throw this.t.fail(node, "functions as values are not supported yet");
    // A nullable variable read as non-null relies on narrowing the translator
    // didn't follow; the value would have the wrong Lean type.
    if (this.nullable(this.declaredType(symbol, node)) && !this.nullable(this.typeOf(node)) && !env.get(symbol)?.present) {
      throw this.t.fail(node, "this kind of null check is not supported yet");
    }
    return this.current(symbol, env);
  }

  isModuleLevel(declaration) {
    let node = declaration;
    while (node && !ts.isFunctionLike(node) && !ts.isSourceFile(node)) node = node.parent;
    return ts.isSourceFile(node);
  }

  property(node, env, lines) {
    const object = unwrap(node.expression);
    const known = env.get(this.fieldKey(node));
    if (known) return known.lean;
    if (ts.isIdentifier(object) && object.text === "Number" && !this.isLocal(object)) {
      if (node.name.text === "MAX_SAFE_INTEGER") return this.t.number(Number.MAX_SAFE_INTEGER, node);
      if (node.name.text === "MIN_SAFE_INTEGER") return this.t.number(Number.MIN_SAFE_INTEGER, node);
      throw this.t.fail(node, `\`Number.${node.name.text}\` is not supported`);
    }
    const state = ts.isIdentifier(object) ? env.get(this.symbol(object)) : undefined;
    if (state?.bound) {
      const bound = state.bound.get(node.name.text);
      if (!bound) throw this.t.fail(node, "this field isn't available in this case");
      return bound;
    }
    if (node.questionDotToken || ts.isOptionalChain(node)) return this.optionalField(node, object, env, lines);
    if (this.nullable(this.typeOf(object))) {
      // Compiled without index checks: a missing object stops the model.
      const value = this.expression(object, env, lines);
      const bare = this.checker.getNonNullableType(this.typeOf(object));
      const unwrapped = this.bind(`Js.unwrap ${value}`, lines);
      if (node.name.text === "length" && (bare.flags & ts.TypeFlags.StringLike || this.checker.isArrayType(bare))) return this.bind(`Js.len ${unwrapped}`, lines);
      return `${unwrapped}.${name(node.name.text)}`;
    }
    if (this.isString(object) && node.name.text === "length") return this.bind(`Js.len ${this.expression(object, env, lines)}`, lines);
    if (this.isCollection(object) && node.name.text === "size") return this.bind(`Js.len ${this.expression(object, env, lines)}`, lines);
    if (this.isArray(object) && node.name.text === "length") return this.bind(`Js.len ${this.expression(object, env, lines)}`, lines);
    if (this.isArray(object)) throw this.t.fail(node, `\`.${node.name.text}\` is not supported on arrays yet`);
    const type = this.typeOf(object);
    if (type.isUnion()) throw this.t.fail(node, "reading a field of a union outside a `switch` is not supported yet");
    const read = `${this.expression(object, env, lines)}.${name(node.name.text)}`;
    // tsc narrowed the field here, as in `o.x !== null && o.x > 1`, but the record still holds an Option.
    const field = this.checker.getPropertyOfType(this.checker.getApparentType(type), node.name.text);
    if (field && this.nullable(this.checker.getTypeOfSymbol(field)) && !this.nullable(this.typeOf(node))) return this.bind(`Js.unwrap ${read}`, lines);
    return read;
  }

  optionalField(node, object, env, lines) {
    if (!this.nullable(this.typeOf(object))) return this.expression(ts.factory.createPropertyAccessExpression(object, node.name), env, lines);
    const value = this.expression(object, env, lines);
    const field = name(node.name.text);
    const inner = this.checker.getNonNullableType(this.typeOf(object));
    const property = this.checker.getPropertyOfType(inner, node.name.text);
    const array = this.checker.isArrayType(inner) || inner.flags & ts.TypeFlags.StringLike;
    if (array && node.name.text === "length") {
      const fresh = this.fresh();
      lines.push(`let ${fresh} ← match ${value} with`, "  | some item => do", "    let size ← Js.len item", "    Result.ok (some size)",
        "  | none => Result.ok none");
      return fresh;
    }
    const declaration = property?.valueDeclaration;
    if (!declaration || array || this.t.program.isSourceFileDefaultLibrary(declaration.getSourceFile())) {
      throw this.t.fail(node, "`?.` is only supported on fields for now");
    }
    const slot = this.checker.getTypeOfSymbolAtLocation(property, property.valueDeclaration);
    const flat = this.nullable(slot) || property.flags & ts.SymbolFlags.Optional;
    return flat ? `(Option.bind ${value} (fun item => item.${field}))` : `(Option.map (fun item => item.${field}) ${value})`;
  }

  // `a ?? b`: `b` only runs when `a` is null or undefined.
  nullish(node, env, lines, target) {
    const left = this.expression(node.left, env, lines);
    const type = target ?? this.typeOf(node);
    const inner = [];
    const fallback = this.convert(node.right, type, env, inner);
    const present = this.nullable(type) ? "some value" : "value";
    const fresh = this.fresh();
    lines.push(`let ${fresh} ← match ${left} with`, `  | some value => Result.ok (${present})`, "  | none => do",
      ...inner.map(l => `    ${l}`), `    Result.ok ${fallback}`);
    return fresh;
  }

  isLocal(node) {
    const declaration = this.symbol(node)?.valueDeclaration;
    return Boolean(declaration) && !this.t.program.isSourceFileDefaultLibrary(declaration.getSourceFile());
  }

  nonNull(node, env, lines) {
    const inner = this.expression(node.expression, env, lines);
    return this.nullable(this.typeOf(node.expression)) ? this.bind(`Js.unwrap ${inner}`, lines) : inner;
  }

  ternary(node, env, lines, target) {
    const narrowed = this.narrowing(node.condition, env);
    const type = target ?? this.typeOf(node);
    const branch = (expression, branchEnv) => {
      const inner = [];
      const value = this.convert(expression, type, branchEnv, inner);
      return [...inner, `Result.ok ${value}`];
    };
    const fresh = this.fresh();
    if (narrowed) {
      const arms = narrowed((onPath, next) => branch(onPath ? node.whenTrue : node.whenFalse, next));
      lines.push(`let ${fresh} ← do`, ...this.indent(arms));
      return fresh;
    }
    const test = this.condition(node.condition, env, lines);
    lines.push(`let ${fresh} ← if ${test} then`, ...this.indent(this.indent(branch(node.whenTrue, env))),
      "  else", ...this.indent(this.indent(branch(node.whenFalse, env))));
    return fresh;
  }

  call(node, env, lines) {
    const callee = unwrap(node.expression);
    if (node.questionDotToken) throw this.t.fail(node, "optional calls are not supported yet");
    if (ts.isOptionalChain(node)) {
      const chained = this.optionalChain(node, env, lines);
      if (chained) return chained;
    }
    if (ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression) && callee.expression.text === "Math" && !this.isLocal(callee.expression)) {
      return this.math(callee.name.text, node, env, lines);
    }
    const builtin = this.builtin(callee, node, env, lines);
    if (builtin) return builtin;
    if (ts.isPropertyAccessExpression(callee) && this.isArray(callee.expression)) return this.arrayMethod(callee, node, env, lines);
    if (ts.isPropertyAccessExpression(callee) && this.isString(callee.expression)) return this.stringMethod(callee, node, env, lines);
    if (ts.isPropertyAccessExpression(callee) && this.isCollection(callee.expression)) return this.collectionMethod(callee, node, env, lines);
    if (ts.isIdentifier(callee) && callee.text === "String" && !this.isLocal(callee) && node.arguments.length === 1) {
      return this.toText(node.arguments[0], env, lines);
    }
    const signature = this.checker.getResolvedSignature(node);
    const outside = this.outsideName(callee);
    if (outside && this.t.assumes.has(outside)) return this.assumedCall(outside, signature, node, env, lines);
    let declaration = signature?.declaration;
    if (declaration && !ts.isFunctionDeclaration(declaration)) declaration = declaration.parent;
    declaration = this.t.resolve(declaration);
    if (!declaration) throw this.t.fail(node, "this call isn't to a function the translator can see");
    if (declaration.getSourceFile().isDeclarationFile) throw this.t.fail(node, "this function has no source in the package");
    const lean = this.t.declareFunction(declaration);
    this.t.noteAssumed(this.t.assumedBy.get(declaration) ?? []);
    const parameters = signature.getParameters();
    if (node.arguments.length > parameters.length) throw this.t.fail(node, "too many arguments");
    const args = parameters.map((parameter, index) => {
      const site = parameter.valueDeclaration;
      const hasDefault = Boolean(site.initializer);
      const argument = node.arguments[index];
      if (!argument) {
        if (!hasDefault && !site.questionToken) throw this.t.fail(node, "a missing argument");
        return "none";
      }
      const slot = this.checker.getTypeAtLocation(site);
      const value = this.convert(argument, slot, env, lines);
      return hasDefault ? `(some ${value})` : value;
    });
    // A function can't name itself through `_root_` while it is being defined.
    const callee_ = this.t.functions.get(declaration)?.pending ? lean : `_root_.${lean}`;
    return this.bind(`${callee_} ${args.join(" ")}`, lines);
  }

  arrayMethod(callee, node, env, lines) {
    const method = callee.name.text;
    if (MUTATING.has(method)) throw this.t.fail(node, `\`${method}\` is only supported as its own statement, and its result can't be used yet`);
    const list = this.expression(callee.expression, env, lines);
    const args = node.arguments;
    const item = this.checker.getTypeArguments(this.checker.getApparentType(this.typeOf(callee.expression)))[0];
    const comparable = () => {
      if (item.flags & ts.TypeFlags.Object) throw this.t.fail(node, `\`${method}\` on objects compares identity, which is not supported`);
    };
    switch (method) {
      case "includes": comparable(); return `(Js.includes ${list} ${this.convert(args[0], item, env, lines)})`;
      case "indexOf": comparable(); return this.bind(`Js.indexOf ${list} ${this.convert(args[0], item, env, lines)}`, lines);
      case "slice":
        if (args.length === 0) return list;
        if (args.length === 1) return `(Js.sliceFrom ${list} ${this.numeric(args[0], env, lines)})`;
        return `(Js.slice ${list} ${this.numeric(args[0], env, lines)} ${this.numeric(args[1], env, lines)})`;
      case "join": {
        if (!(item.flags & ts.TypeFlags.StringLike)) throw this.t.fail(node, "`join` is only supported on strings for now");
        return `(Js.join ${list} ${args[0] ? this.expression(args[0], env, lines) : this.text(",")})`;
      }
      case "concat":
        if (args.length !== 1 || !this.isArray(args[0])) throw this.t.fail(node, "only `concat` of one array is supported for now");
        return `(${list} ++ ${this.expression(args[0], env, lines)})`;
      case "map": case "filter": case "some": case "every": case "find": {
        const result = this.bindCallback(method === "some" ? "some_" : method, this.callback(args, 1, node, env), list, lines);
        if (method !== "filter" || !this.nullable(item)) return result;
        // A type guard removed the nullish values, so the result holds plain values.
        const kept = this.checker.getTypeArguments(this.checker.getApparentType(this.typeOf(node)))[0];
        return this.nullable(kept) ? result : this.bind(`Js.unwrapAll ${result}`, lines);
      }
      case "reduce": {
        if (args.length !== 2) throw this.t.fail(node, "`reduce` needs an initial value");
        const signature = this.checker.getResolvedSignature(node);
        const start = this.convert(args[1], signature.getReturnType(), env, lines);
        return this.bindCallback("reduce", this.callback(args, 2, node, env), `${start} ${list}`, lines);
      }
      default: throw this.t.fail(node, `\`.${method}\` is not supported on arrays yet`);
    }
  }

  stringMethod(callee, node, env, lines) {
    return this.stringCall(this.expression(callee.expression, env, lines), callee.name.text, node, env, lines);
  }

  // `x?.trim().toLowerCase()` on an optional string. A missing `x` skips the whole
  // chain, arguments included, so everything after `?.` runs inside the `some` arm.
  optionalChain(node, env, lines) {
    const links = [];
    for (let at = node; ts.isCallExpression(at) && ts.isPropertyAccessExpression(unwrap(at.expression)); at = unwrap(unwrap(at.expression).expression)) {
      links.unshift(at);
      if (unwrap(at.expression).questionDotToken) break;
    }
    const first = links[0] && unwrap(links[0].expression);
    if (!first?.questionDotToken || links.at(-1) !== node) return undefined;
    const base = unwrap(first.expression);
    const type = this.typeOf(base);
    if (!this.nullable(type) || this.leanOf(this.checker.getNonNullableType(type), base) !== "Js.Str") return undefined;
    if (!ts.isIdentifier(base) && !this.isFieldPath(base)) throw this.t.fail(node, "`?.` on an expression is not supported yet");
    const present = this.fresh(), arm = [];
    let value = present;
    for (const link of links) value = this.stringCall(value, unwrap(link.expression).name.text, link, env, arm);
    const fresh = this.fresh();
    lines.push(`let ${fresh} ← match ${this.expression(base, env, lines)} with`, `  | some ${present} => do`,
      ...arm.map(line => `    ${line}`), `    Result.ok (some ${value})`, "  | none => Result.ok none");
    return fresh;
  }

  stringCall(value, method, node, env, lines) {
    const args = node.arguments;
    const text = index => {
      if (!args[index] || !this.isString(args[index])) throw this.t.fail(node, `\`${method}\` is only supported with a string here, because it would otherwise take a regular expression`);
      return this.expression(args[index], env, lines);
    };
    const count = index => this.numeric(args[index], env, lines);
    const none = () => { if (args.length) throw this.t.fail(node, `\`${method}\` with arguments is not supported yet`); };
    const exactly = n => { if (args.length !== n) throw this.t.fail(node, `\`${method}\` with these arguments is not supported yet`); };
    switch (method) {
      case "charAt": exactly(1); return `(Js.charAt ${value} ${count(0)})`;
      case "slice":
        if (args.length === 1) return `(Js.sliceFrom ${value} ${count(0)})`;
        exactly(2); return `(Js.slice ${value} ${count(0)} ${count(1)})`;
      case "substring": exactly(2); return `(Js.substring ${value} ${count(0)} ${count(1)})`;
      case "startsWith": exactly(1); return `(Js.startsWith ${value} ${text(0)})`;
      case "endsWith": exactly(1); return `(Js.endsWith ${value} ${text(0)})`;
      case "includes": exactly(1); return `(Js.strIncludes ${value} ${text(0)})`;
      case "indexOf": exactly(1); return this.bind(`Js.strIndexOf ${value} ${text(0)}`, lines);
      case "lastIndexOf": exactly(1); return this.bind(`Js.strLastIndexOf ${value} ${text(0)}`, lines);
      case "charCodeAt": exactly(1); return this.bind(`Js.charCodeAt ${value} ${count(0)}`, lines);
      case "trim": none(); return `(Js.trim ${value})`;
      case "trimStart": none(); return `(Js.trimStart ${value})`;
      case "trimEnd": none(); return `(Js.trimEnd ${value})`;
      case "toLowerCase": none(); return this.bind(`Js.toLower ${value}`, lines);
      case "toUpperCase": none(); return this.bind(`Js.toUpper ${value}`, lines);
      case "toString": none(); return value;
      case "split": exactly(1); return `(Js.split ${value} ${text(0)})`;
      case "replace": exactly(2); return this.bind(`Js.replace ${value} ${text(0)} ${text(1)}`, lines);
      case "replaceAll": exactly(2); return this.bind(`Js.replaceAll ${value} ${text(0)} ${text(1)}`, lines);
      case "concat": exactly(1); return `(${value} ++ ${text(0)})`;
      default: throw this.t.fail(node, `\`.${method}\` is not supported on strings yet`);
    }
  }

  collectionMethod(callee, node, env, lines) {
    const method = callee.name.text;
    if (MUTATING.has(method)) throw this.t.fail(node, `\`${method}\` is only supported as its own statement, and its result can't be used yet`);
    const value = this.expression(callee.expression, env, lines);
    const { kind, args: types } = this.t.collection(this.typeOf(callee.expression));
    const key = () => this.convert(node.arguments[0], types[0], env, lines);
    if (kind === "Map" && method === "get") return `(Js.dictGet ${value} ${key()})`;
    if (kind === "Map" && method === "has") return `(Js.dictHas ${value} ${key()})`;
    if (kind === "Set" && method === "has") return `(Js.setHas ${value} ${key()})`;
    throw this.t.fail(node, `\`.${method}\` is not supported here yet`);
  }

  // Functions on numbers that JavaScript provides.
  builtin(callee, node, env, lines) {
    const args = node.arguments;
    const global = ts.isIdentifier(callee) && !this.isLocal(callee);
    const onNumber = ts.isPropertyAccessExpression(callee) && !callee.questionDotToken
      && ts.isIdentifier(callee.expression) && callee.expression.text === "Number" && !this.isLocal(callee.expression);
    const named = global ? callee.text : onNumber ? `Number.${callee.name.text}` : undefined;
    const test = name => (this.isNumber(args[0]) ? `(Js.${name} ${this.expression(args[0], env, lines)})` : undefined);
    if (args.length === 1) {
      switch (named) {
        case "Number.isFinite": case "Number.isInteger": case "Number.isSafeInteger":
          if (this.nullable(this.typeOf(args[0])) && this.isOptionalNumber(args[0])) return `(Option.isSome ${this.expression(args[0], env, lines)})`;
          return test("isFinite");
        case "isFinite": return test("isFinite");
        case "isNaN": case "Number.isNaN": return test("isNaN");
        case "Boolean": return `(decide (¬¬(${this.condition(args[0], env, lines)})))`;
        default:
      }
    }
    if ((named === "parseInt" || named === "Number.parseInt") && this.isString(args[0])) {
      if (args.length === 1) return this.bind(`Js.parseIntStr true ${this.expression(args[0], env, lines)}`, lines);
      const radix = args.length === 2 && unwrap(args[1]);
      if (radix && ts.isNumericLiteral(radix) && radix.text === "10") return this.bind(`Js.parseIntStr false ${this.expression(args[0], env, lines)}`, lines);
    }
    if (ts.isPropertyAccessExpression(callee) && !callee.questionDotToken) {
      const receiver = callee.expression, method = callee.name.text;
      if (method === "toFixed" && this.isNumber(receiver) && !this.nullable(this.typeOf(receiver))) {
        const value = this.expression(receiver, env, lines);
        if (!args.length) return `(Js.numStr ${value})`;
        if (args.length === 1) return this.bind(`Js.toFixed ${value} ${this.numeric(args[0], env, lines)}`, lines);
      }
      if (method === "toString" && !args.length && !this.nullable(this.typeOf(receiver))) {
        if (this.isNumber(receiver)) return `(Js.numStr ${this.expression(receiver, env, lines)})`;
        if (this.isBigInt(receiver)) return `(Js.intStr ${this.expression(receiver, env, lines)})`;
        if (this.isBoolean(receiver)) return `(Js.boolStr ${this.expression(receiver, env, lines)})`;
      }
    }
    return undefined;
  }

  isOptionalNumber(node) {
    const type = this.typeOf(node);
    return this.nothing(type) !== undefined && this.leanOf(this.checker.getNonNullableType(type), node) === "Js.Num";
  }

  // `kebabCase` imported from "lodash" is `lodash::kebabCase`. Relative imports are this code.
  outsideName(callee) {
    if (!ts.isIdentifier(callee)) return undefined;
    const site = this.checker.getSymbolAtLocation(callee)?.declarations?.[0];
    if (!site || !ts.isImportSpecifier(site)) return undefined;
    const module = site.parent.parent.parent.moduleSpecifier.text;
    return module.startsWith(".") ? undefined : `${module}::${(site.propertyName ?? site.name).text}`;
  }

  assumedCall(key, signature, node, env, lines) {
    const site = signature.declaration;
    if (signature.typeParameters?.length || signature.target || site?.typeParameters?.length) throw this.t.fail(node, `\`${key}\` is generic, so it can't be assumed yet`);
    const listed = this.t.assumes.get(key);
    const found = this.checker.signatureToString(signature);
    const plain = text => text.replace(/\s+/g, " ").trim();
    // Listing the signature keeps it under the protected policy: the type a proof
    // relies on can't change through the code or through a package upgrade.
    if (plain(found) !== plain(listed)) throw this.t.fail(node, `\`${key}\` has the signature \`${found}\`, but \`assumes\` lists \`${listed}\``);
    if (site?.parameters.some(p => p.dotDotDotToken)) throw this.t.fail(node, `\`${key}\` takes a rest parameter, so it can't be assumed yet`);
    const parameters = signature.getParameters();
    // Assuming a call means the same arguments give the same result, which a
    // function of nothing could only satisfy by being a constant.
    if (!parameters.length) throw this.t.fail(node, `\`${key}\` takes no arguments, so it can't be a function of its inputs`);
    if (node.arguments.length > parameters.length) throw this.t.fail(node, "too many arguments");
    const lean = this.t.declareAssumed(key, signature, node);
    const args = parameters.map((parameter, index) => {
      const argument = node.arguments[index];
      if (argument) return this.convert(argument, this.checker.getTypeOfSymbolAtLocation(parameter, node), env, lines);
      if (!site.parameters[index].questionToken) throw this.t.fail(node, "a missing argument");
      return "none";
    });
    this.t.noteAssumed([key]);
    return this.bind(`_root_.${lean} ${args.join(" ")}`, lines);
  }

  bindCallback(method, callback, rest, lines) {
    const fresh = this.fresh();
    lines.push(`let ${fresh} ← Js.${method} (${callback[0]}`, ...callback.slice(1), `  ) ${rest}`);
    return fresh;
  }

  // An inline function, as lines of a Lean `fun`. JavaScript also passes the
  // index and the array, so taking more parameters than `count` isn't supported.
  callback(args, count, node, env) {
    const fn = args[0] && unwrap(args[0]);
    if (!fn || !(ts.isArrowFunction(fn) || ts.isFunctionExpression(fn))) throw this.t.fail(node, "only an inline function is supported here for now");
    if (fn.parameters.length !== count) throw this.t.fail(fn, `this function must take exactly ${count} parameter${count === 1 ? "" : "s"} for now`);
    if (fn.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) throw this.t.fail(fn, "`async` is not supported yet");
    const inner = new Map(env);
    const params = fn.parameters.map(p => {
      if (!ts.isIdentifier(p.name) || p.initializer || p.dotDotDotToken) throw this.t.fail(p, "only plain parameters are supported for now");
      const lean = this.rebind(this.symbol(p.name), inner);
      return `(${lean} : ${this.t.type(this.checker.getTypeAtLocation(p), p)})`;
    });
    const signature = this.checker.getSignatureFromDeclaration(fn);
    const returns = this.checker.getReturnTypeOfSignature(signature);
    const flow = this.functionFlow(returns, this.t.type(returns, fn));
    const body = ts.isBlock(fn.body) ? this.block([...fn.body.statements], flow, inner) : this.returning(fn.body, flow, inner);
    return [`fun ${params.join(" ")} => do`, ...this.indent(this.indent(body))];
  }

  math(method, node, env, lines) {
    const args = node.arguments.map(unwrap);
    if (ROUNDING[method] && args.length === 1) {
      const inner = args[0];
      if (ts.isBinaryExpression(inner) && inner.operatorToken.kind === ts.SyntaxKind.SlashToken) {
        const left = this.numeric(inner.left, env, lines);
        const right = this.numeric(inner.right, env, lines);
        return this.bind(`Js.${ROUNDING[method]} ${left} ${right}`, lines);
      }
      return this.numeric(inner, env, lines); // already a safe integer
    }
    if (method === "abs" && args.length === 1) return `(Js.abs ${this.numeric(args[0], env, lines)})`;
    if ((method === "min" || method === "max") && args.length === 2) {
      const left = this.numeric(args[0], env, lines);
      return `(Js.${method} ${left} ${this.numeric(args[1], env, lines)})`;
    }
    throw this.t.fail(node, `\`Math.${method}\` is not supported`);
  }

  // The integer a number expression evaluates to.
  valueOf(node, env, lines) {
    const literal = this.t.literal(node);
    if (literal !== undefined) {
      this.t.number(literal, node);
      return literal < 0 ? `(${literal})` : `${literal}`;
    }
    return `${this.numeric(node, env, lines)}.val`;
  }

  // A Lean proposition for a boolean expression.
  condition(node, env, lines) {
    node = unwrap(node);
    if (ts.isPrefixUnaryExpression(node) && node.operator === ts.SyntaxKind.ExclamationToken) {
      return `¬(${this.condition(node.operand, env, lines)})`;
    }
    if (ts.isBinaryExpression(node)) {
      const op = node.operatorToken.kind;
      if (ORDER[op]) {
        if (this.isString(node.left) && this.isString(node.right)) {
          const a = this.expression(node.left, env, lines), b = this.expression(node.right, env, lines);
          const swap = op === ts.SyntaxKind.GreaterThanToken || op === ts.SyntaxKind.LessThanEqualsToken;
          const lt = `Js.strLt ${swap ? b : a} ${swap ? a : b} = true`;
          return op === ts.SyntaxKind.LessThanToken || op === ts.SyntaxKind.GreaterThanToken ? lt : `¬(${lt})`;
        }
        if (this.isBigInt(node.left) && this.isBigInt(node.right)) {
          return `${this.expression(node.left, env, lines)} ${ORDER[op]} ${this.expression(node.right, env, lines)}`;
        }
        return `${this.valueOf(node.left, env, lines)} ${ORDER[op]} ${this.valueOf(node.right, env, lines)}`;
      }
      if (op === ts.SyntaxKind.AmpersandAmpersandToken || op === ts.SyntaxKind.BarBarToken) return this.logical(node, env, lines);
      if (op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsEqualsToken) {
        const test = this.equality(node, env, lines);
        return op === ts.SyntaxKind.EqualsEqualsEqualsToken ? test : `¬(${test})`;
      }
      // Loose equality only means something simple against `null`.
      if ((op === ts.SyntaxKind.EqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken)
        && unwrap(node.right).kind === ts.SyntaxKind.NullKeyword) {
        const test = this.missing(node, env, lines);
        return op === ts.SyntaxKind.EqualsEqualsToken ? test : `¬(${test})`;
      }
      throw this.t.fail(node, "this operator is not supported");
    }
    if (this.isString(node)) return `${this.expression(node, env, lines)} ≠ []`;
    if (this.isNumber(node)) return `${this.expression(node, env, lines)}.val ≠ 0`; // NaN never reaches here
    if (this.isBigInt(node)) return `${this.expression(node, env, lines)} ≠ 0`;
    if (this.isBoolean(node)) return `${this.expression(node, env, lines)} = true`;
    const type = this.typeOf(node);
    if (type.isUnion() && this.nullable(type)) return this.present(this.expression(node, env, lines), this.checker.getNonNullableType(type), node);
    if (this.alwaysTruthy(type, node)) throw this.t.fail(node, "this value is always truthy, so the test does nothing");
    throw this.t.fail(node, "truthiness of this type is not supported yet");
  }

  // Objects, arrays and enumerations are truthy whatever they hold: no tag is empty.
  alwaysTruthy(type, node) {
    const lean = this.leanOf(type, node);
    if (!lean || ["Js.Num", "Js.Str", "Bool", "Int", "Unit"].includes(lean)) return false;
    return !type.isUnion() || !this.nullable(type);
  }

  // A test on an optional value, by what its inner value's truth depends on.
  present(value, inner, node) {
    const lean = this.leanOf(inner, node);
    if (lean === "Js.Str") return `Js.truthyStr ${value} = true`;
    if (lean === "Js.Num") return `Js.truthyNum ${value} = true`;
    if (lean === "Bool") return `Js.truthyBool ${value} = true`;
    if (lean === "Int") return `Js.truthyBig ${value} = true`;
    if (this.alwaysTruthy(inner, node)) return `Option.isSome ${value} = true`;
    throw this.t.fail(node, "truthiness of this type is not supported yet");
  }

  // `x == null`, or `x === null` where the type allows only that nullish value.
  missing(node, env, lines) {
    const operand = unwrap(node.left);
    if (!this.isNull(unwrap(node.right))) throw this.t.fail(node, "the nullish value must be on the right here for now");
    const type = this.typeOf(operand);
    const kind = this.nothing(type);
    if (!kind) throw this.t.fail(node, "this kind of null check is not supported yet");
    const strict = node.operatorToken.kind === ts.SyntaxKind.EqualsEqualsEqualsToken || node.operatorToken.kind === ts.SyntaxKind.ExclamationEqualsEqualsToken;
    const wanted = this.isUndefined(unwrap(node.right)) ? "undefined" : "null";
    if (strict && kind === "both") throw this.t.fail(node, "`===` can't tell `null` from `undefined` here; use `== null`");
    if (strict && kind !== wanted) throw this.t.fail(node, "this null check is always false, because the type allows the other nullish value");
    return `Option.isNone ${this.expression(operand, env, lines)} = true`;
  }

  // `&&` and `||` as a test only ask whether the result is truthy, whatever the sides are.
  logical(node, env, lines) {
    if (this.splits(node)) {
      const fresh = this.fresh();
      lines.push(`let ${fresh} ← do`, ...this.indent(this.splitTest(node, env, onPath => [`Result.ok ${onPath}`])));
      return `${fresh} = true`;
    }
    const and = node.operatorToken.kind === ts.SyntaxKind.AmpersandAmpersandToken;
    const left = this.condition(node.left, env, lines);
    const inner = [];
    const right = this.condition(node.right, env, inner);
    if (!inner.length) return `(${left}) ${and ? "∧" : "∨"} (${right})`;
    // The right side only runs when the left side doesn't decide the result.
    const fresh = this.fresh();
    const rest = this.indent(this.indent([...inner, `Result.ok (decide (${right}))`]));
    const short = `Result.ok ${and ? "false" : "true"}`;
    lines.push(`let ${fresh} ← if ${left} then`, ...(and ? rest : [`    ${short}`]),
      "  else", ...(and ? [`    ${short}`] : rest));
    return `${fresh} = true`;
  }

  equality(node, env, lines) {
    const left = unwrap(node.left), right = unwrap(node.right);
    if (this.isNull(left) || this.isNull(right)) return this.missing(node, env, lines);
    if (this.isNumber(left) && this.isNumber(right)) {
      return `${this.valueOf(left, env, lines)} = ${this.valueOf(right, env, lines)}`;
    }
    if ((this.isBoolean(left) && this.isBoolean(right)) || (this.isBigInt(left) && this.isBigInt(right))) {
      return `${this.expression(left, env, lines)} = ${this.expression(right, env, lines)}`;
    }
    // `undefined === 5` is false, so a possibly missing number compares as an Option.
    for (const [maybe, plain] of [[left, right], [right, left]]) {
      if (this.nullable(this.typeOf(maybe)) && this.isNumber(plain)) {
        return `${this.expression(maybe, env, lines)} = some ${this.expression(plain, env, lines)}`;
      }
    }
    const literal = [left, right].find(ts.isStringLiteralLike);
    const other = left === literal ? right : left;
    const otherType = this.narrowedType(other, env);
    if (literal && this.nullable(otherType)) {
      const plain = this.t.type(this.checker.getNonNullableType(this.storedType(other)), other) === "Js.Str";
      return `${this.expression(other, env, lines)} = some ${plain ? this.text(literal.text) : `.${name(literal.text)}`}`;
    }
    if (literal && this.t.type(this.checker.getNonNullableType(this.storedType(other)), other) !== "Js.Str") {
      return `${this.expression(other, env, lines)} = .${name(literal.text)}`;
    }
    if (this.isText(left) && this.isText(right)) {
      return `${this.expression(left, env, lines)} = ${this.expression(right, env, lines)}`;
    }
    const leftType = this.typeOf(left), rightType = this.typeOf(right);
    const inner = type => (this.nullable(type) ? this.checker.getNonNullableType(type) : type);
    const same = this.leanOf(inner(leftType), left);
    const comparable = same && same === this.leanOf(inner(rightType), right) && same !== "Js.Num"
      && (same === "Js.Str" || same === "Bool" || same === "Int" || (same.startsWith("_root_.") && this.t.shape(inner(leftType))?.kind === "enum"));
    if (comparable) {
      const a = this.expression(left, env, lines), b = this.expression(right, env, lines);
      const [leftKind, rightKind] = [this.nothing(leftType), this.nothing(rightType)];
      if (!leftKind && !rightKind) return `${a} = ${b}`;
      if (leftKind && !rightKind) return `${a} = some ${b}`;
      if (rightKind && !leftKind) return `${b} = some ${a}`;
      // Two missing values are only equal if they are the same nullish value.
      if (leftKind === rightKind && leftKind !== "both") return `${a} = ${b}`;
    }
    throw this.t.fail(node, "`===` is only supported on numbers, booleans and string-literal unions for now");
  }
}

function leanString(value) {
  if (/^[\x20-\x21\x23-\x5b\x5d-\x7e]*$/.test(value)) return `(js!"${value}")`;
  const units = Array.from({ length: value.length }, (_, i) => value.charCodeAt(i));
  return `([${units.join(", ")}] : Js.Str)`;
}

export function findDeclaration(translator, target) {
  const [path, functionName] = target.split("::");
  const file = translator.program.getSourceFile(join(translator.root, path));
  if (!file) throw new Unsupported(`${path} does not exist`);
  for (const statement of file.statements) {
    if (ts.isFunctionDeclaration(statement) && statement.name?.text === functionName) return statement;
    if (ts.isVariableStatement(statement)) {
      for (const declaration of statement.declarationList.declarations) {
        if (ts.isIdentifier(declaration.name) && declaration.name.text === functionName && translator.bodyOf(declaration)) return declaration;
      }
    }
  }
  throw new Unsupported(`\`${functionName}\` is not a top-level function in ${path}`);
}

export function translate({ root, module, targets, paths, repository, policyRoot, requireTypes, assumes }) {
  const resolved = policyRoot ? protectedPaths(policyRoot, repository) : paths;
  const translator = new Translator(root, targets, resolved, repository, assumes);
  translator.requireTypes = Boolean(requireTypes);
  const failures = {};
  const names = {};
  const signatures = {};
  const assumed = {};
  let fatal = null;
  for (const target of targets) {
    const snapshot = {
      order: translator.order.length, types: new Map(translator.types),
      functions: new Map(translator.functions), constants: new Map(translator.constants),
      assumed: new Map(translator.assumed),
    };
    let declaration;
    try {
      declaration = findDeclaration(translator, target);
      names[target] = translator.declareFunction(declaration);
      signatures[target] = translator.signature(declaration);
      assumed[target] = [...translator.assumedBy.get(declaration) ?? []].sort();
    } catch (error) {
      if (!(error instanceof Unsupported)) throw error;
      failures[target] = error.message;
      translator.order.length = snapshot.order;
      translator.types = snapshot.types;
      translator.functions = snapshot.functions;
      translator.assumed = snapshot.assumed;
      translator.constants = snapshot.constants;
      try {
        if (declaration) names[target] = translator.stub(declaration);
      } catch (stubError) {
        if (!(stubError instanceof Unsupported)) throw stubError;
        fatal = stubError.message;
      }
    }
  }
  const header = ["import Aeneas", "import ProofciJs", "", "open Aeneas Aeneas.Std Result", ""];
  const reached = [...translator.fileChecks.keys()];
  const packages = Object.fromEntries([...translator.packages.values()].filter(Boolean).map(p => [p.name, p.version]));
  const local = file => relative(translator.root, realpathSync(file));
  // Records can be used only inside a constant or a callback, so no signature shows them.
  const records = () => translator.shaped.flatMap(({ type, node }) => {
    try { return [translator.describe(type, node)]; } catch { return []; }
  });
  return { module, source: `${[...header, ...translator.order.flatMap(d => [d, ""])].join("\n")}\n`, failures, names, fatal, signatures, assumed, packages, records,
    files: reached.map(f => local(f.fileName)),
    imports: Object.fromEntries(reached.map(f => [local(f.fileName), imports(f, translator.program)])) };
}

// Where each import of a file leads, resolved the way the translation resolved it.
function imports(file, program) {
  const found = {};
  for (const statement of file.statements) {
    if (!statement.moduleSpecifier) continue;
    const specifier = statement.moduleSpecifier.text;
    const { resolvedModule } = ts.resolveModuleName(specifier, file.fileName, program.getCompilerOptions(), ts.sys);
    if (resolvedModule) found[specifier] = realpathSync(resolvedModule.resolvedFileName);
  }
  return found;
}

if (process.argv[1]?.endsWith("translate.mjs")) {
  const config = JSON.parse(readFileSync(process.argv[2], "utf8"));
  try {
    const { source, ...result } = translate(config);
    writeFileSync(join(config.out, `${config.module}.lean`), source);
    console.log(JSON.stringify(result));
  } catch (error) {
    if (!(error instanceof Unsupported)) throw error;
    console.log(JSON.stringify({ module: config.module, failures: Object.fromEntries(config.targets.map(t => [t, error.message])), names: {} }));
  }
}
