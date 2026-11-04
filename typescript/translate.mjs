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
import { join, relative, sep } from "node:path";
import ts from "typescript";

export class Unsupported extends Error {}

const LEAN_KEYWORDS = new Set(["at", "by", "calc", "class", "deriving", "do", "else", "end", "export", "extends",
  "fun", "from", "have", "if", "import", "in", "infix", "instance", "let", "macro", "match", "mut", "namespace",
  "notation", "of", "open", "prefix", "private", "protected", "public", "section", "set_option", "show", "structure",
  "syntax", "then", "theorem", "this", "to", "try", "universe", "unless", "using", "variable", "where", "with",
  "abbrev", "axiom", "def", "example", "fix", "for", "forall", "inductive", "lemma", "mutual", "nomatch", "opaque",
  "return", "suffices", "termination_by", "decreasing_by", "Type", "Sort", "Prop", "true", "false", "none", "some"]);

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

class Translator {
  constructor(root, targets) {
    this.root = realpathSync(root);
    this.files = [...new Set(targets.map(t => join(this.root, t.split("::")[0])))];
    for (const file of this.files) {
      if (!existsSync(file)) throw new Unsupported(`${relative(this.root, file)} does not exist`);
    }
    this.program = ts.createProgram(this.files, OPTIONS);
    this.checker = this.program.getTypeChecker();
    this.types = new Map();      // declaration -> { lean, text }
    this.functions = new Map();  // declaration -> { lean, text } (null while in progress)
    this.constants = new Map();
    this.fileChecks = new Map();
    this.order = [];
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
    if (file.isDeclarationFile || !(path === this.root || path.startsWith(this.root + sep))) {
      throw new Unsupported(`${file.fileName} is outside the translated package`);
    }
    const stem = path.replace(/\.ts$/, "");
    for (const extension of SHADOW_EXTENSIONS) {
      if (existsSync(stem + extension)) {
        throw new Unsupported(`${relative(this.root, stem + extension)} sits beside the TypeScript source, `
          + "so the program may load it instead");
      }
    }
    if (COMPILER_SWITCH.test(file.text)) {
      throw new Unsupported(`${relative(this.root, path)} turns off compiler errors with a \`@ts-\` comment`);
    }
    const problems = [...this.program.getSyntacticDiagnostics(file), ...this.program.getSemanticDiagnostics(file)];
    if (problems.length) {
      const first = problems[0];
      const where = first.file ? first.file.getLineAndCharacterOfPosition(first.start ?? 0).line + 1 : 0;
      throw new Unsupported(`${relative(this.root, path)}:${where}: TypeScript error: `
        + ts.flattenDiagnosticMessageText(first.messageText, " "));
    }
    for (const statement of file.statements) this.checkTopLevel(statement);
  }

  // Module code runs on import. Anything beyond declarations could change what
  // the translated functions do, for example by patching `Math.floor`.
  checkTopLevel(statement) {
    if (ts.isImportDeclaration(statement)) {
      if (!statement.importClause) throw this.fail(statement, "an import that exists only for its side effects");
      return;
    }
    if (ts.isVariableStatement(statement)) {
      if (!(statement.declarationList.flags & ts.NodeFlags.Const)) throw this.fail(statement, "module-level `let` or `var`");
      for (const declaration of statement.declarationList.declarations) {
        const init = declaration.initializer && unwrap(declaration.initializer);
        if (!init || !(ts.isArrowFunction(init) || ts.isFunctionExpression(init) || this.literal(init) !== undefined)) {
          throw this.fail(declaration, "module-level values must be functions or number literals for now");
        }
      }
      return;
    }
    if (ts.isFunctionDeclaration(statement) || ts.isInterfaceDeclaration(statement) || ts.isTypeAliasDeclaration(statement)
      || ts.isExportDeclaration(statement) || ts.isEmptyStatement(statement)) return;
    throw this.fail(statement, "module-level code runs on import, and only declarations are supported");
  }

  namespace(file) {
    const relativePath = relative(this.root, realpathSync(file.fileName)).replace(/\.ts$/, "");
    return relativePath.split(sep).map(part => part.replace(/-/g, "_")).map(name).join(".");
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
    if (this.checker.isArrayType(type)) return `(List ${this.type(this.checker.getTypeArguments(type)[0], node)})`;
    if (type.isUnion() && type.types.every(t => t.flags & TypeFlags.NumberLike)) return "Js.Num";
    if (type.isUnion() && type.types.every(t => t.flags & TypeFlags.BigIntLike)) return "Int";
    if (type.isUnion()) {
      const parts = type.types.filter(t => !(t.flags & (TypeFlags.Null | TypeFlags.Undefined)));
      const nulls = type.types.filter(t => t.flags & TypeFlags.Null).length;
      const undefineds = type.types.filter(t => t.flags & TypeFlags.Undefined).length;
      if (nulls + undefineds === 1) {
        const rest = parts.length === 1 ? parts[0] : this.checker.getNonNullableType(type);
        return `(Option ${this.type(rest, node)})`;
      }
      if (nulls + undefineds > 1) throw this.fail(node, "a type allowing both `null` and `undefined`");
    }
    const symbol = type.aliasSymbol ?? type.symbol;
    const declaration = symbol?.declarations?.[0];
    const library = declaration && this.program.isSourceFileDefaultLibrary(declaration.getSourceFile());
    if (declaration && !library && (ts.isInterfaceDeclaration(declaration) || ts.isTypeAliasDeclaration(declaration))) {
      return `_root_.${this.declareType(declaration, type)}`;
    }
    throw this.fail(node, `the type \`${this.checker.typeToString(type)}\` is not supported yet`);
  }

  declareType(declaration, type) {
    if (this.types.has(declaration)) {
      const known = this.types.get(declaration);
      if (!known) throw this.fail(declaration, "recursive types are not supported yet");
      return known.lean;
    }
    this.checkFile(declaration.getSourceFile());
    if (declaration.typeParameters?.length) throw this.fail(declaration, "generic types are not supported yet");
    if (declaration.heritageClauses?.length) throw this.fail(declaration, "`extends` on a type is not supported yet");
    this.types.set(declaration, null);
    const lean = this.leanName(declaration, declaration.name.text);
    let shape;
    if (type.isUnion()) shape = this.declareUnion(declaration, type, lean);
    else shape = this.declareRecord(declaration, type, lean);
    this.types.set(declaration, { lean, ...shape });
    this.order.push(shape.text);
    return lean;
  }

  fields(type, declaration) {
    if (this.checker.getIndexInfosOfType(type).length) throw this.fail(declaration, "index signatures are not supported yet");
    return this.checker.getPropertiesOfType(type).map(property => {
      const node = property.valueDeclaration;
      if (!node || !(ts.isPropertySignature(node))) throw this.fail(declaration, `\`${property.name}\` is not a plain field`);
      if (node.questionToken) throw this.fail(node, "optional fields are not supported yet");
      return { name: property.name, type: this.checker.getTypeOfSymbolAtLocation(property, node), node };
    });
  }

  declareRecord(declaration, type, lean) {
    if (!(type.flags & ts.TypeFlags.Object)) throw this.fail(declaration, "this type is not supported yet");
    const fields = this.fields(type, declaration);
    if (!fields.length) throw this.fail(declaration, "empty records are not supported");
    const lines = fields.map(f => `  ${name(f.name)} : ${this.type(f.type, f.node)}`);
    return { kind: "record", fields: fields.map(f => f.name),
      text: [`structure ${lean} where`, ...lines, "deriving DecidableEq, Repr"].join("\n") };
  }

  // A union of string literals is an enumeration. A union of records tagged by
  // a shared `kind` field is an inductive type with one constructor each.
  declareUnion(declaration, type, lean) {
    if (type.types.every(t => t.isStringLiteral())) {
      const tags = type.types.map(t => t.value);
      return { kind: "enum", tags,
        text: [`inductive ${lean} where`, ...tags.map(t => `  | ${name(t)}`), "deriving DecidableEq, Repr"].join("\n") };
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

  // A description of a type, for generating and reading values of it.
  describe(type, node) {
    const lean = this.type(type, node);
    if (lean === "Js.Num") return { kind: "number" };
    if (lean === "Bool") return { kind: "boolean" };
    if (lean === "Int") return { kind: "bigint" };
    if (lean === "Unit") return { kind: "void" };
    if (this.checker.isArrayType(type)) return { kind: "array", item: this.describe(this.checker.getTypeArguments(type)[0], node) };
    if (type.isUnion() && this.nullish(type)) {
      const nothing = type.types.some(t => t.flags & ts.TypeFlags.Null) ? "null" : "undefined";
      return { kind: "optional", nothing, inner: this.describe(this.checker.getNonNullableType(type), node) };
    }
    const shape = this.shape(type);
    const fields = owner => this.fields(owner, node).map(f => ({ name: f.name, lean: name(f.name), type: this.describe(f.type, f.node) }));
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
      params: fn.parameters.map(p => this.describe(this.checker.getTypeAtLocation(p), p)),
      result: this.describe(this.checker.getReturnTypeOfSignature(signature), fn),
    };
  }

  shape(type) {
    const symbol = type.aliasSymbol ?? type.symbol;
    const declaration = symbol?.declarations?.[0];
    return declaration ? this.types.get(declaration) : undefined;
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
    const fn = this.bodyOf(declaration);
    if (!fn || !fn.body) throw this.fail(declaration, "this function has no body to translate");
    if (fn.typeParameters?.length) throw this.fail(fn, "generic functions are not supported yet");
    if (fn.asteriskToken) throw this.fail(fn, "generators are not supported");
    if (fn.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) throw this.fail(fn, "`async` is not supported yet");
    const lean = this.leanName(declaration, declaration.name.text);
    const entry = { lean, pending: true, recursive: false };
    this.functions.set(declaration, entry);
    this.current.push(declaration);
    const signature = this.checker.getSignatureFromDeclaration(fn);
    const returns = this.checker.getReturnTypeOfSignature(signature);
    const scope = new Scope(this, fn);
    const params = fn.parameters.map(p => {
      if (!ts.isIdentifier(p.name) || p.initializer || p.questionToken || p.dotDotDotToken) {
        throw this.fail(p, "only plain parameters are supported for now");
      }
      const text = local(p.name.text);
      scope.taken.add(text);
      return `(${text} : ${this.type(this.checker.getTypeAtLocation(p), p)})`;
    });
    const result = this.type(returns, fn);
    const flow = scope.functionFlow(returns, result);
    const statements = ts.isBlock(fn.body) ? [...fn.body.statements] : [ts.factory.createReturnStatement(fn.body)];
    const body = ts.isBlock(fn.body)
      ? scope.block(statements, flow, new Map())
      : scope.returning(fn.body, flow, new Map());
    const lines = [`def ${lean} ${params.join(" ")} : Result ${result} := do`, ...body.map(l => `  ${l}`)];
    if (entry.recursive) lines.push("partial_fixpoint");
    this.current.pop();
    entry.pending = false;
    this.order.push(lines.join("\n"));
    return lean;
  }

  // A failed target stays as a bare declaration, so that the contract still
  // elaborates and the other targets are judged. Its theorems are never run.
  stub(declaration) {
    const fn = this.bodyOf(declaration);
    const signature = this.checker.getSignatureFromDeclaration(fn);
    const params = fn.parameters.map((p, index) => {
      const text = ts.isIdentifier(p.name) ? local(p.name.text) : `arg${index}`;
      return `(${text} : ${this.type(this.checker.getTypeAtLocation(p), p)})`;
    });
    const result = this.type(this.checker.getReturnTypeOfSignature(signature), fn);
    const lean = this.leanName(declaration, declaration.name.text);
    this.order.push(`axiom ${lean} ${params.join(" ")} : Result ${result}`);
    return lean;
  }

  declareConstant(declaration) {
    if (this.constants.has(declaration)) return this.constants.get(declaration);
    this.checkFile(declaration.getSourceFile());
    const value = this.literal(declaration.initializer);
    if (value === undefined) throw this.fail(declaration, "only number constants are supported for now");
    const lean = this.leanName(declaration, declaration.name.text);
    this.order.push(`def ${lean} : Js.Num := ${this.number(value, declaration)}`);
    this.constants.set(declaration, lean);
    return lean;
  }
}

// Translates one function body. `env` maps a variable's symbol to how it reads
// in the current branch, which is how narrowing reaches the Lean output.
class Scope {
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
      ts.forEachChild(node, child => walk(child, nested || (ts.isFunctionLike(node) && node !== fn)));
    };
    this.owned = new Set();
    walk(fn, false);
    this.checkOwnership();
  }

  // A method that merely shares a name with a mutating one, such as a call to
  // a user's own `set`, is judged as a call, not as a write.
  isBuiltinReceiver(node, write) {
    if (!ts.isCallExpression(node)) return false;
    return !this.isArray(write);
  }

  isArray(node) {
    return this.checker.isArrayType(this.checker.getApparentType(this.typeOf(node)));
  }

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
      if (ts.isForOfStatement(node)) {
        const iterated = rootOf(node.expression);
        if (ts.isIdentifier(iterated) && this.owned.has(this.symbol(iterated)) && this.assignedIn([node.statement]).includes(this.symbol(iterated))) {
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
      if (ts.isFunctionLike(node)) return;
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

  isNumber(node) { return (this.typeOf(node).flags & ts.TypeFlags.NumberLike) !== 0; }
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
      if (!first.expression) {
        if (flow.result !== "Unit") throw this.t.fail(first, "`return` without a value");
        return flow.ret("()");
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
    return [...lines, ...flow.ret(value)];
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
    if (!ts.isPropertyAccessExpression(callee) || !MUTATING.has(callee.name.text) || !this.isArray(callee.expression)) return false;
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

  conditional(statement, rest, flow, env) {
    const whenTrue = statement.thenStatement;
    const whenFalse = statement.elseStatement;
    const trueExits = this.exits(whenTrue);
    const falseExits = whenFalse ? this.exits(whenFalse) : false;
    const narrowed = this.narrowing(statement.expression, env);

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

  forOf(statement, rest, flow, env) {
    if (statement.awaitModifier) throw this.t.fail(statement, "`for await` is not supported");
    if (!this.isArray(statement.expression)) throw this.t.fail(statement.expression, "`for...of` is only supported on arrays for now");
    const declaration = statement.initializer.declarations?.[0];
    if (!declaration || !ts.isIdentifier(declaration.name)) throw this.t.fail(statement, "`for...of` needs a plain variable for now");
    const lines = [];
    const start = new Map(env);
    const iterated = this.expression(statement.expression, start, lines);
    const remaining = { name: this.fresh(), leanType: this.t.type(this.typeOf(statement.expression), statement) };
    start.set(remaining, { lean: remaining.name });
    this.taken.add(remaining.name);
    lines.push(`let ${remaining.name} ← Result.ok (${iterated})`);
    const outer = this.assignedIn([statement]);
    const element = this.symbol(declaration.name);
    const code = this.emitLoop(statement, [remaining, ...outer], rest, flow, start, (body, inside, leave, again) => {
      const next = new Map(inside);
      const head = this.rebind(element, next);
      const tail = this.fresh();
      next.set(remaining, { lean: tail });
      const inner = this.block([statement.statement], { ...body, fall: again, cont: again }, next);
      return [`match ${this.current(remaining, inside)} with`, `| [] =>`, `  ${leave(inside)}`, `| ${head} :: ${tail} =>`, ...this.indent(inner)];
    }, outer);
    return [...lines, ...code];
  }

  indent(lines) { return lines.map(l => `  ${l}`); }

  // `x === null` and `x !== null` on a variable become a `match`, so that the
  // branch where it is present sees the plain value.
  narrowing(test, env) {
    test = unwrap(test);
    if (!ts.isBinaryExpression(test)) return undefined;
    const op = test.operatorToken.kind;
    const equal = op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.EqualsEqualsToken;
    const different = op === ts.SyntaxKind.ExclamationEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsToken;
    if (!equal && !different) return undefined;
    const [variable, other] = this.isNull(test.right) ? [unwrap(test.left), test.right] : [unwrap(test.right), test.left];
    if (!this.isNull(other)) return undefined;
    if (!ts.isIdentifier(variable)) throw this.t.fail(test, "only a local variable can be tested against null for now");
    const symbol = this.symbol(variable);
    // `===` tells null from undefined, and a type only ever allows one of them
    // here, so testing for the other one is always false.
    const strict = op === ts.SyntaxKind.EqualsEqualsEqualsToken || op === ts.SyntaxKind.ExclamationEqualsEqualsToken;
    const allowed = this.declaredType(symbol, variable);
    const wanted = this.isUndefined(unwrap(other)) ? ts.TypeFlags.Undefined : ts.TypeFlags.Null;
    if (strict && !(allowed.isUnion() && allowed.types.some(t => t.flags & wanted))) {
      throw this.t.fail(test, "this null check is always false, because the type allows the other nullish value");
    }
    const lean = this.current(symbol, env);
    return arm => {
      const next = new Map(env);
      const inner = this.rebind(symbol, next, { present: true });
      return [`match ${lean} with`, "| none =>", ...this.indent(arm(equal, env)), `| some ${inner} =>`, ...this.indent(arm(!equal, next))];
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
    const value = this.expression(node, env, lines);
    const from = this.t.type(this.narrowedType(node, env), node);
    const to = this.t.type(target, node);
    if (from === to) return value;
    if (to === `(Option ${from})`) return `(some ${value})`;
    throw this.t.fail(node, `a \`${this.checker.typeToString(this.typeOf(node))}\` is used as a \`${this.checker.typeToString(target)}\`, which is not supported yet`);
  }

  arrayLiteral(node, target, env, lines) {
    const type = this.nullable(target) ? this.checker.getNonNullableType(target) : target;
    if (!this.checker.isArrayType(type)) throw this.t.fail(node, "tuples are not supported yet");
    const item = this.checker.getTypeArguments(type)[0];
    const parts = [];
    let run = [];
    const flush = () => { if (run.length) parts.push(`[${run.join(", ")}]`); run = []; };
    for (const element of node.elements) {
      if (ts.isOmittedExpression(element)) throw this.t.fail(element, "arrays with holes are not supported");
      if (ts.isSpreadElement(element)) {
        flush();
        if (!this.isArray(element.expression)) throw this.t.fail(element, "only arrays can be spread for now");
        parts.push(this.convert(element.expression, type, env, lines));
      } else {
        run.push(this.convert(element, item, env, lines));
      }
    }
    flush();
    if (!parts.length) return `([] : ${this.t.type(type, node)})`;
    return `(${parts.join(" ++ ")})`;
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
        if (!value) continue;
        const slot = this.checker.getTypeOfSymbolAtLocation(property, property.valueDeclaration);
        parts.push(`${name(property.name)} := ${this.convert(value, slot, env, lines)}`);
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
    if (ts.isNumericLiteral(node)) return this.t.number(Number(node.text), node);
    if (ts.isBigIntLiteral(node)) return `(${node.text.slice(0, -1).replace(/_/g, "")} : Int)`;
    if (node.kind === ts.SyntaxKind.TrueKeyword) return "true";
    if (node.kind === ts.SyntaxKind.FalseKeyword) return "false";
    if (ts.isIdentifier(node)) return this.identifier(node, env);
    if (ts.isPropertyAccessExpression(node)) return this.property(node, env, lines);
    if (ts.isArrayLiteralExpression(node)) return this.arrayLiteral(node, this.typeOf(node), env, lines);
    if (ts.isElementAccessExpression(node)) {
      if (!this.isArray(node.expression)) throw this.t.fail(node, "`[]` is only supported on arrays for now");
      if (node.questionDotToken) throw this.t.fail(node, "`?.` is not supported yet");
      return `(Js.at_ ${this.expression(node.expression, env, lines)} ${this.numeric(node.argumentExpression, env, lines)})`;
    }
    if (ts.isNonNullExpression(node)) return this.nonNull(node, env, lines);
    if (ts.isCallExpression(node)) return this.call(node, env, lines);
    if (ts.isConditionalExpression(node)) return this.ternary(node, env, lines);
    if (ts.isSatisfiesExpression(node) || ts.isAsExpression(node)) {
      if (ts.isAsExpression(node) && ts.isConstTypeReference(node.type)) return this.expression(node.expression, env, lines);
      throw this.t.fail(node, "type assertions are not supported yet");
    }
    if (ts.isStringLiteral(node)) return this.tag(node);
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
      return `(decide (${this.condition(node, env, lines)}))`;
    }
    throw this.t.fail(node, `\`${ts.SyntaxKind[node.kind]}\` is not supported yet`);
  }

  operand(node, env, lines) {
    if (this.isBigInt(node)) return this.expression(node, env, lines);
    return this.numeric(node, env, lines);
  }

  arithmetic(op, leftNode, left, rightNode, env, lines) {
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

  tag(node) {
    const type = this.checker.getContextualType(node) ?? this.typeOf(node);
    if (type.isStringLiteral?.() && !type.aliasSymbol) throw this.t.fail(node, "string values are not supported yet");
    this.t.type(type, node);
    return `.${name(node.text)}`;
  }

  identifier(node, env) {
    if (node.text === "undefined") return "none";
    const symbol = this.symbol(node);
    const declaration = symbol?.valueDeclaration;
    if (!declaration) throw this.t.fail(node, `\`${node.text}\` is not declared in the translated code`);
    if (this.isModuleLevel(declaration)) return `_root_.${this.t.declareConstant(declaration)}`;
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
    if (node.questionDotToken) throw this.t.fail(node, "`?.` is not supported yet");
    if (this.isArray(object) && node.name.text === "length") return this.bind(`Js.len ${this.expression(object, env, lines)}`, lines);
    if (this.isArray(object)) throw this.t.fail(node, `\`.${node.name.text}\` is not supported on arrays yet`);
    const type = this.typeOf(object);
    if (type.isUnion()) throw this.t.fail(node, "reading a field of a union outside a `switch` is not supported yet");
    return `${this.expression(object, env, lines)}.${name(node.name.text)}`;
  }

  isLocal(node) {
    const declaration = this.symbol(node)?.valueDeclaration;
    return Boolean(declaration) && !this.t.program.isSourceFileDefaultLibrary(declaration.getSourceFile());
  }

  nonNull(node, env, lines) {
    const inner = this.expression(node.expression, env, lines);
    return this.nullable(this.typeOf(node.expression)) ? this.bind(`Js.unwrap ${inner}`, lines) : inner;
  }

  ternary(node, env, lines) {
    const narrowed = this.narrowing(node.condition, env);
    const type = this.typeOf(node);
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
    if (ts.isPropertyAccessExpression(callee) && ts.isIdentifier(callee.expression) && callee.expression.text === "Math" && !this.isLocal(callee.expression)) {
      return this.math(callee.name.text, node, env, lines);
    }
    if (ts.isPropertyAccessExpression(callee) && this.isArray(callee.expression)) return this.arrayMethod(callee, node, env, lines);
    const signature = this.checker.getResolvedSignature(node);
    let declaration = signature?.declaration;
    if (declaration && !ts.isFunctionDeclaration(declaration)) declaration = declaration.parent;
    declaration = this.t.resolve(declaration);
    if (!declaration) throw this.t.fail(node, "this call isn't to a function the translator can see");
    if (declaration.getSourceFile().isDeclarationFile) throw this.t.fail(node, "this function has no source in the package");
    const lean = this.t.declareFunction(declaration);
    const parameters = signature.getParameters();
    if (parameters.length !== node.arguments.length) throw this.t.fail(node, "optional arguments are not supported yet");
    const args = node.arguments.map((argument, index) => this.convert(argument,
      this.checker.getTypeOfSymbolAtLocation(parameters[index], parameters[index].valueDeclaration), env, lines));
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
      case "concat":
        if (args.length !== 1 || !this.isArray(args[0])) throw this.t.fail(node, "only `concat` of one array is supported for now");
        return `(${list} ++ ${this.expression(args[0], env, lines)})`;
      case "map": case "filter": case "some": case "every": case "find":
        return this.bindCallback(method === "some" ? "some_" : method, this.callback(args, 1, node, env), list, lines);
      case "reduce": {
        if (args.length !== 2) throw this.t.fail(node, "`reduce` needs an initial value");
        const signature = this.checker.getResolvedSignature(node);
        const start = this.convert(args[1], signature.getReturnType(), env, lines);
        return this.bindCallback("reduce", this.callback(args, 2, node, env), `${start} ${list}`, lines);
      }
      default: throw this.t.fail(node, `\`.${method}\` is not supported on arrays yet`);
    }
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
      throw this.t.fail(node, "this operator is not supported");
    }
    if (!this.isBoolean(node)) throw this.t.fail(node, "conditions must be `boolean`; truthiness is not supported yet");
    return `${this.expression(node, env, lines)} = true`;
  }

  logical(node, env, lines) {
    if (!this.isBoolean(node.left) || !this.isBoolean(node.right)) throw this.t.fail(node, "`&&` and `||` are only supported on `boolean` for now");
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
    if (this.isNull(left) || this.isNull(right)) throw this.t.fail(node, "this kind of null check is not supported yet");
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
    if (literal && this.t.type(this.typeOf(other), other)) {
      return `${this.expression(other, env, lines)} = .${name(literal.text)}`;
    }
    throw this.t.fail(node, "`===` is only supported on numbers, booleans and string-literal unions for now");
  }
}

function findDeclaration(translator, target) {
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

export function translate({ root, module, targets }) {
  const translator = new Translator(root, targets);
  const failures = {};
  const names = {};
  const signatures = {};
  let fatal = null;
  for (const target of targets) {
    const snapshot = {
      order: translator.order.length, types: new Map(translator.types),
      functions: new Map(translator.functions), constants: new Map(translator.constants),
    };
    let declaration;
    try {
      declaration = findDeclaration(translator, target);
      names[target] = translator.declareFunction(declaration);
      signatures[target] = translator.signature(declaration);
    } catch (error) {
      if (!(error instanceof Unsupported)) throw error;
      failures[target] = error.message;
      translator.order.length = snapshot.order;
      translator.types = snapshot.types;
      translator.functions = snapshot.functions;
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
  return { module, source: `${[...header, ...translator.order.flatMap(d => [d, ""])].join("\n")}\n`, failures, names, fatal, signatures,
    files: [...translator.fileChecks.keys()].map(f => relative(translator.root, realpathSync(f.fileName))) };
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
