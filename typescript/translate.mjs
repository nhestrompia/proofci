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
    if (type.isUnion() && type.types.every(t => t.flags & TypeFlags.NumberLike)) return "Js.Num";
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
    if (ts.isPrefixUnaryExpression(node) && node.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(unwrap(node.operand))) {
      return -Number(unwrap(node.operand).text);
    }
    return undefined;
  }

  number(value, node) {
    if (!Number.isSafeInteger(value)) throw this.fail(node, `the number ${value} is not a safe integer`);
    return `(Js.Num.mk (${value}) (by decide) (by decide))`;
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
    if (this.functions.has(declaration)) {
      const known = this.functions.get(declaration);
      if (!known) throw this.fail(declaration, "recursion is not supported yet");
      return known.lean;
    }
    this.checkFile(declaration.getSourceFile());
    const fn = this.bodyOf(declaration);
    if (!fn || !fn.body) throw this.fail(declaration, "this function has no body to translate");
    if (fn.typeParameters?.length) throw this.fail(fn, "generic functions are not supported yet");
    if (fn.asteriskToken) throw this.fail(fn, "generators are not supported");
    if (fn.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) throw this.fail(fn, "`async` is not supported yet");
    this.functions.set(declaration, null);
    const lean = this.leanName(declaration, declaration.name.text);
    const signature = this.checker.getSignatureFromDeclaration(fn);
    const returns = this.checker.getReturnTypeOfSignature(signature);
    const scope = new Scope(this, fn);
    const params = fn.parameters.map(p => {
      if (!ts.isIdentifier(p.name) || p.initializer || p.questionToken || p.dotDotDotToken) {
        throw this.fail(p, "only plain parameters are supported for now");
      }
      const text = local(p.name.text);
      return `(${text} : ${this.type(this.checker.getTypeAtLocation(p), p)})`;
    });
    const result = this.type(returns, fn);
    const body = ts.isBlock(fn.body)
      ? scope.block([...fn.body.statements], returns, new Map())
      : scope.block([ts.factory.createReturnStatement(fn.body)], returns, new Map(), fn.body);
    const text = [`def ${lean} ${params.join(" ")} : Result ${result} := do`, ...body.map(l => `  ${l}`)].join("\n");
    this.functions.set(declaration, { lean });
    this.order.push(text);
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
    this.writes = new Set();
    const walk = node => {
      if (ts.isIdentifier(node)) this.names.add(node.text);
      if (ts.isBinaryExpression(node) && ts.isAssignmentOperator(node.operatorToken.kind)) this.noteWrite(node.left);
      if ((ts.isPrefixUnaryExpression(node) || ts.isPostfixUnaryExpression(node))
        && (node.operator === ts.SyntaxKind.PlusPlusToken || node.operator === ts.SyntaxKind.MinusMinusToken)) this.noteWrite(node.operand);
      ts.forEachChild(node, walk);
    };
    walk(fn);
  }

  noteWrite(target) {
    throw this.t.fail(target, "assignment is not supported yet");
  }

  fresh() {
    let candidate;
    do { candidate = `tmp${++this.counter}`; } while (this.names.has(candidate));
    return candidate;
  }

  symbol(node) {
    const symbol = this.checker.getSymbolAtLocation(node);
    return symbol && symbol.flags & ts.SymbolFlags.Alias ? this.checker.getAliasedSymbol(symbol) : symbol;
  }

  typeOf(node) {
    return this.checker.getTypeAtLocation(node);
  }

  isNumber(node) { return (this.typeOf(node).flags & ts.TypeFlags.NumberLike) !== 0; }
  isBoolean(node) { return (this.typeOf(node).flags & ts.TypeFlags.BooleanLike) !== 0; }
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

  // Lines for `statements`. Every path must leave through `return`.
  block(statements, returns, env, expression) {
    if (expression) return this.returning(expression, returns, env);
    if (!statements.length) throw this.t.fail(this.fn, "a path reaches the end of the function without `return`");
    const [first, ...rest] = statements;
    if (ts.isBlock(first)) return this.block([...first.statements, ...rest], returns, env);
    if (ts.isEmptyStatement(first)) return this.block(rest, returns, env);
    if (ts.isReturnStatement(first)) {
      if (!first.expression) throw this.t.fail(first, "`return` without a value");
      return this.returning(first.expression, returns, env);
    }
    if (ts.isVariableStatement(first)) return this.variable(first, rest, returns, env);
    if (ts.isIfStatement(first)) return this.conditional(first, rest, returns, env);
    if (ts.isSwitchStatement(first)) return this.switching(first, returns, env);
    throw this.t.fail(first, `\`${ts.SyntaxKind[first.kind]}\` is not supported yet`);
  }

  returning(node, returns, env) {
    const lines = [];
    const value = this.convert(node, returns, env, lines);
    return [...lines, `Result.ok ${value}`];
  }

  variable(statement, rest, returns, env) {
    if (!(statement.declarationList.flags & ts.NodeFlags.BlockScoped)) throw this.t.fail(statement, "`var` is not supported");
    const lines = [];
    const next = new Map(env);
    for (const declaration of statement.declarationList.declarations) {
      if (!declaration.initializer) throw this.t.fail(declaration, "a declaration without a value");
      if (ts.isIdentifier(declaration.name)) {
        const value = this.expression(declaration.initializer, env, lines);
        lines.push(`let ${local(declaration.name.text)} := ${value}`);
        next.delete(this.symbol(declaration.name));
        continue;
      }
      if (!ts.isObjectBindingPattern(declaration.name)) throw this.t.fail(declaration, "array destructuring is not supported yet");
      const source = this.expression(declaration.initializer, env, lines);
      for (const element of declaration.name.elements) {
        if (element.dotDotDotToken || element.initializer || !ts.isIdentifier(element.name)) {
          throw this.t.fail(element, "only plain destructuring is supported for now");
        }
        const field = element.propertyName?.getText() ?? element.name.text;
        lines.push(`let ${local(element.name.text)} := ${source}.${name(field)}`);
      }
    }
    return [...lines, ...this.block(rest, returns, next)];
  }

  exits(node) {
    if (ts.isReturnStatement(node)) return true;
    if (ts.isBlock(node)) return node.statements.some(s => this.exits(s));
    if (ts.isIfStatement(node)) return Boolean(node.elseStatement) && this.exits(node.thenStatement) && this.exits(node.elseStatement);
    if (ts.isSwitchStatement(node)) return true;
    return false;
  }

  conditional(statement, rest, returns, env) {
    const whenTrue = statement.thenStatement;
    const whenFalse = statement.elseStatement;
    const trueExits = this.exits(whenTrue);
    const falseExits = whenFalse ? this.exits(whenFalse) : false;
    // A branch that doesn't return would need a join point; that comes with mutation.
    if (!trueExits && !falseExits) throw this.t.fail(statement, "an `if` where neither branch returns is not supported yet");
    const thenPath = trueExits ? [whenTrue] : [whenTrue, ...rest];
    const elsePath = falseExits ? [whenFalse] : [...(whenFalse ? [whenFalse] : []), ...rest];
    const narrowed = this.narrowing(statement.expression, env);
    if (narrowed) return narrowed(onPath => this.block(onPath ? thenPath : elsePath, returns, env), (onPath, next) => this.block(onPath ? thenPath : elsePath, returns, next));
    const lines = [];
    const test = this.condition(statement.expression, env, lines);
    return [...lines, `if ${test} then`, ...this.indent(this.block(thenPath, returns, env)),
      "else", ...this.indent(this.block(elsePath, returns, env))];
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
    const lean = name(variable.text);
    return (_unused, arm) => {
      const next = new Map(env);
      next.set(symbol, { present: true });
      return [`match ${lean} with`, "| none =>", ...this.indent(arm(equal, env)), `| some ${lean} =>`, ...this.indent(arm(!equal, next))];
    };
  }

  switching(statement, returns, env) {
    const subject = unwrap(statement.expression);
    if (statement.caseBlock.clauses.some(c => ts.isDefaultClause(c)) && !ts.isPropertyAccessExpression(subject) && !ts.isIdentifier(subject)) {
      throw this.t.fail(statement, "this `switch` is not supported yet");
    }
    let owner, shape;
    if (ts.isPropertyAccessExpression(subject) && subject.name.text === "kind" && ts.isIdentifier(subject.expression)) {
      owner = subject.expression;
      shape = this.t.shape(this.declaredType(this.symbol(owner), owner)) ?? this.declareFor(owner);
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
    let fallback;
    for (const clause of statement.caseBlock.clauses) {
      if (!clause.statements.length) throw this.t.fail(clause, "fall-through between cases is not supported yet");
      if (!clause.statements.some(s => this.exits(s))) throw this.t.fail(clause, "every case must return");
      if (ts.isDefaultClause(clause)) { fallback = clause; continue; }
      const label = unwrap(clause.expression);
      if (!ts.isStringLiteral(label)) throw this.t.fail(clause, "case labels must be string literals");
      arms.set(label.text, clause);
    }
    const lines = [`match ${name(owner.text)} with`];
    const symbol = this.symbol(owner);
    for (const tag of tags) {
      const clause = arms.get(tag) ?? fallback;
      if (!clause) throw this.t.fail(statement, `no case handles \`${tag}\``);
      if (shape.kind === "enum") {
        lines.push(`| .${name(tag)} =>`, ...this.indent(this.block([...clause.statements], returns, env)));
        continue;
      }
      const fields = shape.variants.find(v => v.tag === tag).fields;
      const bound = new Map(fields.map(f => [f, this.fresh()]));
      const next = new Map(env);
      next.set(symbol, { tag, bound });
      lines.push(`| .${name(tag)} ${[...bound.values()].join(" ")} =>`, ...this.indent(this.block([...clause.statements], returns, next)));
    }
    return lines;
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
    const value = this.expression(node, env, lines);
    const from = this.t.type(this.narrowedType(node, env), node);
    const to = this.t.type(target, node);
    if (from === to) return value;
    if (to === `(Option ${from})`) return `(some ${value})`;
    throw this.t.fail(node, `a \`${this.checker.typeToString(this.typeOf(node))}\` is used as a \`${this.checker.typeToString(target)}\`, which is not supported yet`);
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
      return base ? `{ ${base} with ${parts.join(", ")} }` : `{ ${parts.join(", ")} }`;
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
    if (node.kind === ts.SyntaxKind.TrueKeyword) return "true";
    if (node.kind === ts.SyntaxKind.FalseKeyword) return "false";
    if (ts.isIdentifier(node)) return this.identifier(node, env);
    if (ts.isPropertyAccessExpression(node)) return this.property(node, env, lines);
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
        return this.bind(`Js.neg ${this.numeric(node.operand, env, lines)}`, lines);
      }
      throw this.t.fail(node, "this operator is not supported");
    }
    if (ts.isBinaryExpression(node)) {
      const op = node.operatorToken.kind;
      if (ARITHMETIC[op]) {
        if (!this.isNumber(node)) throw this.t.fail(node, "arithmetic is only supported on `number` for now");
        const left = this.numeric(node.left, env, lines);
        const right = this.numeric(node.right, env, lines);
        return this.bind(`Js.${ARITHMETIC[op]} ${left} ${right}`, lines);
      }
      return `(decide (${this.condition(node, env, lines)}))`;
    }
    throw this.t.fail(node, `\`${ts.SyntaxKind[node.kind]}\` is not supported yet`);
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
    return name(node.text);
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
      const arms = narrowed(null, (onPath, next) => branch(onPath ? node.whenTrue : node.whenFalse, next));
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
    return this.bind(`_root_.${lean} ${args.join(" ")}`, lines);
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
    if (this.isBoolean(left) && this.isBoolean(right)) {
      return `${this.expression(left, env, lines)} = ${this.expression(right, env, lines)}`;
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
