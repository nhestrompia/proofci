// The dynamic translation (spike): TypeScript functions and classes to Lean on `Core.Val` in the
// `Dyn.M` monad. Types don't change the meaning; parameters get `Dyn.Ty` preconditions instead.
// Anything outside the subset throws `Unsupported`, so nothing is guessed.
//   node dyn.mjs <file.ts> <name>... > Out.lean
import { createRequire } from "node:module";
import { fileURLToPath } from "node:url";
import path from "node:path";
import fs from "node:fs";

const require = createRequire(new URL("../../typescript/package.json", import.meta.url));
const ts = require("typescript");

export class Unsupported extends Error {
  constructor(node, why) {
    const sf = node.getSourceFile();
    const { line } = sf.getLineAndCharacterOfPosition(node.getStart());
    super(`${path.basename(sf.fileName)}:${line + 1}: ${why}`);
  }
}

const OPS = { "+": "add", "-": "sub", "*": "mul", "/": "div", "%": "rem", "<": "lt", "<=": "le", ">": "gt", ">=": "ge", "===": "eq", "!==": "ne" };
const COMPOUND = { "+=": "add", "-=": "sub", "*=": "mul" };
const METHODS = new Set(["padStart", "startsWith", "endsWith", "includes", "trim", "toLowerCase", "toUpperCase", "slice", "indexOf",
  "lastIndexOf", "charAt", "charCodeAt", "split", "join", "concat", "replaceAll", "substring", "padEnd", "repeat", "at", "flat"]);
const HOFS = { map: "jsMap", filter: "jsFilter", forEach: "jsForEach", some: "jsSome", every: "jsEvery", find: "jsFind", findIndex: "jsFindIndex" };

const lit = (s) => {
  for (const c of s) if (c.codePointAt(0) > 0xffff) throw new Error("non-BMP");
  return `(str ${JSON.stringify(s)})`;
};
const P = (p) => ({ p });
const Mt = (m) => ({ m });
const v = (e) => (e.p !== undefined ? e.p : `(← ${e.m})`);
const asM = (e) => (e.p !== undefined ? `(pure ${e.p})` : e.m);

export function program(file) {
  return ts.createProgram([file], { target: ts.ScriptTarget.ES2022, strict: true, noEmit: true, skipLibCheck: true, noResolve: false, allowJs: false });
}

export class Dyn {
  constructor(prog) {
    this.prog = prog;
    this.checker = prog.getTypeChecker();
    this.defs = new Map();   // name -> lean text, in dependency order
    this.js = new Map();     // name -> source text, for the Node side
    this.pending = new Set();
    this.classes = new Map(); // class name -> { methods: Set }
    this.consts = new Map();  // module constants read, for the Node side
    this.strings = new Set(); // string literals, to seed inputs
  }

  inLibrary(id) {
    const s = this.checker.getSymbolAtLocation(id);
    return !!s && (s.declarations ?? []).length > 0 && s.declarations.every((d) => this.prog.isSourceFileDefaultLibrary(d.getSourceFile()) || d.getSourceFile().fileName.includes("/typescript/lib/"));
  }

  decl(id) {
    let s = this.checker.getSymbolAtLocation(id);
    if (!s) return undefined;
    if (s.flags & ts.SymbolFlags.Alias) s = this.checker.getAliasedSymbol(s);
    return s.valueDeclaration ?? s.declarations?.[0];
  }

  name(n) { return `${n}'`; }

  add(declNode) {
    const n = declNode.name.text;
    if (this.defs.has(n)) return n;
    if (this.pending.has(n)) throw new Unsupported(declNode, "recursion");
    this.pending.add(n);
    const text = ts.isClassDeclaration(declNode) ? this.cls(declNode) : this.fn(declNode, n);
    this.pending.delete(n);
    this.defs.set(n, text);
    this.js.set(n, declNode.getText());
    return n;
  }

  // --- types to preconditions

  ty(t, node, depth = 0) {
    const c = this.checker, F = ts.TypeFlags;
    if (depth > 3) return ".any";
    if (t.flags & (F.Any | F.Unknown)) return ".any";
    if (t.isUnion()) return `(.union [${t.types.map((u) => this.ty(u, node, depth + 1)).join(", ")}])`;
    if (t.flags & F.Undefined || t.flags & F.Void) return ".undef";
    if (t.flags & F.Null) return ".null";
    if (t.flags & F.BooleanLiteral) return `(.lit (.bool ${c.typeToString(t)}))`;
    if (t.flags & F.Boolean) return ".bool";
    if (t.flags & F.StringLiteral) return `(.lit ${lit(t.value)})`;
    if (t.flags & F.String) return ".str";
    if (t.flags & F.NumberLiteral && Number.isSafeInteger(t.value)) return `(.lit (num ${t.value}))`;
    if (t.flags & F.Number) return ".num";
    if (t.flags & F.BigInt) return ".big";
    if (c.isArrayType(t) || c.isTupleType?.(t)) return `(.arr ${this.ty(c.getTypeArguments(t)[0] ?? c.getAnyType(), node, depth + 1)})`;
    if (t.flags & F.Object) {
      if (t.getCallSignatures().length) return ".any";
      const sym = t.getSymbol();
      const fsx = t.getProperties().filter((p) => !(p.flags & ts.SymbolFlags.Method)).map((p) => {
        const pt = c.getTypeOfSymbolAtLocation(p, node);
        return `(${JSON.stringify(p.name)}, ${pt.getCallSignatures().length ? ".any" : this.ty(pt, node, depth + 1)})`;
      });
      if (sym && sym.flags & ts.SymbolFlags.Class) return `(.cls ${JSON.stringify(sym.name)} [${fsx.join(", ")}])`;
      return `(.obj [${fsx.join(", ")}])`;
    }
    throw new Unsupported(node, `no precondition for type \`${c.typeToString(t)}\``);
  }

  pre(fname, params) {
    const ps = params.map((p) => `(${this.name(p.name.text)} : Val)`).join(" ");
    const conj = params.map((p) => `Is h ${this.ty(this.checker.getTypeAtLocation(p), p)} ${this.name(p.name.text)}`);
    return `abbrev ${fname}.pre ${ps} (h : Heap) : Prop :=\n  ${conj.length ? conj.join(" ∧\n  ") : "True"}\n`;
  }

  // --- functions

  params(f) {
    return f.parameters.map((p) => {
      if (!ts.isIdentifier(p.name) || p.initializer || p.dotDotDotToken) throw new Unsupported(p, "only plain parameters");
      return p;
    });
  }

  fn(f, n, self) {
    if (!(ts.isFunctionDeclaration(f) || ts.isMethodDeclaration(f)) || !f.body) throw new Unsupported(f, "only function declarations");
    if (f.asteriskToken || f.modifiers?.some((m) => m.kind === ts.SyntaxKind.AsyncKeyword)) throw new Unsupported(f, "async and generator functions");
    const ps = this.params(f);
    const sc = new Scope(null, f, this);
    if (self) sc.vars.set("this", { lean: "this" });
    for (const p of ps) sc.declare(p, p.name.text);
    const body = this.block(f.body.statements, sc, 1, true);
    const args = [self ? "(this : Val)" : "", ...ps.map((p) => `(${this.name(p.name.text)} : Val)`)].filter(Boolean).join(" ");
    const pre = self ? "" : this.pre(n, ps);
    return `${pre}def ${n} ${args} : M Val := do\n${body}`;
  }

  cls(c) {
    const n = c.name.text;
    if (c.heritageClauses?.length || c.typeParameters?.length) throw new Unsupported(c, "only classes without `extends` or type parameters");
    const info = { methods: new Set(), arity: {} };
    this.classes.set(n, info);
    let ctor;
    const inits = [], methods = [];
    for (const m of c.members) {
      if (m.modifiers?.some((x) => x.kind === ts.SyntaxKind.StaticKeyword)) throw new Unsupported(m, "static members");
      if (m.name && (ts.isPrivateIdentifier(m.name) || ts.isComputedPropertyName(m.name))) throw new Unsupported(m, "only named members");
      if (ts.isConstructorDeclaration(m)) ctor = m;
      else if (ts.isPropertyDeclaration(m)) inits.push(m);
      else if (ts.isMethodDeclaration(m)) methods.push(m);
      else throw new Unsupported(m, "only fields, a constructor and methods");
    }
    const out = [];
    const sc = new Scope(null, ctor ?? c, this);
    sc.vars.set("this", { lean: "this" });
    const ps = ctor ? this.params(ctor) : [];
    for (const p of ps) sc.declare(p, p.name.text);
    const lines = [`  let this ← record [("__class", ${lit(n)})]`];
    for (const f of inits) {
      const init = f.initializer ? this.expr(f.initializer, sc) : P(".undef");
      lines.push(`  setField this ${JSON.stringify(this.field(f, f.name.text))} ${v(init)}`);
    }
    for (const p of ps) if (ts.isParameterPropertyDeclaration(p, ctor))
      lines.push(`  setField this ${JSON.stringify(this.field(p, p.name.text))} ${this.name(p.name.text)}`);
    if (ctor?.body) lines.push(this.block(ctor.body.statements, sc, 1, false));
    lines.push("  return this");
    const args = ps.map((p) => `(${this.name(p.name.text)} : Val)`).join(" ");
    out.push(`def ${n}.new ${args} : M Val := do\n${lines.join("\n")}\n`);
    for (const m of methods) {
      try {
        out.push(this.fn(m, `${n}.${m.name.text}`, true));
        info.methods.add(m.name.text);
        info.arity[m.name.text] = m.parameters.length;
      } catch (e) {
        if (!(e instanceof Unsupported)) throw e;
        out.push(`-- ${n}.${m.name.text}: unsupported: ${e.message}\n`);
      }
    }
    return out.join("\n");
  }

  field(node, k) {
    if (k.startsWith("__class")) throw new Unsupported(node, "reserved field name");
    return k;
  }

  // --- statements

  ind(d) { return "  ".repeat(d); }

  block(stmts, sc, d, fnBody) {
    const out = [];
    for (const s of stmts) out.push(...this.stmt(s, sc, d));
    if (fnBody && !(stmts.length && ends(stmts[stmts.length - 1]))) out.push(`${this.ind(d)}return .undef`);
    if (!out.length) out.push(`${this.ind(d)}pure ()`);
    return out.join("\n");
  }

  stmt(s, sc, d) {
    const I = this.ind(d);
    if (ts.isVariableStatement(s)) {
      const flags = s.declarationList.flags;
      if (!(flags & (ts.NodeFlags.Const | ts.NodeFlags.Let))) throw new Unsupported(s, "`var`");
      const out = [];
      for (const dcl of s.declarationList.declarations) {
        const init = dcl.initializer ? this.expr(dcl.initializer, sc) : P(".undef");
        if (ts.isObjectBindingPattern(dcl.name)) {
          const tmp = sc.fresh("o");
          out.push(`${I}let ${tmp} := ${v(init)}`);
          for (const el of dcl.name.elements) {
            if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name) || (el.propertyName && !ts.isIdentifier(el.propertyName))) throw new Unsupported(el, "only plain destructuring");
            const key = (el.propertyName ?? el.name).text;
            out.push(...this.bind(el, el.name.text, Mt(`(field ${tmp} ${JSON.stringify(this.field(el, key))})`), sc, I, flags & ts.NodeFlags.Let));
          }
          continue;
        }
        if (!ts.isIdentifier(dcl.name)) throw new Unsupported(dcl, "only plain declarations");
        out.push(...this.bind(dcl, dcl.name.text, init, sc, I, flags & ts.NodeFlags.Let));
      }
      return out;
    }
    if (ts.isReturnStatement(s)) return [`${I}return ${s.expression ? v(this.expr(s.expression, sc)) : ".undef"}`];
    if (ts.isIfStatement(s)) {
      const out = [`${I}if truthy ${v(this.expr(s.expression, sc))} then`, this.sub(s.thenStatement, sc, d + 1)];
      if (s.elseStatement) out.push(`${I}else`, this.sub(s.elseStatement, sc, d + 1));
      return out;
    }
    if (ts.isBlock(s)) return [this.sub(s, sc, d)];
    if (ts.isExpressionStatement(s)) return this.effect(s.expression, sc, I);
    if (ts.isThrowStatement(s)) {
      const e = s.expression;
      if (ts.isNewExpression(e) && ts.isIdentifier(e.expression) && !this.classes.has(e.expression.text)) {
        const dcl = this.decl(e.expression);
        if (!dcl || !ts.isClassDeclaration(dcl) || !this.tryAdd(dcl)) return [`${I}let _ ← (stuck : M Val)`];
      }
      return [`${I}throwV ${v(this.expr(e, sc))}`];
    }
    if (ts.isForOfStatement(s)) {
      if (s.awaitModifier) throw new Unsupported(s, "`for await`");
      const dl = s.initializer;
      if (!ts.isVariableDeclarationList(dl) || !(dl.flags & ts.NodeFlags.Const) || dl.declarations.length !== 1 || !ts.isIdentifier(dl.declarations[0].name))
        throw new Unsupported(s, "only `for (const x of xs)`");
      const inner = new Scope(sc, s, this);
      const x = inner.declare(dl.declarations[0], dl.declarations[0].name.text);
      return [`${I}for ${x} in (← iter ${v(this.expr(s.expression, sc))}) do`, this.sub(s.statement, inner, d + 1)];
    }
    if (ts.isWhileStatement(s))
      return [`${I}for _ in fuel do`, `${this.ind(d + 1)}if !(truthy ${v(this.expr(s.expression, sc))}) then break`, this.sub(s.statement, sc, d + 1)];
    if (ts.isForStatement(s)) {
      const inner = new Scope(sc, s, this);
      const out = [];
      const dl = s.initializer;
      if (dl && ts.isVariableDeclarationList(dl)) {
        if (!(dl.flags & ts.NodeFlags.Let)) throw new Unsupported(dl, "only `let` in `for (;;)`");
        for (const dcl of dl.declarations) {
          if (!ts.isIdentifier(dcl.name)) throw new Unsupported(dcl, "only plain declarations");
          if (inner.boxed(dcl)) throw new Unsupported(dcl, "a `for (;;)` variable captured by a closure");
          out.push(...this.bind(dcl, dcl.name.text, dcl.initializer ? this.expr(dcl.initializer, inner) : P(".undef"), inner, I, true));
        }
      } else if (dl) out.push(...this.effect(dl, inner, I));
      if (hasContinue(s.statement)) throw new Unsupported(s, "`continue` in `for (;;)`");
      const J = this.ind(d + 1);
      out.push(`${I}for _ in fuel do`);
      if (s.condition) out.push(`${J}if !(truthy ${v(this.expr(s.condition, inner))}) then break`);
      out.push(this.sub(s.statement, inner, d + 1));
      if (s.incrementor) out.push(...this.effect(s.incrementor, inner, J));
      return out;
    }
    if (s.kind === ts.SyntaxKind.BreakStatement && !s.label) return [`${I}break`];
    if (s.kind === ts.SyntaxKind.ContinueStatement && !s.label) return [`${I}continue`];
    if (ts.isEmptyStatement(s)) return [];
    throw new Unsupported(s, `the statement \`${ts.SyntaxKind[s.kind]}\` is not in the dynamic subset`);
  }

  tryAdd(dcl) {
    try { this.add(dcl); return true; } catch (e) { if (e instanceof Unsupported) return false; throw e; }
  }

  sub(s, sc, d) {
    const inner = new Scope(sc, s, this);
    return this.block(ts.isBlock(s) ? s.statements : [s], inner, d, false);
  }

  bind(node, name, init, sc, I, mutable) {
    const x = sc.declare(node, name);
    if (sc.boxed(node)) return [`${I}let ${x} ← cell ${v(init)}`];
    return [`${I}let ${mutable ? "mut " : ""}${x} ${init.p !== undefined ? ":=" : "←"} ${init.p ?? init.m}`];
  }

  effect(e, sc, I) {
    if (ts.isBinaryExpression(e) && (e.operatorToken.kind === ts.SyntaxKind.EqualsToken || COMPOUND[e.operatorToken.getText()])) {
      const op = COMPOUND[e.operatorToken.getText()];
      return this.assign(e.left, op ? (cur) => Mt(`(bin .${op} ${cur} ${v(this.expr(e.right, sc))})`) : () => this.expr(e.right, sc), sc, I);
    }
    if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) && [ts.SyntaxKind.PlusPlusToken, ts.SyntaxKind.MinusMinusToken].includes(e.operator)) {
      const op = e.operator === ts.SyntaxKind.PlusPlusToken ? "add" : "sub";
      return this.assign(e.operand, (cur) => Mt(`(bin .${op} ${cur} (num 1))`), sc, I);
    }
    const r = this.expr(e, sc);
    return r.p !== undefined ? [] : [`${I}let _ ← ${r.m}`];
  }

  // `rhs(cur)` builds the new value from the current one, for compound assignment.
  assign(target, rhs, sc, I) {
    target = strip(target);
    if (ts.isIdentifier(target)) {
      const b = sc.lookup(target.text);
      if (!b || !b.mutable) throw new Unsupported(target, `assignment to \`${target.text}\``);
      if (b.cell) {
        const val = rhs(`(← get ${b.lean})`);
        return [`${I}put ${b.lean} ${v(val)}`];
      }
      const val = rhs(b.lean);
      return [`${I}${b.lean} ${val.p !== undefined ? ":=" : "←"} ${val.p ?? val.m}`];
    }
    if (ts.isPropertyAccessExpression(target) && !target.questionDotToken) {
      const o = sc.fresh("o");
      const k = JSON.stringify(this.field(target, target.name.text));
      const val = rhs(`(← field ${o} ${k})`);
      return [`${I}let ${o} := ${v(this.expr(target.expression, sc))}`, `${I}setField ${o} ${k} ${v(val)}`];
    }
    if (ts.isElementAccessExpression(target) && !target.questionDotToken) {
      const o = sc.fresh("o"), i = sc.fresh("i");
      const val = rhs(`(← index ${o} ${i})`);
      return [`${I}let ${o} := ${v(this.expr(target.expression, sc))}`, `${I}let ${i} := ${v(this.expr(target.argumentExpression, sc))}`, `${I}setIndex ${o} ${i} ${v(val)}`];
    }
    throw new Unsupported(target, "assignment target");
  }

  // --- expressions

  expr(e, sc) {
    const K = ts.SyntaxKind;
    if (ts.isOptionalChain(e) && !e.questionDotToken && !(ts.isCallExpression(e) && e.expression.questionDotToken))
      throw new Unsupported(e, "an optional chain continued past `?.`");
    if (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isNonNullExpression(e) || ts.isSatisfiesExpression?.(e) || ts.isTypeAssertionExpression(e)) return this.expr(e.expression, sc);
    if (ts.isNumericLiteral(e)) {
      const n = Number(e.text.replace(/_/g, ""));
      if (!Number.isSafeInteger(n)) throw new Unsupported(e, "only whole-number literals");
      return P(`(num ${n})`);
    }
    if (ts.isStringLiteral(e) || ts.isNoSubstitutionTemplateLiteral(e)) { this.strings.add(e.text); return P(lit(e.text)); }
    if (e.kind === K.TrueKeyword) return P("(.bool true)");
    if (e.kind === K.FalseKeyword) return P("(.bool false)");
    if (e.kind === K.NullKeyword) return P(".null");
    if (e.kind === K.ThisKeyword) {
      const b = sc.lookup("this");
      if (!b) throw new Unsupported(e, "`this` outside a method");
      return P("this");
    }
    if (ts.isTemplateExpression(e)) {
      const parts = [lit(e.head.text)];
      for (const span of e.templateSpans) parts.push(`(← toStr ${v(this.expr(span.expression, sc))})`, lit(span.literal.text));
      let acc = parts[0];
      for (const p of parts.slice(1)) acc = `(← bin .add ${acc} ${p})`;
      return Mt(`(do pure ${acc})`);
    }
    if (ts.isIdentifier(e)) return this.ident(e, sc);
    if (ts.isPrefixUnaryExpression(e)) {
      const x = this.expr(e.operand, sc);
      if (e.operator === K.ExclamationToken) return x.p !== undefined ? P(`(notV ${x.p})`) : Mt(`(do pure (notV ${v(x)}))`);
      if (e.operator === K.MinusToken) return Mt(`(do neg ${v(x)})`);
      throw new Unsupported(e, "prefix operator");
    }
    if (ts.isTypeOfExpression(e)) {
      const x = this.expr(e.expression, sc);
      return x.p !== undefined ? P(`(typeOf ${x.p})`) : Mt(`(do pure (typeOf ${v(x)}))`);
    }
    if (ts.isBinaryExpression(e)) {
      const op = e.operatorToken.getText();
      const a = this.expr(e.left, sc);
      if (op === "&&" || op === "||" || op === "??") {
        const b = this.expr(e.right, sc), t = sc.fresh("a");
        const test = op === "??" ? `nullish ${t}` : `truthy ${t}`;
        const [yes, no] = op === "||" ? [`pure ${t}`, asM(b)] : [asM(b), `pure ${t}`];
        return Mt(`(do let ${t} := ${v(a)}; if ${test} then ${op === "??" ? asM(b) : yes} else ${op === "??" ? `pure ${t}` : no})`);
      }
      if ((op === "==" || op === "!=") && [e.left, e.right].some((x) => strip(x).kind === K.NullKeyword || (ts.isIdentifier(strip(x)) && strip(x).text === "undefined"))) {
        const other = strip(e.left).kind === K.NullKeyword || (ts.isIdentifier(strip(e.left)) && strip(e.left).text === "undefined") ? this.expr(e.right, sc) : a;
        const r = `(.bool (${op === "!=" ? "!" : ""}nullish ${v(other)}))`;
        return other.p !== undefined ? P(r) : Mt(`(do pure ${r})`);
      }
      if (OPS[op]) return Mt(`(do bin .${OPS[op]} ${v(a)} ${v(this.expr(e.right, sc))})`);
      throw new Unsupported(e, `the operator \`${op}\``);
    }
    if (ts.isConditionalExpression(e)) {
      return Mt(`(do if truthy ${v(this.expr(e.condition, sc))} then ${asM(this.expr(e.whenTrue, sc))} else ${asM(this.expr(e.whenFalse, sc))})`);
    }
    if (ts.isPropertyAccessExpression(e)) {
      const o = this.expr(e.expression, sc), k = e.name.text;
      if (ts.isIdentifier(e.expression) && ["Number", "Math", "String", "Array", "Object", "JSON"].includes(e.expression.text) && this.inLibrary(e.expression))
        throw new Unsupported(e, `\`${e.getText()}\``);
      const read = k === "length" ? `length` : `(fun o => field o ${JSON.stringify(this.field(e, k))})`;
      if (e.questionDotToken) { const t = sc.fresh("o"); return Mt(`(do let ${t} := ${v(o)}; if nullish ${t} then pure .undef else ${read} ${t})`); }
      return Mt(`(do ${read} ${v(o)})`);
    }
    if (ts.isElementAccessExpression(e)) {
      if (e.questionDotToken) throw new Unsupported(e, "`?.[`");
      return Mt(`(do index ${v(this.expr(e.expression, sc))} ${v(this.expr(e.argumentExpression, sc))})`);
    }
    if (ts.isObjectLiteralExpression(e)) {
      const steps = [];
      let acc = "[]";
      const pairs = [];
      for (const p of e.properties) {
        if (ts.isSpreadAssignment(p)) {
          const t = sc.fresh("s");
          steps.push(`let ${t} ← fieldsOf ${v(this.expr(p.expression, sc))}`);
          acc = `(mergeFields ${acc} ${t})`;
          continue;
        }
        if (!(ts.isPropertyAssignment(p) || ts.isShorthandPropertyAssignment(p)) || !(ts.isIdentifier(p.name) || ts.isStringLiteral(p.name)) || /^\d/.test(p.name.text))
          throw new Unsupported(p, "only named properties and spreads in object literals");
        const val = ts.isShorthandPropertyAssignment(p) ? this.ident(p.name, sc) : this.expr(p.initializer, sc);
        const t = sc.fresh("f");
        steps.push(`let ${t} := ${v(val)}`);
        acc = `(mergeFields ${acc} [(${JSON.stringify(this.field(p, p.name.text))}, ${t})])`;
        pairs.push([this.field(p, p.name.text), t]);
      }
      const keys = pairs.map(([k]) => k);
      const flat = pairs.length === e.properties.length && new Set(keys).size === keys.length
        ? `[${pairs.map(([k, t]) => `(${JSON.stringify(k)}, ${t})`).join(", ")}]` : null;
      return Mt(`(do ${[...steps, `record ${flat ?? acc}`].join("; ")})`);
    }
    if (ts.isArrayLiteralExpression(e)) {
      const steps = [];
      let acc = "[]";
      for (const x of e.elements) {
        const t = sc.fresh("x");
        if (ts.isSpreadElement(x)) steps.push(`let ${t} ← items ${v(this.expr(x.expression, sc))}`), (acc = `${acc} ++ ${t}`);
        else if (ts.isOmittedExpression(x)) throw new Unsupported(x, "holes");
        else steps.push(`let ${t} := ${v(this.expr(x, sc))}`), (acc = `${acc} ++ [${t}]`);
      }
      return Mt(`(do ${[...steps, `arr (${acc})`].join("; ")})`);
    }
    if (ts.isNewExpression(e)) {
      if (!ts.isIdentifier(e.expression)) throw new Unsupported(e, "`new` of an expression");
      const dcl = this.decl(e.expression);
      if (!dcl || !ts.isClassDeclaration(dcl)) throw new Unsupported(e, `\`new ${e.expression.text}\``);
      const n = this.add(dcl);
      return Mt(`(do ${n}.new ${this.args(e.arguments ?? [], dcl.members.find(ts.isConstructorDeclaration)?.parameters.length ?? 0, sc, e)})`);
    }
    if (ts.isCallExpression(e)) return this.call(e, sc);
    throw new Unsupported(e, `the expression \`${ts.SyntaxKind[e.kind]}\` is not in the dynamic subset`);
  }

  ident(e, sc) {
    if (e.text === "undefined" && !this.checker.getSymbolAtLocation(e)?.declarations?.length) return P(".undef");
    const b = sc.lookup(e.text);
    if (b) return b.cell ? Mt(`(get ${b.lean})`) : P(b.lean);
    const dcl = this.decl(e);
    if (dcl && ts.isVariableDeclaration(dcl) && dcl.parent.flags & ts.NodeFlags.Const && dcl.initializer) {
      const init = strip(dcl.initializer);
      this.consts.set(e.text, init.getText());
      if (ts.isStringLiteral(init) || ts.isNoSubstitutionTemplateLiteral(init)) { this.strings.add(init.text); return P(lit(init.text)); }
      if (ts.isNumericLiteral(init) && Number.isSafeInteger(Number(init.text.replace(/_/g, "")))) return P(`(num ${Number(init.text.replace(/_/g, ""))})`);
      if (init.kind === ts.SyntaxKind.TrueKeyword || init.kind === ts.SyntaxKind.FalseKeyword) return P(`(.bool ${init.getText()})`);
    }
    throw new Unsupported(e, `reading \`${e.text}\``);
  }

  args(as, arity, sc, node) {
    if (as.length > arity || as.some(ts.isSpreadElement)) throw new Unsupported(node, "argument count");
    const vals = as.map((a) => v(this.expr(a, sc)));
    while (vals.length < arity) vals.push(".undef");
    return vals.join(" ");
  }

  callback(f, sc, arity) {
    f = strip(f);
    if (!(ts.isArrowFunction(f) || ts.isFunctionExpression(f)) || f.asteriskToken || f.modifiers?.length) throw new Unsupported(f, "only an arrow function as the callback");
    const ps = this.params(f);
    if (ps.length > arity) throw new Unsupported(f, "callback parameters");
    const inner = new Scope(sc, f, this, true);
    const names = [];
    for (let i = 0; i < arity; i++) names.push(ps[i] ? inner.declare(ps[i], ps[i].name.text) : "_");
    const body = ts.isBlock(f.body) ? this.block(f.body.statements, inner, 2, true) : `    return ${v(this.expr(f.body, inner))}`;
    return `(fun ${names.join(" ")} => do\n${body.replace(/^/gm, "  ")})`;
  }

  call(e, sc) {
    const callee = strip(e.expression), as = e.arguments;
    if (ts.isIdentifier(callee)) {
      if (this.inLibrary(callee)) {
        if (callee.text === "String" && as.length === 1) return Mt(`(do toStr ${v(this.expr(as[0], sc))})`);
        if (callee.text === "Number" && as.length === 1) return Mt(`(do toNum ${v(this.expr(as[0], sc))})`);
        throw new Unsupported(e, `\`${callee.text}\``);
      }
      const dcl = this.decl(callee);
      if (!dcl || !ts.isFunctionDeclaration(dcl) || !dcl.body) throw new Unsupported(e, `this call isn't to a function the dynamic path can see`);
      const n = this.add(dcl);
      return Mt(`(do ${n} ${this.args(as, dcl.parameters.length, sc, e)})`);
    }
    if (!ts.isPropertyAccessExpression(callee)) throw new Unsupported(e, "call of an expression");
    const m = callee.name.text;
    if (ts.isIdentifier(callee.expression) && this.inLibrary(callee.expression)) {
      const lib = `${callee.expression.text}.${m}`;
      const one = { "Number.isInteger": "isInteger", "Number.isFinite": "isFinite" }[lib];
      if (one && as.length === 1) { const x = this.expr(as[0], sc); return x.p !== undefined ? P(`(${one} ${x.p})`) : Mt(`(do pure (${one} ${v(x)}))`); }
      if (lib === "Array.isArray" && as.length === 1) return Mt(`(do isArray ${v(this.expr(as[0], sc))})`);
      if (["Math.floor", "Math.ceil", "Math.trunc"].includes(lib) && as.length === 1) return Mt(`(do math F64.${m} ${v(this.expr(as[0], sc))})`);
      if ((lib === "Math.max" || lib === "Math.min") && as.length === 2) return Mt(`(do prim .${lib.slice(5)} [${v(this.expr(as[0], sc))}, ${v(this.expr(as[1], sc))}])`);
      if (lib === "Math.abs" && as.length === 1) return Mt(`(do abs ${v(this.expr(as[0], sc))})`);
      throw new Unsupported(e, `\`${lib}\``);
    }
    const rt = this.checker.getTypeAtLocation(callee.expression);
    for (const u of rt.isUnion() ? rt.types : [rt]) {
      const cd = u.getSymbol()?.valueDeclaration;
      if (cd && ts.isClassDeclaration(cd) && cd.name) this.tryAdd(cd);
    }
    const o = this.expr(callee.expression, sc);
    const t = sc.fresh("r");
    let body;
    const owners = [...this.classes].filter(([, c]) => c.methods.has(m)).map(([n]) => n);
    if (HOFS[m] && as.length === 1) body = `${HOFS[m]} ${t} ${this.callback(as[0], sc, 2)}`;
    else if (m === "reduce" && as.length === 2) body = `jsReduce ${t} ${this.callback(as[0], sc, 3)} ${v(this.expr(as[1], sc))}`;
    else if (m === "push" && as.length === 1) body = `push ${t} ${v(this.expr(as[0], sc))}`;
    else if (METHODS.has(m)) body = `method .${["at", "repeat"].includes(m) ? `«${m}»` : m} ${t} [${as.map((a) => v(this.expr(a, sc))).join(", ")}]`;
    else body = "(stuck : M Val)";
    for (const c of owners) {
      const meth = this.classes.get(c);
      body = `if (← isMethodOf ${t} ${JSON.stringify(c)} ${JSON.stringify(m)}) then ${c}.${m} ${t} ${this.args(as, meth.arity[m], sc, e)} else ${body}`;
    }
    const pre = `let ${t} := ${v(o)}`;
    if (callee.questionDotToken) return Mt(`(do ${pre}; if nullish ${t} then pure .undef else ${body})`);
    return Mt(`(do ${pre}; ${body})`);
  }
}

function strip(e) {
  while (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isNonNullExpression(e) || ts.isSatisfiesExpression?.(e) || ts.isTypeAssertionExpression(e)) e = e.expression;
  return e;
}

function ends(s) {
  if (ts.isReturnStatement(s) || ts.isThrowStatement(s)) return true;
  if (ts.isIfStatement(s)) return !!s.elseStatement && ends(s.thenStatement) && ends(s.elseStatement);
  if (ts.isBlock(s)) return s.statements.length > 0 && ends(s.statements[s.statements.length - 1]);
  return false;
}

// Names in scope. A variable that a nested function assigns lives in a heap cell.
// A `continue` that would skip the update of the enclosing `for (;;)`.
function hasContinue(n) {
  if (n.kind === ts.SyntaxKind.ContinueStatement) return true;
  if (ts.isIterationStatement(n, false) || ts.isFunctionLike(n)) return false;
  return ts.forEachChild(n, hasContinue) ?? false;
}

class Scope {
  constructor(parent, node, dyn, fnBoundary = false) {
    this.parent = parent; this.node = node; this.dyn = dyn; this.fnBoundary = fnBoundary;
    this.vars = new Map();
    this.root = parent ? parent.root : this;
    if (!parent) { this.counter = 0; this.boxedDecls = boxedIn(node, dyn.checker); }
  }
  fresh(base) { return `${base}${++this.root.counter}`; }
  boxed(node) { return this.root.boxedDecls.has(node); }
  declare(node, name) {
    if (this.lookup(name)) throw new Unsupported(node, `\`${name}\` shadows an outer name`);
    const mutable = ts.isVariableDeclaration(node) && !!(node.parent.flags & ts.NodeFlags.Let);
    const lean = `${this.dyn.name(name)}`;
    const cell = mutable && this.boxed(node);
    this.vars.set(name, { lean, mutable, cell });
    return lean;
  }
  lookup(name, crossed = false) {
    const b = this.vars.get(name);
    if (b) {
      if (crossed && b.mutable && !b.cell) return { ...b, mutable: false, crossed: true };
      return b;
    }
    return this.parent ? this.parent.lookup(name, crossed || this.fnBoundary) : undefined;
  }
}

// `let` variables assigned inside a function nested in the one that declares them.
function boxedIn(root, checker) {
  const out = new Set();
  const owner = (n) => ts.findAncestor(n.parent, (a) => ts.isFunctionLike(a));
  const visit = (n) => {
    const target = ts.isBinaryExpression(n) && ts.isAssignmentOperator(n.operatorToken.kind) ? n.left
      : (ts.isPostfixUnaryExpression(n) || ts.isPrefixUnaryExpression(n)) && [ts.SyntaxKind.PlusPlusToken, ts.SyntaxKind.MinusMinusToken].includes(n.operator) ? n.operand : null;
    if (target && ts.isIdentifier(strip(target))) {
      const d = checker.getSymbolAtLocation(strip(target))?.valueDeclaration;
      if (d && owner(d) !== owner(n)) out.add(d);
    }
    ts.forEachChild(n, visit);
  };
  visit(root);
  return out;
}

export function translate(file, names) {
  const prog = program(file);
  const sf = prog.getSourceFile(file);
  const d = new Dyn(prog);
  for (const n of names) {
    const [top, member] = n.split(".");
    let found;
    sf.forEachChild((s) => { if ((ts.isFunctionDeclaration(s) || ts.isClassDeclaration(s)) && s.name?.text === top) found = s; });
    if (!found) throw new Error(`${n} not found in ${file}`);
    d.add(found);
  }
  return d;
}

export function lean(d, ns) {
  return `import Dyn\n\nnamespace ${ns}\nopen Core Dyn\n\nset_option maxRecDepth 4096\n\n${[...d.defs.values()].join("\n")}\nend ${ns}\n`;
}

if (process.argv[1] === fileURLToPath(import.meta.url)) {
  const [file, ns, ...names] = process.argv.slice(2);
  try {
    process.stdout.write(lean(translate(path.resolve(file), names), ns));
  } catch (e) {
    if (e instanceof Unsupported) { console.error(`unsupported: ${e.message}`); process.exit(2); }
    throw e;
  }
}
