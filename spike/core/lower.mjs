// TypeScript to Core. A spike: it handles what the sample functions use and refuses
// the rest. It reads types only to choose `==` forms, so it knows nothing about Lean.
import ts from "../../typescript/node_modules/typescript/lib/typescript.js";
import { dirname, join, relative } from "node:path";

const OPS = { "+": "add", "-": "sub", "*": "mul", "<": "lt", "<=": "le", ">": "gt", ">=": "ge", "===": "eq", "!==": "ne", "/": "div", "%": "rem" };
const lean = s => JSON.stringify(s);
const PRELUDE = { map: "jsMap", filter: "jsFilter", reduce: "jsReduce", some: "jsSome" };
const bits = new DataView(new ArrayBuffer(8));
const num = x => {
  if (Number.isSafeInteger(x) && !Object.is(x, -0)) return `(F64.ofInt (${x}))`;
  bits.setFloat64(0, x);
  return `(F64.ofBits ${bits.getBigUint64(0)})`;
};
const MATH = { floor: "F64.floor", ceil: "F64.ceil", trunc: "F64.trunc" };
const UNITS = t => `[${[...Array(t.length).keys()].map(i => t.charCodeAt(i)).join(", ")}]`;
// Methods that lower to a built-in, by the receiver's type and the number of arguments.
const STRING_METHODS = {
  "startsWith/1": "startsWith", "endsWith/1": "endsWith", "includes/1": "strIncludes", "trim/0": "trim", "trimStart/0": "trimStart",
  "trimEnd/0": "trimEnd", "toLowerCase/0": "toLower", "toUpperCase/0": "toUpper", "slice/1": "sliceFrom", "slice/2": "slice",
  "indexOf/1": "strIndexOf", "lastIndexOf/1": "strLastIndexOf", "charAt/1": "charAt", "charCodeAt/1": "charCodeAt", "split/1": "split",
  "replace/2": "replace", "replaceAll/2": "replaceAll", "substring/2": "substring",
};
const HOF = { map: "map", filter: "filter", some: "some", every: "every", find: "find" };
const READS = new Set(["length", "join", "slice", "includes", "indexOf", "map", "filter", "some", "every", "find", "reduce", "forEach"]);
const ARRAY_METHODS = { "includes/1": "includes", "join/1": "join", "slice/1": "sliceFrom", "slice/2": "slice", "indexOf/1": "indexOfStr" };

export function lower(root, targets, { paths } = {}) {
  const files = [...new Set([...targets.map(t => join(root, t.split("::")[0])), ...(ts.sys.fileExists(join(root, "src/prelude.ts")) ? [join(root, "src/prelude.ts")] : [])])];
  const program = ts.createProgram(files, { strict: true, target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler, noEmit: true, ...(paths ? { baseUrl: root, paths } : {}) });
  const checker = program.getTypeChecker();
  const done = new Map();
  const info = {};
  const queue = [];
  const fnKey = d => d.__name ? d.__name.replace(/\W/g, "_") : `${relative(root, d.getSourceFile().fileName).replace(/\.tsx?$/, "").replace(/\W/g, "_")}_${d.__top ?? d.name.text}`;
  const resolve = id => {
    let s = checker.getSymbolAtLocation(id);
    if (s && s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s);
    return s;
  };

  const decls = new Map();
  const loopMeta = [];
  const lambdas = { count: 0 };
  const aliases = new Map();
  const classes = new Set();
  const extras = [];
  const parentOf = decl => decl.parent.heritageClauses?.[0]?.types[0].expression.getText();
  const classDecl = name => program.getSourceFiles().flatMap(f => f.statements.filter(s => ts.isClassDeclaration(s) && s.name?.text === name))[0];
  const preludeSym = m => {
    const f = program.getSourceFile(join(root, "src/prelude.ts"));
    const d = f.statements.find(s => ts.isFunctionDeclaration(s) && s.name.text === PRELUDE[m]);
    return d;
  };
  // A class is a table of methods, flattened so that a subclass lists what it inherits.
  function useClass(name) {
    if (classes.has(name)) return;
    classes.add(name);
    const c = classDecl(name), parent = c.heritageClauses?.[0]?.types[0].expression.getText();
    if (parent) useClass(parent);
    for (const m of c.members) {
      if (ts.isMethodDeclaration(m)) {
        m.__name = `${name}.${m.name.text}`; m.__this = true;
        aliases.set(m.__name, fnKey(m)); done.set(fnKey(m), null); queue.push(m);
      }
    }
    if (parent) for (const [k, v] of [...aliases]) {
      if (k.startsWith(`${parent}.`) && !aliases.has(`${name}.${k.slice(parent.length + 1)}`)) aliases.set(`${name}.${k.slice(parent.length + 1)}`, v);
    }
    const ctor = c.members.find(ts.isConstructorDeclaration);
    const initKey = `${name}.__init`;
    if (ctor) {
      ctor.__name = initKey; ctor.__this = true;
      aliases.set(initKey, fnKey(ctor)); done.set(fnKey(ctor), null); queue.push(ctor);
    } else if (parent && aliases.has(`${parent}.__init`)) aliases.set(initKey, aliases.get(`${parent}.__init`));
    const params = ctor ? ctor.parameters.map(p => p.name.text) : ["a", "b"];
    const tag = `[${[...name].map(x => x.charCodeAt(0)).join(", ")}]`;
    const newKey = `${name}_new`;
    aliases.set(`${name}.__new`, newKey);
    extras.push(`def ${newKey} : Fn := { params := [${params.map(lean).join(", ")}], body := [
    .set "this" (.record [("__class", .lit (.str ${tag}))]),
    ${aliases.has(initKey) ? `.expr (.call ${lean(initKey)} [.var "this", ${params.map(p => `.var ${lean(p)}`).join(", ")}]),\n    ` : ""}.ret (.var "this")] }`);
  }

  function lowerFn(decl) {
    const key = fnKey(decl);
    decls.set(key, decl);
    const scope = new Map(); // symbol -> unique name
    const taken = new Set();
    const bind = (id) => {
      const s = checker.getSymbolAtLocation(id);
      let n = id.text, i = 1;
      while (taken.has(n)) n = `${id.text}_${i++}`;
      taken.add(n); scope.set(s, n);
      return n;
    };
    let lambdaCount = 0;
    const prelude = [], defaults = [];
    const inner = decl.__env ?? null;          // variables of the enclosing function
    const captured = new Set();                // mutable variables a lambda shares: they live in a scope object
    const capturedConst = new Set();           // `const` variables, copied when the lambda is made
    const isConst = d => ts.isVariableDeclaration(d) && (d.parent.flags & ts.NodeFlags.Const) !== 0;
    let hasLambda = false;
    // An arrow written in place as an array method's callback runs here and now, in this
    // function's variables, so it needs no closure.
    const isFnExpr = n => ts.isArrowFunction(n) || ts.isFunctionExpression(n);
    const isInlineCb = n => {
      const c = n.parent;
      if (!ts.isCallExpression(c) || c.arguments[0] !== n || !ts.isPropertyAccessExpression(c.expression)) return false;
      const m = c.expression.name.text;
      return (HOF[m] || m === "reduce" || m === "forEach") && checker.isArrayType(checker.getTypeAtLocation(c.expression.expression));
    };
    const walk = (n, f) => { f(n); ts.forEachChild(n, c => walk(c, f)); };
    // A callback must not write outer variables: its writes wouldn't outlive the turn.
    const checkPure = cb => walk(cb.body, n => {
      const outer = id => { const d = resolve(id)?.valueDeclaration; return !d || !isInside(d, cb); };
      if (ts.isBinaryExpression(n) && ts.isAssignmentOperator(n.operatorToken.kind)) {
        const t = n.left;
        if (!ts.isIdentifier(t) || outer(t)) throw new Error("a callback that writes outside itself");
      }
      if ((ts.isPostfixUnaryExpression(n) || ts.isPrefixUnaryExpression(n)) && (n.operator === ts.SyntaxKind.PlusPlusToken || n.operator === ts.SyntaxKind.MinusMinusToken)) {
        if (!ts.isIdentifier(n.operand) || outer(n.operand)) throw new Error("a callback that writes outside itself");
      }
      if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && ["push", "pop", "shift", "unshift", "splice", "sort", "reverse"].includes(n.expression.name.text)) {
        const r = n.expression.expression;
        if (!ts.isIdentifier(r) || outer(r)) throw new Error("a callback that writes outside itself");
      }
    });
    // `xs.push(v)` as a new array is the same as JavaScript only if nothing else holds `xs`.
    const ownedArray = sym => {
      const d = sym?.valueDeclaration;
      if (!d || !ts.isVariableDeclaration(d) || !d.initializer) return false;
      let init = d.initializer;
      while (ts.isAsExpression(init) || ts.isParenthesizedExpression(init) || ts.isSatisfiesExpression(init)) init = init.expression;
      if (!ts.isArrayLiteralExpression(init)) return false;
      let ok = true;
      walk(decl.body, n => {
        if (!ts.isIdentifier(n) || n === d.name || resolve(n) !== sym) return;
        let u = n;
        while (ts.isParenthesizedExpression(u.parent) || ts.isAsExpression(u.parent) || ts.isNonNullExpression(u.parent)) u = u.parent;
        const p = u.parent;
        if (ts.isPropertyAccessExpression(p) && p.expression === u && (READS.has(p.name.text) || p.name.text === "push")) return;
        if (ts.isElementAccessExpression(p) && p.expression === u) {
          if (ts.isBinaryExpression(p.parent) && p.parent.left === p && ts.isAssignmentOperator(p.parent.operatorToken.kind)) ok = false;
          return;
        }
        if (ts.isReturnStatement(p) || ts.isSpreadElement(p)) return;
        if (ts.isForOfStatement(p) && p.expression === u) {
          walk(p.statement, m => { if (ts.isIdentifier(m) && resolve(m) === sym) ok = false; });
          return;
        }
        ok = false;
      });
      return ok;
    };
    const visitCapt = n => {
      if (ts.isArrowFunction(n) && !isInlineCb(n)) {
        hasLambda = true;
        const look = m => {
          if (ts.isIdentifier(m)) {
            const s = checker.getSymbolAtLocation(m);
            const d = s?.valueDeclaration;
            if (d && !isInside(d, n) && d.getSourceFile() === decl.getSourceFile() && (ts.isVariableDeclaration(d) || ts.isParameter(d)) && isInside(d, decl)) {
              (isConst(d) ? capturedConst : captured).add(s);
              (n.__const ??= new Set()); if (isConst(d)) n.__const.add(s);
            }
          }
          ts.forEachChild(m, look);
        };
        look(n.body);
      }
      ts.forEachChild(n, visitCapt);
    };
    const isInside = (d, n) => d.pos >= n.pos && d.end <= n.end;
    if (decl.body) visitCapt(decl.body);
    const params = decl.parameters.map((p, i) => {
      if (ts.isIdentifier(p.name)) {
        const n = bind(p.name);
        if (p.initializer) defaults.push([n, p.initializer]);
        return n;
      }
      const arg = `arg${i}`;
      taken.add(arg);
      for (const e of p.name.elements) prelude.push(`.set ${lean(bind(e.name))} (.field (.var ${lean(arg)}) ${lean(e.name.text)})`);
      return arg;
    });
    const loops = [];
    let cbCount = 0, inForEach = false;
    const callback = (fn, count) => {
      const name = `${key}_cb${cbCount++}`;
      if (isFnExpr(fn)) {
        if (fn.parameters.length !== count || !fn.parameters.every(p => ts.isIdentifier(p.name) && !p.initializer)) throw new Error("a callback with this parameter shape");
        checkPure(fn);
        const params = fn.parameters.map(p => bind(p.name));
        const body = [];
        if (ts.isBlock(fn.body)) S(fn.body, body); else body.push(`.ret (${E(fn.body)})`);
        done.set(name, `def ${name} : Fn := { params := [${params.map(lean).join(", ")}], body := [${body.join(", ")}] }`);
        decls.set(name, null);
        return name;
      }
      if (ts.isIdentifier(fn) && count === 1) {
        const d = resolve(fn)?.valueDeclaration;
        if (d && ts.isFunctionDeclaration(d) && d.parameters.length === 1) {
          if (!done.has(fnKey(d))) { done.set(fnKey(d), null); queue.push(d); }
          const x = `__cb${cbCount}`;
          done.set(name, `def ${name} : Fn := { params := [${lean(x)}], body := [.ret (.call ${lean(fnKey(d))} [.var ${lean(x)}])] }`);
          decls.set(name, null);
          return name;
        }
      }
      throw new Error("a callback that isn't written in place");
    };
    const idOf = sym => ({ __sym: sym });
    const E = e => {
      if (e.__sym) return scope.has(e.__sym) ? `.var ${lean(scope.get(e.__sym))}` : `.field (.var "__env") ${lean(e.__sym.name)}`;
      if (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isNonNullExpression(e) || ts.isSatisfiesExpression(e)) return E(e.expression);
      if (ts.isTemplateExpression(e)) {
        const part = x => {
          const t = checker.getTypeAtLocation(x);
          if (t.flags & ts.TypeFlags.String) return E(x);
          if (t.flags & ts.TypeFlags.NumberLike) return `.prim .numStr [${E(x)}]`;
          return `.prim .toText [${E(x)}]`;
        };
        const lit = t => `.lit (.str ${UNITS(t)})`;
        // Left-nested, as in the typed view.
        const items = [lit(e.head.text)];
        for (const span of e.templateSpans) items.push(part(span.expression), lit(span.literal.text));
        return items.reduce((sum, item) => `.bin .add (${sum}) (${item})`);
      }
      if (ts.isNumericLiteral(e)) return `.lit (.num ${num(Number(e.text.replace(/_/g, "")))})`;
      if (ts.isBigIntLiteral(e)) return `.lit (.big ${e.text.replace(/n$/, "").replace(/_/g, "")})`;
      if (e.kind === ts.SyntaxKind.TrueKeyword) return ".lit (.bool true)";
      if (e.kind === ts.SyntaxKind.FalseKeyword) return ".lit (.bool false)";
      if (e.kind === ts.SyntaxKind.NullKeyword) return ".lit .null";
      if (ts.isStringLiteralLike(e)) return `.lit (.str ${UNITS(e.text)})`;
      if (ts.isIdentifier(e)) {
        if (e.text === "undefined") return ".lit .undef";
        const s = resolve(e);
        if (decl.__const?.has(s)) return `.field (.var "__env") ${lean(e.text)}`;
        if (decl.__env?.has(s)) return `.field (.field (.var "__env") "__up") ${lean(e.text)}`;
        if (captured.has(s)) return `.field (.var "__scope") ${lean(e.text)}`;
        if (scope.has(s)) return `.var ${lean(scope.get(s))}`;
        const d = s?.valueDeclaration;
        if (d && ts.isVariableDeclaration(d) && d.initializer) return E(d.initializer); // module constant
        throw new Error(`unknown name ${e.text}`);
      }
      if (ts.isPropertyAccessExpression(e)) {
        const continues = ts.isOptionalChain(e) && !e.questionDotToken;
        if (continues) throw new Error("an optional chain that continues past `?.`");
        if (e.name.text === "length") {
          if (!e.questionDotToken) return `.length (${E(e.expression)})`;
          if (!ts.isIdentifier(e.expression)) throw new Error("`?.length` on an expression");
          return `.cond (.isNullish (${E(e.expression)})) (.lit .undef) (.length (${E(e.expression)}))`;
        }
        if (e.questionDotToken) return `.optField (${E(e.expression)}) ${lean(e.name.text)}`;
        return `.field (${E(e.expression)}) ${lean(e.name.text)}`;
      }
      if (ts.isElementAccessExpression(e)) return `.index (${E(e.expression)}) (${E(e.argumentExpression)})`;
      if (e.kind === ts.SyntaxKind.ThisKeyword) return `.var "this"`;
      if (ts.isArrowFunction(e)) {
        const name = `${key}_lambda${lambdaCount++}`;
        e.__env = captured; e.__name = name;
        queue.push(e); done.set(name, null);
        const copies = [...(e.__const ?? [])].map(c => `(${lean(c.name)}, ${E(ts.factory.createIdentifier(c.name) && idOf(c))})`);
        return `.closure ${lean(name)} (.record [("__up", .var "__scope")${copies.length ? ", " : ""}${copies.join(", ")}])`;
      }
      if (ts.isNewExpression(e)) { if (!classDecl(e.expression.getText())) throw new Error("`new` on a class outside this code"); useClass(e.expression.text); }
      if (ts.isNewExpression(e)) return `.call ${lean(`${e.expression.text}.__new`)} [${(e.arguments ?? []).map(E).join(", ")}]`;
      if (ts.isTypeOfExpression(e)) return `.typeOf (${E(e.expression)})`;
      if (ts.isConditionalExpression(e)) return `.cond (${E(e.condition)}) (${E(e.whenTrue)}) (${E(e.whenFalse)})`;
      if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.ExclamationToken) return `.not (${E(e.operand)})`;
      if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.MinusToken && ts.isNumericLiteral(e.operand) && Number(e.operand.text) !== 0) return `.lit (.num ${num(-Number(e.operand.text))})`;
      if (ts.isPrefixUnaryExpression(e) && e.operator === ts.SyntaxKind.MinusToken) return `.neg (${E(e.operand)})`;
      if (ts.isObjectLiteralExpression(e)) {
        const fields = e.properties.map(p => {
          if (ts.isShorthandPropertyAssignment(p)) return `(${lean(p.name.text)}, .var ${lean(scope.get(checker.getShorthandAssignmentValueSymbol(p)))})`;
          if (ts.isPropertyAssignment(p)) return `(${lean(p.name.text)}, ${E(p.initializer)})`;
          throw new Error("object shape");
        });
        return `.record [${fields.join(", ")}]`;
      }
      if (ts.isArrayLiteralExpression(e)) {
        if (!e.elements.some(ts.isSpreadElement)) return `.array [${e.elements.map(E).join(", ")}]`;
        // `[...a, b, ...c]`: a run of plain elements is an array of its own.
        const parts = [];
        let run = [];
        const flush = () => { if (run.length) parts.push(`.array [${run.join(", ")}]`); run = []; };
        for (const el of e.elements) {
          if (ts.isSpreadElement(el)) {
            if (!checker.isArrayType(checker.getTypeAtLocation(el.expression))) throw new Error("a spread of something other than an array");
            flush(); parts.push(E(el.expression));
          } else run.push(E(el));
        }
        flush();
        return parts.length === 1 ? `.prim .concat [${parts[0]}, .array []]` : parts.reduce((a, b) => `.prim .concat [${a}, ${b}]`);
      }
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && e.expression.expression.getText() === "Math" && MATH[e.expression.name.text]) {
        return `.math ${MATH[e.expression.name.text]} (${E(e.arguments[0])})`;
      }
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && e.expression.expression.getText() === "Math" && ["min", "max", "abs"].includes(e.expression.name.text)) {
        return `.prim .${e.expression.name.text} [${e.arguments.map(E).join(", ")}]`;
      }
      if (ts.isCallExpression(e) && e.expression.getText() === "String" && e.arguments.length === 1) return `.prim .numStr [${E(e.arguments[0])}]`;
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && !e.expression.questionDotToken && !e.questionDotToken
        && checker.isArrayType(checker.getTypeAtLocation(e.expression.expression))) {
        const m = e.expression.name.text, recv = e.expression.expression;
        if (HOF[m] && e.arguments.length === 1) return `.hof .${HOF[m]} (${E(recv)}) ${lean(callback(e.arguments[0], 1))}`;
        if (m === "reduce" && e.arguments.length === 2) return `.reduce (${E(recv)}) (${E(e.arguments[1])}) ${lean(callback(e.arguments[0], 2))}`;
      }
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && !e.expression.questionDotToken && !e.questionDotToken) {
        const m = `${e.expression.name.text}/${e.arguments.length}`, recv = e.expression.expression;
        const t = checker.getTypeAtLocation(recv);
        const table = t.flags & ts.TypeFlags.StringLike ? STRING_METHODS : checker.isArrayType(t) ? ARRAY_METHODS : null;
        if (table?.[m]) return `.prim .${table[m]} [${[recv, ...e.arguments].map(E).join(", ")}]`;
      }
      if (ts.isCallExpression(e) && e.expression.kind === ts.SyntaxKind.SuperKeyword) throw new Error("super call outside a constructor");
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && e.expression.expression.kind === ts.SyntaxKind.SuperKeyword) {
        return `.call ${lean(`${parentOf(decl)}.${e.expression.name.text}`)} [.var "this", ${e.arguments.map(E).join(", ")}]`.replace(", ]", "]");
      }
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression)) {
        const m = e.expression.name.text, o = e.expression.expression;
        const t = checker.getTypeAtLocation(o);
        if (checker.isArrayType(t) && PRELUDE[m] && !program.getSourceFile(join(root, "src/prelude.ts"))) throw new Error("a callback method on an array");
        if (checker.isArrayType(t) && PRELUDE[m]) {
          const d = preludeSym(m);
          if (!done.has(fnKey(d))) { done.set(fnKey(d), null); queue.push(d); }
          return `.call ${lean(fnKey(d))} [${[o, ...e.arguments].map(E).join(", ")}]`;
        }
        if (t.symbol?.flags & ts.SymbolFlags.Class) return `.callM (${E(o)}) ${lean(m)} [${e.arguments.map(E).join(", ")}]`;
        throw new Error(`method ${e.getText()}`);
      }
      if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
        let d = resolve(e.expression)?.valueDeclaration;
        if (d && ts.isVariableDeclaration(d) && d.initializer && (ts.isArrowFunction(d.initializer) || ts.isFunctionExpression(d.initializer)) && d.parent.parent.parent === d.getSourceFile()) {
          const f = d.initializer; f.__top = d.name.text; d = f;
        } else if (d && !ts.isFunctionDeclaration(d)) return `.callV (${E(e.expression)}) [${e.arguments.map(E).join(", ")}]`;
        if (!d || !(ts.isFunctionDeclaration(d) || ts.isArrowFunction(d) || ts.isFunctionExpression(d))) throw new Error(`call ${e.getText()}`);
        if (!done.has(fnKey(d))) { done.set(fnKey(d), null); queue.push(d); }
        // Missing arguments are `undefined`.
        const padded = [...e.arguments.map(E), ...d.parameters.slice(e.arguments.length).map(() => ".lit .undef")];
        return `.call ${lean(fnKey(d))} [${padded.join(", ")}]`;
      }
      if (ts.isBinaryExpression(e)) {
        const op = e.operatorToken.getText();
        if (op === "===" || op === "!==" ) {
          const isUndef = n => n.getText() === "undefined";
          void isUndef;
        }
        if (op === "??") return `.coalesce (${E(e.left)}) (${E(e.right)})`;
        if (op === "||") return `.or (${E(e.left)}) (${E(e.right)})`;
        if (op === "&&") return `.and (${E(e.left)}) (${E(e.right)})`;
        if ((op === "==" || op === "===") && e.right.kind === ts.SyntaxKind.NullKeyword && op === "==") return `.isNullish (${E(e.left)})`;
        if (op === "!=" && e.right.kind === ts.SyntaxKind.NullKeyword) return `.not (.isNullish (${E(e.left)}))`;
        if (OPS[op]) return `.bin .${OPS[op]} (${E(e.left)}) (${E(e.right)})`;
      }
      throw new Error(`expression: ${e.getText()}`);
    };
    const S = (s, out) => {
      if (s.__decls) { S({ declarationList: s.__decls, __var: true }, out); return; }
      if (s.__expr) { S({ expression: s.__expr, __stmt: true }, out); return; }
      if (s.__var) {
        for (const d of s.declarationList.declarations) {
          if (!ts.isIdentifier(d.name)) throw new Error("this declaration pattern");
          out.push(`.set ${lean(bind(d.name))} (${d.initializer ? E(d.initializer) : ".lit .undef"})`);
        }
        return;
      }
      if (s.__stmt) {
        const e = s.expression;
        if ((ts.isPostfixUnaryExpression(e) || ts.isPrefixUnaryExpression(e)) && ts.isIdentifier(e.operand) && (e.operator === ts.SyntaxKind.PlusPlusToken || e.operator === ts.SyntaxKind.MinusMinusToken)) {
          const n = lean(scope.get(resolve(e.operand)));
          out.push(`.set ${n} (.bin .${e.operator === ts.SyntaxKind.PlusPlusToken ? "add" : "sub"} (.var ${n}) (.lit (.num (F64.ofInt (1)))))`);
          return;
        }
        if (ts.isBinaryExpression(e)) {
          const { left, right, operatorToken: t } = e, op = t.getText();
          const value = op === "=" ? E(right) : op === "+=" ? `.bin .add (${E(left)}) (${E(right)})` : op === "-=" ? `.bin .sub (${E(left)}) (${E(right)})` : null;
          if (value === null || !ts.isIdentifier(left)) throw new Error("this `for` step");
          out.push(`.set ${lean(scope.get(resolve(left)))} (${value})`);
          return;
        }
        throw new Error("this `for` step");
      }
      if (ts.isBlock(s)) { for (const c of s.statements) S(c, out); return; }
      if (ts.isVariableStatement(s)) {
        for (const d of s.declarationList.declarations) {
          const v = d.initializer ? E(d.initializer) : ".lit .undef";
          if (ts.isObjectBindingPattern(d.name)) {
            const tmp = `__obj${d.pos}`;
            out.push(`.set ${lean(tmp)} (${v})`);
            for (const el of d.name.elements) {
              if (el.dotDotDotToken || el.initializer || !ts.isIdentifier(el.name)) throw new Error("this destructuring");
              out.push(`.set ${lean(bind(el.name))} (.field (.var ${lean(tmp)}) ${lean((el.propertyName ?? el.name).text)})`);
            }
            continue;
          }
          if (!ts.isIdentifier(d.name)) throw new Error("this declaration pattern");
          const sym = checker.getSymbolAtLocation(d.name);
          if (captured.has(sym)) out.push(`.setField (.var "__scope") ${lean(d.name.text)} (${v})`);
          else out.push(`.set ${lean(bind(d.name))} (${v})`);
        }
        return;
      }
      if (ts.isReturnStatement(s)) {
        if (inForEach) { if (s.expression) throw new Error("a value returned from `forEach`"); out.push(".cont"); return; }
        out.push(`.ret (${s.expression ? E(s.expression) : ".lit .undef"})`); return;
      }
      if (ts.isBreakStatement(s)) { if (s.label) throw new Error("a labelled `break`"); out.push(".brk"); return; }
      if (ts.isContinueStatement(s)) { if (s.label) throw new Error("a labelled `continue`"); out.push(".cont"); return; }
      if (ts.isThrowStatement(s)) {
        // The built-in errors have no behaviour a return value can see, and a bridge covers no thrown path.
        if (ts.isNewExpression(s.expression) && /^(Range|Type|Syntax|Reference|URI|Eval)?Error$/.test(s.expression.expression.getText())) { out.push(`.throw (.lit (.str ${UNITS("Error")}))`); return; }
        out.push(`.throw (${E(s.expression)})`); return;
      }
      if (ts.isIfStatement(s)) {
        const c = E(s.expression), t = [], f = [];
        S(s.thenStatement, t); if (s.elseStatement) S(s.elseStatement, f);
        out.push(`.ite (${c}) [${t.join(", ")}] [${f.join(", ")}]`); return;
      }
      if (ts.isSwitchStatement(s)) {
        const tmp = `__sw${s.pos}`;
        out.push(`.set ${lean(tmp)} (${E(s.expression)})`);
        const clauses = [...s.caseBlock.clauses];
        // Empty clauses fall through into the next one; anything else must end its own case.
        const chain = i => {
          if (i >= clauses.length) return "";
          let j = i, tests = [];
          while (true) {
            const c = clauses[j];
            if (ts.isDefaultClause(c)) throw new Error("`default` that shares a case");
            tests.push(`.bin .eq (.var ${lean(tmp)}) (${E(c.expression)})`);
            if (c.statements.length) break;
            j += 1;
            if (j >= clauses.length) throw new Error("an empty last case");
            if (ts.isDefaultClause(clauses[j]) && !clauses[j].statements.length) throw new Error("an empty `default`");
            if (ts.isDefaultClause(clauses[j])) break;
          }
          const body = [], stmts = [...(ts.isDefaultClause(clauses[j]) ? clauses[j] : clauses[j]).statements];
          if (stmts.at(-1) && ts.isBreakStatement(stmts.at(-1))) stmts.pop();
          else if (!(stmts.at(-1) && (ts.isReturnStatement(stmts.at(-1)) || ts.isThrowStatement(stmts.at(-1))))) throw new Error("a `case` that falls through");
          for (const c of stmts) S(c, body);
          const test = tests.reduceRight((rest, t) => rest === null ? t : `.or (${t}) (${rest})`, null);
          const next = clauses[j + 1];
          if (next && ts.isDefaultClause(next)) {
            const fin = []; const ds = [...next.statements];
            if (ds.at(-1) && ts.isBreakStatement(ds.at(-1))) ds.pop();
            for (const c of ds) S(c, fin);
            if (j + 2 < clauses.length) throw new Error("`default` before the last case");
            return `.ite (${test}) [${body.join(", ")}] [${fin.join(", ")}]`;
          }
          const rest = chain(j + 1);
          return `.ite (${test}) [${body.join(", ")}] [${rest}]`;
        };
        if (ts.isDefaultClause(clauses[0])) throw new Error("`default` first");
        out.push(chain(0));
        return;
      }
      if (ts.isEmptyStatement?.(s)) return;
      if (ts.isDoStatement(s)) throw new Error("`do` loops");
      if (ts.isForStatement(s) || ts.isWhileStatement(s)) {
        if (ts.isForStatement(s) && s.initializer) {
          if (!ts.isVariableDeclarationList(s.initializer)) throw new Error("this `for` initializer");
          S(ts.factory.createVariableStatement ? { __decls: s.initializer } : s, out);
        }
        const idx = loops.length; loops.push(null);
        const loop = `${key}_loop${idx}`;
        const test = ts.isWhileStatement(s) ? s.expression : s.condition;
        if (!test) throw new Error("a `for` with no condition");
        const c = E(test), body = [], step = [];
        S(s.statement, body);
        if (ts.isForStatement(s) && s.incrementor) S({ __expr: s.incrementor }, step);
        loops[idx] = `def ${loop} : List Stmt := [${body.join(", ")}]\n\ndef ${loop}_step : List Stmt := [${step.join(", ")}]`;
        loopMeta.push({ key, idx, name: loop, kind: "while", item: null, text: body.join(" ") + step.join(" ") });
        out.push(`.whileL (${c}) ${loop} ${loop}_step`); return;
      }
      if (ts.isTryStatement(s)) throw new Error("try");
      if (ts.isForOfStatement(s)) {
        const x = bind(s.initializer.declarations[0].name), arr = E(s.expression), body = [];
        const idx = loops.length; loops.push(null);
        S(s.statement, body);
        const loop = `${key}_loop${idx}`;
        const assigned = [...new Set(body.join(" ").match(/\.set "[^"]+"/g)?.map(m => m.slice(6, -1)) ?? [])];
        info[key] = { loop, item: x, carried: assigned.filter(v => taken.has(v) && v !== x) };
        loops[idx] = `def ${loop} : List Stmt := [${body.join(", ")}]`;
        loopMeta.push({ key, idx, name: loop, kind: "for", item: x, text: body.join(" ") });
        out.push(`.forOf ${lean(x)} (${arr}) ${loop}`); return;
      }
      if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression) && ts.isPropertyAccessExpression(s.expression.expression) && s.expression.expression.name.text === "pop") {
        out.push(`.pop (${E(s.expression.expression.expression)})`); return;
      }
      if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression) && s.expression.expression.getText() === "__stuck") {
        out.push(`.expr (.call "__stuck" [])`); return;
      }
      if (ts.isExpressionStatement(s) && ts.isAwaitExpression(s.expression)) { out.push(".await"); return; }
      if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression) && ts.isPropertyAccessExpression(s.expression.expression) && s.expression.expression.name.text === "forEach"
        && s.expression.arguments.length === 1 && isFnExpr(s.expression.arguments[0]) && checker.isArrayType(checker.getTypeAtLocation(s.expression.expression.expression))) {
        const fn = s.expression.arguments[0];
        if (fn.parameters.length !== 1 || !ts.isIdentifier(fn.parameters[0].name)) throw new Error("a `forEach` with this parameter shape");
        const x = bind(fn.parameters[0].name), arr = E(s.expression.expression.expression), body = [];
        const idx = loops.length; loops.push(null);
        const was = inForEach; inForEach = true;
        if (ts.isBlock(fn.body)) S(fn.body, body); else S({ expression: fn.body, __plain: true, kind: ts.SyntaxKind.ExpressionStatement }, body);
        inForEach = was;
        const loop = `${key}_loop${idx}`;
        loops[idx] = `def ${loop} : List Stmt := [${body.join(", ")}]`;
        loopMeta.push({ key, idx, name: loop, kind: "for", item: x, text: body.join(" ") });
        out.push(`.forOf ${lean(x)} (${arr}) ${loop}`); return;
      }
      if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression) && ts.isPropertyAccessExpression(s.expression.expression) && s.expression.expression.name.text === "push") {
        const r = s.expression.expression.expression;
        if (ts.isIdentifier(r) && scope.has(resolve(r)) && s.expression.arguments.length === 1 && ownedArray(resolve(r))) {
          const n = lean(scope.get(resolve(r)));
          out.push(`.set ${n} (.prim .append [.var ${n}, ${E(s.expression.arguments[0])}])`); return;
        }
        out.push(`.push (${E(s.expression.expression.expression)}) (${E(s.expression.arguments[0])})`); return;
      }
      if (ts.isExpressionStatement(s) && ts.isCallExpression(s.expression) && s.expression.expression.kind === ts.SyntaxKind.SuperKeyword) {
        out.push(`.expr (.call ${lean(`${parentOf(decl)}.__init`)} [.var "this", ${s.expression.arguments.map(E).join(", ")}])`.replace(", ])", "])")); return;
      }
      if (ts.isExpressionStatement(s) && (ts.isPostfixUnaryExpression(s.expression) || ts.isPrefixUnaryExpression(s.expression))) { S({ __expr: s.expression }, out); return; }
      if (ts.isExpressionStatement(s) && ts.isBinaryExpression(s.expression)) {
        const { left, right, operatorToken: t } = s.expression;
        const op = t.getText();
        const value = op === "=" ? E(right) : op === "+=" ? `.bin .add (${E(left)}) (${E(right)})` : op === "-=" ? `.bin .sub (${E(left)}) (${E(right)})` : null;
        if (value === null) throw new Error(`assignment ${op}`);
        const target = ts.isIdentifier(left) ? resolve(left) : null;
        if (target && decl.__env?.has(target)) out.push(`.setField (.field (.var "__env") "__up") ${lean(left.text)} (${value})`);
        else if (target && captured.has(target)) out.push(`.setField (.var "__scope") ${lean(left.text)} (${value})`);
        else if (ts.isIdentifier(left)) out.push(`.set ${lean(scope.get(resolve(left)))} (${value})`);
        else if (ts.isPropertyAccessExpression(left)) out.push(`.setField (${E(left.expression)}) ${lean(left.name.text)} (${value})`);
        else if (ts.isElementAccessExpression(left)) out.push(`.setIndex (${E(left.expression)}) (${E(left.argumentExpression)}) (${value})`);
        else throw new Error("assignment target");
        return;
      }
      if (ts.isExpressionStatement(s)) { out.push(`.expr (${E(s.expression)})`); return; }
      throw new Error(`statement: ${s.getText()}`);
    };
    if (decl.__env) params.unshift("__env");
    if (decl.__this) params.unshift("this");
    const body = [...prelude];
    for (const [n, init] of defaults) body.push(`.ite (.bin .eq (.var ${lean(n)}) (.lit .undef)) [.set ${lean(n)} (${E(init)})] []`);
    if (hasLambda) body.push(`.set "__scope" (.record [${[...decl.parameters].filter(p => captured.has(checker.getSymbolAtLocation(p.name))).map(p => `(${lean(p.name.text)}, .var ${lean(p.name.text)})`).join(", ")}])`);
    if (ts.isBlock(decl.body)) S(decl.body, body); else body.push(`.ret (${E(decl.body)})`);
    if (body.includes(".await") || decl.modifiers?.some(m => m.kind === ts.SyntaxKind.AsyncKeyword)) {
      const segs = [[]];
      for (const b of body) { if (b === ".await") segs.push([]); else segs.at(-1).push(b); }
      done.set(key, `def ${key}_segs : List (List Stmt) := [${segs.map(g => `[${g.join(", ")}]`).join(",\n  ")}]\n\ndef ${key} : Fn := { params := [${params.map(lean).join(", ")}], body := [] }`);
      return;
    }
    done.set(key, `${loops.map(l => `${l}\n\n`).join("")}def ${key} : Fn := { params := [${params.map(lean).join(", ")}], body := [\n    ${body.join(",\n    ")}] }`);
  }

  const names = {};
  for (const t of targets) {
    const [file, name] = t.split("::");
    const sf = program.getSourceFile(join(root, file));
    let decl = sf.statements.find(s => ts.isFunctionDeclaration(s) && s.name?.text === name);
    if (!decl) {
      const v = sf.statements.filter(ts.isVariableStatement).flatMap(s => s.declarationList.declarations).find(d => d.name.getText() === name);
      const f = v?.initializer && (ts.isArrowFunction(v.initializer) || ts.isFunctionExpression(v.initializer)) ? v.initializer : null;
      if (!f) throw new Error(`no ${t}`);
      f.__top = name; decl = f;
    }
    names[t] = fnKey(decl);
    if (!done.has(fnKey(decl))) { done.set(fnKey(decl), null); queue.push(decl); }
  }
  while (queue.length) lowerFn(queue.shift());
  const defs = [...done.values(), ...extras];
  const prog = `def prog : Prog := fun fname => match fname with\n${[...done.keys()].map(k => `  | ${lean(k)} => some ${k}`).concat([...aliases].filter(([k]) => !done.has(k)).map(([k, v]) => `  | ${lean(k)} => some ${v}`)).join("\n")}\n  | _ => none`;
  const sources = [...decls].filter(([, d]) => d).map(([key, d]) => ({ key, file: relative(root, d.getSourceFile().fileName), name: d.__top ?? d.name.text }));
  // Every variable a loop can assign, through the loops nested in it.
  const defsOf = name => { const m = loopMeta.find(l => l.name === name); return m ? m.text : ""; };
  for (const l of loopMeta) {
    const seen = new Set([l.name]);
    let text = l.text;
    for (let grew = true; grew;) {
      grew = false;
      for (const m of text.matchAll(/\b(\w+_loop\d+)\b/g)) if (!seen.has(m[1])) { seen.add(m[1]); text += " " + defsOf(m[1]); grew = true; }
    }
    l.W = [...new Set([...(l.item ? [l.item] : []), ...[...text.matchAll(/\.set "([^"]+)"/g)].map(m => m[1])])];
    delete l.text;
  }
  return { names, info, sources, loops: loopMeta, lean: `import Core\nopen Core\nset_option maxRecDepth 100000\nnamespace Gen\n\n${defs.join("\n\n")}\n\n${prog}\n\nend Gen\n` };
}
