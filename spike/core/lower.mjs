// TypeScript to Core. A spike: it handles what the sample functions use and refuses
// the rest. It reads types only to choose `==` forms, so it knows nothing about Lean.
import ts from "/Users/nhestrompia/.t3/worktrees/proofci/typescript-support/typescript/node_modules/typescript/lib/typescript.js";
import { dirname, join, relative } from "node:path";

const OPS = { "+": "add", "-": "sub", "*": "mul", "<": "lt", "<=": "le", ">": "gt", ">=": "ge", "===": "eq", "!==": "ne", "/": "div", "%": "rem" };
const lean = s => JSON.stringify(s);
const bits = new DataView(new ArrayBuffer(8));
const num = x => {
  if (Number.isSafeInteger(x) && !Object.is(x, -0)) return `(F64.ofInt (${x}))`;
  bits.setFloat64(0, x);
  return `(F64.ofBits ${bits.getBigUint64(0)})`;
};
const MATH = { floor: "F64.floor", ceil: "F64.ceil", trunc: "F64.trunc" };

export function lower(root, targets) {
  const files = [...new Set(targets.map(t => join(root, t.split("::")[0])))];
  const program = ts.createProgram(files, { strict: true, target: ts.ScriptTarget.ES2022, module: ts.ModuleKind.ESNext, moduleResolution: ts.ModuleResolutionKind.Bundler, noEmit: true });
  const checker = program.getTypeChecker();
  const done = new Map();
  const info = {};
  const queue = [];
  const fnKey = d => `${relative(root, d.getSourceFile().fileName).replace(/\.tsx?$/, "").replace(/\W/g, "_")}_${d.name.text}`;
  const resolve = id => {
    let s = checker.getSymbolAtLocation(id);
    if (s && s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s);
    return s;
  };

  function lowerFn(decl) {
    const key = fnKey(decl);
    const scope = new Map(); // symbol -> unique name
    const taken = new Set();
    const bind = (id) => {
      const s = checker.getSymbolAtLocation(id);
      let n = id.text, i = 1;
      while (taken.has(n)) n = `${id.text}_${i++}`;
      taken.add(n); scope.set(s, n);
      return n;
    };
    const prelude = [];
    const params = decl.parameters.map((p, i) => {
      if (ts.isIdentifier(p.name)) return bind(p.name);
      const arg = `arg${i}`;
      taken.add(arg);
      for (const e of p.name.elements) prelude.push(`.set ${lean(bind(e.name))} (.field (.var ${lean(arg)}) ${lean(e.name.text)})`);
      return arg;
    });
    const loops = [];
    const E = e => {
      if (ts.isParenthesizedExpression(e) || ts.isAsExpression(e) || ts.isNonNullExpression(e)) return E(e.expression);
      if (ts.isNumericLiteral(e)) return `.lit (.num ${num(Number(e.text.replace(/_/g, "")))})`;
      if (ts.isBigIntLiteral(e)) return `.lit (.big ${e.text.replace(/n$/, "").replace(/_/g, "")})`;
      if (e.kind === ts.SyntaxKind.TrueKeyword) return ".lit (.bool true)";
      if (e.kind === ts.SyntaxKind.FalseKeyword) return ".lit (.bool false)";
      if (e.kind === ts.SyntaxKind.NullKeyword) return ".lit .null";
      if (ts.isStringLiteralLike(e)) return `.lit (.str [${[...e.text].map(c => c.charCodeAt(0)).join(", ")}])`;
      if (ts.isIdentifier(e)) {
        if (e.text === "undefined") return ".lit .undef";
        const s = resolve(e);
        if (scope.has(s)) return `.var ${lean(scope.get(s))}`;
        const d = s?.valueDeclaration;
        if (d && ts.isVariableDeclaration(d) && d.initializer) return E(d.initializer); // module constant
        throw new Error(`unknown name ${e.text}`);
      }
      if (ts.isPropertyAccessExpression(e)) {
        if (e.name.text === "length") return `.length (${E(e.expression)})`;
        return `.field (${E(e.expression)}) ${lean(e.name.text)}`;
      }
      if (ts.isElementAccessExpression(e)) return `.index (${E(e.expression)}) (${E(e.argumentExpression)})`;
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
      if (ts.isArrayLiteralExpression(e)) return `.array [${e.elements.map(E).join(", ")}]`;
      if (ts.isCallExpression(e) && ts.isPropertyAccessExpression(e.expression) && e.expression.expression.getText() === "Math" && MATH[e.expression.name.text]) {
        return `.math ${MATH[e.expression.name.text]} (${E(e.arguments[0])})`;
      }
      if (ts.isCallExpression(e) && ts.isIdentifier(e.expression)) {
        const d = resolve(e.expression)?.valueDeclaration;
        if (!d || !ts.isFunctionDeclaration(d)) throw new Error(`call ${e.getText()}`);
        if (!done.has(fnKey(d))) { done.set(fnKey(d), null); queue.push(d); }
        return `.call ${lean(fnKey(d))} [${e.arguments.map(E).join(", ")}]`;
      }
      if (ts.isBinaryExpression(e)) {
        const op = e.operatorToken.getText();
        if (op === "||") return `.or (${E(e.left)}) (${E(e.right)})`;
        if (op === "&&") return `.and (${E(e.left)}) (${E(e.right)})`;
        if ((op === "==" || op === "===") && e.right.kind === ts.SyntaxKind.NullKeyword && op === "==") return `.isNullish (${E(e.left)})`;
        if (op === "!=" && e.right.kind === ts.SyntaxKind.NullKeyword) return `.not (.isNullish (${E(e.left)}))`;
        if (OPS[op]) return `.bin .${OPS[op]} (${E(e.left)}) (${E(e.right)})`;
      }
      throw new Error(`expression: ${e.getText()}`);
    };
    const S = (s, out) => {
      if (ts.isBlock(s)) { for (const c of s.statements) S(c, out); return; }
      if (ts.isVariableStatement(s)) {
        for (const d of s.declarationList.declarations) {
          const v = E(d.initializer); out.push(`.set ${lean(bind(d.name))} (${v})`);
        }
        return;
      }
      if (ts.isReturnStatement(s)) { out.push(`.ret (${s.expression ? E(s.expression) : ".lit .undef"})`); return; }
      if (ts.isBreakStatement(s)) { out.push(".brk"); return; }
      if (ts.isThrowStatement(s)) { out.push(`.throw (${E(s.expression)})`); return; }
      if (ts.isIfStatement(s)) {
        const c = E(s.expression), t = [], f = [];
        S(s.thenStatement, t); if (s.elseStatement) S(s.elseStatement, f);
        out.push(`.ite (${c}) [${t.join(", ")}] [${f.join(", ")}]`); return;
      }
      if (ts.isForOfStatement(s)) {
        const x = bind(s.initializer.declarations[0].name), arr = E(s.expression), body = [];
        S(s.statement, body);
        const loop = `${key}_loop${loops.length}`;
        const assigned = [...new Set(body.join(" ").match(/\.set "[^"]+"/g)?.map(m => m.slice(6, -1)) ?? [])];
        info[key] = { loop, item: x, carried: assigned.filter(v => taken.has(v) && v !== x) };
        loops.push(`def ${loop} : List Stmt := [${body.join(", ")}]`);
        out.push(`.forOf ${lean(x)} (${arr}) ${loop}`); return;
      }
      if (ts.isExpressionStatement(s) && ts.isBinaryExpression(s.expression)) {
        const { left, right, operatorToken: t } = s.expression;
        const op = t.getText();
        const value = op === "=" ? E(right) : op === "+=" ? `.bin .add (${E(left)}) (${E(right)})` : op === "-=" ? `.bin .sub (${E(left)}) (${E(right)})` : null;
        if (value === null) throw new Error(`assignment ${op}`);
        if (ts.isIdentifier(left)) out.push(`.set ${lean(scope.get(resolve(left)))} (${value})`);
        else if (ts.isPropertyAccessExpression(left)) out.push(`.setField (${E(left.expression)}) ${lean(left.name.text)} (${value})`);
        else if (ts.isElementAccessExpression(left)) out.push(`.setIndex (${E(left.expression)}) (${E(left.argumentExpression)}) (${value})`);
        else throw new Error("assignment target");
        return;
      }
      if (ts.isExpressionStatement(s)) { out.push(`.expr (${E(s.expression)})`); return; }
      throw new Error(`statement: ${s.getText()}`);
    };
    const body = [...prelude];
    S(decl.body, body);
    done.set(key, `${loops.map(l => `${l}\n\n`).join("")}def ${key} : Fn := { params := [${params.map(lean).join(", ")}], body := [\n    ${body.join(",\n    ")}] }`);
  }

  const names = {};
  for (const t of targets) {
    const [file, name] = t.split("::");
    const sf = program.getSourceFile(join(root, file));
    const decl = sf.statements.find(s => ts.isFunctionDeclaration(s) && s.name?.text === name);
    if (!decl) throw new Error(`no ${t}`);
    names[t] = fnKey(decl);
    if (!done.has(fnKey(decl))) { done.set(fnKey(decl), null); queue.push(decl); }
  }
  while (queue.length) lowerFn(queue.shift());
  const defs = [...done.values()];
  const prog = `def prog : Prog := fun name => match name with\n${[...done.keys()].map(k => `  | ${lean(k)} => some ${k}`).join("\n")}\n  | _ => none`;
  return { names, info, lean: `import Core\nopen Core\nset_option maxRecDepth 4000\nnamespace Gen\n\n${defs.join("\n\n")}\n\n${prog}\n\nend Gen\n` };
}
