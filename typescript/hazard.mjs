// What the sequential reading of an `async` function must not meet, and what it rests on.
//
// An `async` function is checked and proved as if nothing else ran between its `await`s.
// Other tasks may change the world (a database, the network, the clock): the model answers
// every outside call from an arbitrary oracle, so those changes are covered. They may not
// change *in-process* state the function reads after an `await`, because then the function
// would see a value its own steps never wrote. This file is the rule, written once, and used
// by the translator and by the lowering to Core. Both are trusted, so the rule is kept small
// and purely syntactic.
//
// The rule (H1): after an `await`, the function reads no variable declared outside it unless
// that variable is a `const` (or an import, a function, a class) of an immutable type.
// "After" means later in the source, or anywhere in a loop that contains an `await`.
//
// What it cannot check, and reports instead (A1, "arguments are not mutated while a call is
// pending"): after an `await`, the function reads a parameter, or something derived from one,
// whose type is not primitive and not readonly. If the caller changed that object meanwhile,
// the function would see it. Primitives and `Readonly` types need no assumption.

import { appendFileSync, readdirSync, readFileSync, realpathSync } from "node:fs";
import { join, sep } from "node:path";

const flag = (ts, type, f) => Boolean(type.flags & f);

export function createHazards(ts, checker, program, root) {
  const isFunctionLike = ts.isFunctionLike;

  // Immutable all the way down: nothing reachable from a value of this type can be changed.
  const immutable = (type, seen = new Set()) => {
    if (seen.has(type)) return true;
    seen.add(type);
    const F = ts.TypeFlags;
    if (flag(ts, type, F.StringLike | F.NumberLike | F.BooleanLike | F.BigIntLike | F.Null | F.Undefined | F.Void | F.Never | F.EnumLike)) return true;
    if (flag(ts, type, F.Any | F.Unknown | F.TypeParameter | F.Instantiable)) return false;
    if (type.isUnionOrIntersection()) return type.types.every(t => immutable(t, seen));
    if (checker.isTupleType(type)) return Boolean(type.target.readonly) && checker.getTypeArguments(type).every(t => immutable(t, seen));
    const name = type.symbol?.name;
    // `readonly T[]` is a ReadonlyArray, and `isArrayType` is true for it as well.
    if (name === "ReadonlyArray") return checker.getTypeArguments(type).every(t => immutable(t, seen));
    if (checker.isArrayType(type)) return false;
    if (name === "ReadonlySet") return checker.getTypeArguments(type).every(t => immutable(t, seen));
    if (name === "ReadonlyMap") return checker.getTypeArguments(type).every(t => immutable(t, seen));
    if (type.getCallSignatures().length && !checker.getPropertiesOfType(type).length) return true;
    if (flag(ts, type, F.Object)) {
      if (["Array", "Set", "Map", "WeakMap", "WeakSet", "Date", "RegExp"].includes(name)) return false;
      if (checker.getIndexInfosOfType(type).some(i => !i.isReadonly || !immutable(i.type, seen))) return false;
      return checker.getPropertiesOfType(type).every(p => {
        const readonly = (ts.getCheckFlags?.(p) & ts.CheckFlags?.Readonly) || p.declarations?.some(d => (ts.getCombinedModifierFlags(d) & ts.ModifierFlags.Readonly) !== 0);
        const t = checker.getTypeOfSymbol(p);
        return Boolean(readonly) && immutable(t, seen);
      });
    }
    return false;
  };


  // ---- H2: a module-level `const` that nothing changes ------------------------------------------------------
  //
  // A `const` table such as `const LIMITS = { free: 10, pro: 100 }` has a mutable type, so `immutable` above
  // refuses it, yet nothing ever changes it and reading it after an `await` is harmless. It is accepted when
  // BOTH hold, and only then:
  //   (1) its initializer builds fresh data: literals, object and array literals of such data, `as const`,
  //       `Object.freeze` of such data, `new Set`/`new Map` of such data, or any expression whose type is a
  //       primitive (a snapshot of a primitive taken once, when the module loads). A table that holds
  //       something else (a function result, a class instance, another variable) may be changed through
  //       that other thing, so it is not accepted;
  //   (2) every use of it anywhere in the program is a read. `uses` below walks them all (the file for a
  //       private binding, every file that names it for an exported one) and is deny-by-default: a use is
  //       fine only if it is one of the forms listed in `flows`; anything else (an assignment, `delete`, `++`,
  //       a method not on the list such as `push`/`set`/`sort`, being passed to a function, returned, stored)
  //       makes the table "touched" and the read is refused as before. An element or property that is read
  //       into a variable is followed: its uses must be reads too.
  // The write and the read-after-`await` can then never meet. The argument is local to the program: code
  // outside it (a package that imports an exported table) could still change one. For an exported table
  // the function records that in `constants` and the report lists it as an assumption.
  const READ_METHODS = new Set(["map", "filter", "find", "findIndex", "findLast", "findLastIndex", "some", "every", "includes",
    "indexOf", "lastIndexOf", "join", "slice", "concat", "reduce", "reduceRight", "forEach", "at", "flat", "flatMap",
    "entries", "keys", "values", "has", "get", "toString", "toSorted", "toReversed"]);
  const PURE_GLOBALS = { Object: new Set(["keys", "values", "entries", "freeze", "isFrozen", "hasOwn", "fromEntries"]),
    Array: new Set(["isArray", "from"]), JSON: new Set(["stringify"]) };
  const SCALARS = new Set(["String", "Number", "Boolean"]);

  const untouchedMemo = new Map();
  const untouched = d => {
    if (untouchedMemo.has(d)) return untouchedMemo.get(d);
    untouchedMemo.set(d, false); // a cycle is not a proof
    let verdict = { ok: false, exported: false };
    try { verdict = constantTable(d); } catch { verdict = { ok: false, exported: false }; }
    untouchedMemo.set(d, verdict);
    return verdict;
  };

  const stripType = n => {
    while (ts.isParenthesizedExpression(n) || ts.isAsExpression(n) || ts.isSatisfiesExpression?.(n) || ts.isTypeAssertionExpression(n) || ts.isNonNullExpression(n)) n = n.expression;
    return n;
  };
  const freshData = n => {
    n = stripType(n);
    if (immutable(checker.getTypeAtLocation(n)) && !ts.isObjectLiteralExpression(n) && !ts.isArrayLiteralExpression(n)) return true;
    if (ts.isObjectLiteralExpression(n)) {
      return n.properties.every(p => ts.isPropertyAssignment(p) && !ts.isPrivateIdentifier(p.name) && (!ts.isComputedPropertyName(p.name) || immutable(checker.getTypeAtLocation(p.name.expression))) && freshData(p.initializer));
    }
    if (ts.isArrayLiteralExpression(n)) return n.elements.every(e => !ts.isSpreadElement(e) && !ts.isOmittedExpression(e) && freshData(e));
    if (ts.isCallExpression(n) && ts.isPropertyAccessExpression(n.expression) && ts.isIdentifier(n.expression.expression)
      && n.expression.expression.text === "Object" && n.expression.name.text === "freeze" && libraryName(n.expression.expression) && n.arguments.length === 1) return freshData(n.arguments[0]);
    if (ts.isNewExpression(n) && ts.isIdentifier(n.expression) && (n.expression.text === "Set" || n.expression.text === "Map") && libraryName(n.expression)) {
      return !n.arguments?.length || (n.arguments.length === 1 && freshData(n.arguments[0]));
    }
    return false;
  };
  const libraryName = id => {
    const s = checker.getSymbolAtLocation(id);
    return Boolean(s?.declarations?.length) && s.declarations.every(x => program.isSourceFileDefaultLibrary(x.getSourceFile()));
  };

  const assignmentTarget = n => {
    for (;;) {
      const p = n.parent;
      if (!p) return false;
      if (ts.isParenthesizedExpression(p) || ts.isNonNullExpression(p) || ts.isAsExpression(p) || ts.isSatisfiesExpression?.(p)) { n = p; continue; }
      if (ts.isBinaryExpression(p)) return p.left === n && ts.isAssignmentOperator(p.operatorToken.kind);
      if ((ts.isPrefixUnaryExpression(p) || ts.isPostfixUnaryExpression(p))) return p.operator === ts.SyntaxKind.PlusPlusToken || p.operator === ts.SyntaxKind.MinusMinusToken;
      if (ts.isDeleteExpression(p)) return true;
      if (ts.isForInStatement(p) || ts.isForOfStatement(p)) return p.initializer === n;
      if (ts.isArrayLiteralExpression(p) || ts.isSpreadElement(p) || ts.isSpreadAssignment(p) || ts.isObjectLiteralExpression(p)) { n = p; continue; }
      if (ts.isPropertyAssignment(p) && p.initializer === n) { n = p.parent; continue; }
      if (ts.isShorthandPropertyAssignment(p)) { n = p.parent; continue; }
      return false;
    }
  };

  const inTypePosition = n => { for (let p = n.parent; p; p = p.parent) { if (ts.isTypeNode(p)) return true; if (ts.isStatement(p)) return false; } return false; };

  // The identifiers that stand for `symbol` inside `scope`.
  const identifiersOf = (scope, symbol) => {
    const found = [];
    const walk = n => {
      if (ts.isIdentifier(n) && n.text === symbol.name) {
        const at = ts.isShorthandPropertyAssignment(n.parent) && n.parent.name === n ? checker.getShorthandAssignmentValueSymbol(n.parent) : checker.getSymbolAtLocation(n);
        if (at === symbol || (at?.flags & ts.SymbolFlags.Alias && checker.getAliasedSymbol(at) === symbol)) found.push(n);
      }
      ts.forEachChild(n, walk);
    };
    walk(scope);
    return found;
  };

  // A table's value, or part of it, appears as `node`. Is every way it is used a read?
  function makeFlows() {
    const visiting = new Set();
    const followName = (name, scope, depth) => {
      if (ts.isIdentifier(name)) {
        const s = checker.getSymbolAtLocation(name);
        if (!s) return false;
        if (visiting.has(s)) return true;
        visiting.add(s);
        const ok = identifiersOf(scope, s).every(id => id === name || inTypePosition(id) || flows(id, depth + 1));
        visiting.delete(s);
        return ok;
      }
      if (ts.isObjectBindingPattern(name) || ts.isArrayBindingPattern(name)) {
        return name.elements.every(e => ts.isOmittedExpression(e) || (!e.dotDotDotToken || false) && followName(e.name, scope, depth));
      }
      return false;
    };
    const scopeOf = n => { for (let p = n.parent; p; p = p.parent) if (isFunctionLike(p) || ts.isSourceFile(p)) return p; return undefined; };
    function flows(node, depth = 0) {
      if (depth > 8) return false;
      const type = checker.getTypeAtLocation(node);
      if (immutable(type)) return !assignmentTarget(node);
      const p = node.parent;
      if (!p) return false;
      if (ts.isParenthesizedExpression(p) || ts.isNonNullExpression(p) || ts.isAsExpression(p) || ts.isSatisfiesExpression?.(p) || ts.isTypeAssertionExpression(p)) return flows(p, depth);
      if (ts.isPropertyAccessExpression(p) && p.expression === node) {
        const call = p.parent;
        if (ts.isCallExpression(call) && call.expression === p) {
          if (!READ_METHODS.has(p.name.text)) return false;
          const reduces = p.name.text === "reduce" || p.name.text === "reduceRight";
          for (const [i, a] of call.arguments.entries()) {
            const arg = stripType(a);
            if (ts.isArrowFunction(arg) || ts.isFunctionExpression(arg)) {
              if (arg.body && (ts.isBlock(arg.body) ? false : false)) return false;
              for (const [j, param] of arg.parameters.entries()) {
                if (reduces && call.arguments.length > 1 && j === 0) continue;
                if (!followName(param.name, arg, depth)) return false;
              }
              // what the callback returns is an ordinary expression; a returned element is refused where it is returned
            } else if (checker.getTypeAtLocation(arg).getCallSignatures().length) return false;
          }
          return flows(call, depth + 1);
        }
        return flows(p, depth + 1);
      }
      if (ts.isElementAccessExpression(p)) return p.expression === node ? flows(p, depth + 1) : false;
      if (ts.isForOfStatement(p) && p.expression === node) {
        const init = p.initializer;
        return ts.isVariableDeclarationList(init) && init.declarations.length === 1 && followName(init.declarations[0].name, p, depth);
      }
      if (ts.isForInStatement(p) && p.expression === node) return true;
      if (ts.isBinaryExpression(p)) {
        const k = p.operatorToken.kind, K = ts.SyntaxKind;
        if (k === K.InKeyword && p.right === node) return true;
        if (k === K.InstanceOfKeyword && p.left === node) return true;
        if ([K.EqualsEqualsToken, K.EqualsEqualsEqualsToken, K.ExclamationEqualsToken, K.ExclamationEqualsEqualsToken].includes(k)) return true;
        if ([K.BarBarToken, K.AmpersandAmpersandToken, K.QuestionQuestionToken].includes(k)) return flows(p, depth + 1);
        return false;
      }
      if (ts.isConditionalExpression(p)) return p.condition === node ? true : flows(p, depth + 1);
      if (ts.isPrefixUnaryExpression(p)) return p.operator === ts.SyntaxKind.ExclamationToken;
      if (ts.isTypeOfExpression(p) || ts.isExpressionStatement(p) || ts.isTemplateSpan(p)) return true;
      if ((ts.isIfStatement(p) || ts.isWhileStatement(p) || ts.isDoStatement(p)) && p.expression === node) return true;
      if (ts.isVariableDeclaration(p) && p.initializer === node) return followName(p.name, scopeOf(p), depth);
      if (ts.isSpreadElement(p) && p.expression === node) {
        const elements = checker.isArrayType(type) || checker.isTupleType(type) ? checker.getTypeArguments(type) : [];
        return elements.length > 0 && elements.every(t => immutable(t));
      }
      if (ts.isSpreadAssignment(p) && p.expression === node) return checker.getPropertiesOfType(type).every(x => immutable(checker.getTypeOfSymbol(x))) && !checker.getIndexInfosOfType(type).some(i => !immutable(i.type));
      if (ts.isCallExpression(p) && p.arguments.includes(node) && ts.isPropertyAccessExpression(p.expression) && ts.isIdentifier(p.expression.expression)) {
        const owner = p.expression.expression.text, method = p.expression.name.text;
        if (libraryName(p.expression.expression) && PURE_GLOBALS[owner]?.has(method)) {
          return ["keys", "isArray", "stringify", "isFrozen", "hasOwn"].includes(method) ? true : flows(p, depth + 1);
        }
      }
      if (ts.isCallExpression(p) && p.arguments.includes(node) && ts.isIdentifier(p.expression) && SCALARS.has(p.expression.text) && libraryName(p.expression)) return true;
      return false;
    }
    return flows;
  }

  // Every source file of the package, for the one question "does this file name the table?".
  let packageFiles;
  const sourcesOfPackage = () => {
    if (packageFiles) return packageFiles;
    packageFiles = [];
    if (!root) return packageFiles;
    const skip = new Set(["node_modules", ".git", "dist", "build", "out", "coverage", ".next", ".turbo", "target", "__tests__", "__mocks__"]);
    const walk = dir => {
      let entries;
      try { entries = readdirSync(dir, { withFileTypes: true }); } catch { return; }
      for (const e of entries) {
        if (e.isDirectory()) { if (!skip.has(e.name)) walk(join(dir, e.name)); }
        else if (/\.(?:[cm]?[jt]sx?)$/.test(e.name) && !e.name.endsWith(".d.ts") && !/\.(?:test|spec|stories|e2e)\.[cm]?[jt]sx?$/.test(e.name)) packageFiles.push(join(dir, e.name));
      }
    };
    walk(root);
    return packageFiles;
  };

  function constantTable(d) {
    const no = exported => ({ ok: false, exported });
    if (!d.initializer || !ts.isIdentifier(d.name) || d.getSourceFile().isDeclarationFile) return no(false);
    if (!freshData(d.initializer)) return no(false);
    const symbol = checker.getSymbolAtLocation(d.name);
    if (!symbol) return no(false);
    const source = d.getSourceFile();
    const named = symbol.name;
    const specifiers = source.statements.filter(st => ts.isExportDeclaration(st) && !st.moduleSpecifier && st.exportClause && ts.isNamedExports(st.exportClause))
      .flatMap(st => st.exportClause.elements).filter(e => (e.propertyName ?? e.name).text === named);
    if (specifiers.some(e => e.propertyName)) return no(true); // exported under another name
    const exported = (ts.getCombinedModifierFlags(d) & ts.ModifierFlags.Export) !== 0 || specifiers.length > 0;
    const flows = makeFlows();

    // An exported table can be used from any file of the package. Those in the program are read here.
    // A file that is not in the program and imports this module (or re-exports from it, which is how a
    // barrel file hands it on) could change it unseen, so the table is refused. Test files are not part
    // of the program that runs. What this cannot see (a package whose `exports` map renames the file) is
    // the assumption the report lists for every exported table.
    if (exported) {
      const here = realpathSync(source.fileName);
      if (!root || !here.startsWith(root + sep)) return no(true);
      const inProgram = new Set(program.getSourceFiles().map(f => { try { return realpathSync(f.fileName); } catch { return f.fileName; } }));
      const parts = here.replace(/\.[cm]?[jt]sx?$/, "").split(sep);
      const base = (parts.at(-1) === "index" ? parts.at(-2) : parts.at(-1)).replace(/[.*+?^${}()|[\]\\]/g, "\\$&");
      const reaches = new RegExp(`(?:from\\s*|import\\s*\\(\\s*|require\\s*\\(\\s*|import\\s*)['"\`][^'"\`]*(?:/|(?<=['"\`]))${base}(?:/index)?(?:\\.[cm]?[jt]sx?|\\.js)?['"\`]`);
      for (const file of sourcesOfPackage()) {
        if (inProgram.has(file) || file === here) continue;
        let text;
        try { text = readFileSync(file, "utf8"); } catch { return no(true); }
        if (reaches.test(text)) return no(true);
      }
    }

    const files = exported ? program.getSourceFiles().filter(f => !f.isDeclarationFile && (f === source || f.text.includes(named) || /import\s+(?:type\s+)?\*\s+as\s/.test(f.text))) : [source];
    for (const file of files) {
      const names = new Set([named]);
      for (const statement of file.statements) {
        if (!ts.isImportDeclaration(statement) || !statement.importClause?.namedBindings) continue;
        const bindings = statement.importClause.namedBindings;
        if (ts.isNamedImports(bindings)) {
          for (const el of bindings.elements) {
            const at = checker.getSymbolAtLocation(el.name);
            if (at && (at.flags & ts.SymbolFlags.Alias) && checker.getAliasedSymbol(at) === symbol) names.add(el.name.text);
          }
        } else if (ts.isNamespaceImport(bindings)) {
          // `ns` may only be used as `ns.name`; anything else could hand the module's tables to code we can't read.
          const at = checker.getSymbolAtLocation(bindings.name);
          const target = at && (at.flags & ts.SymbolFlags.Alias) ? checker.getAliasedSymbol(at) : undefined;
          if (target?.declarations?.some(x => x.getSourceFile() === source)) {
            const bad = identifiersOf(file, at).some(id => id.parent !== bindings && !(ts.isPropertyAccessExpression(id.parent) && id.parent.expression === id));
            if (bad) return no(exported);
          }
        }
      }
      for (const text of names) {
        const found = [];
        const walk = n => {
          if (ts.isIdentifier(n) && n.text === text && !(ts.isImportSpecifier(n.parent) || ts.isImportClause(n.parent) || ts.isNamespaceImport(n.parent))) {
            const at = ts.isShorthandPropertyAssignment(n.parent) && n.parent.name === n ? checker.getShorthandAssignmentValueSymbol(n.parent) : checker.getSymbolAtLocation(n);
            const resolved = at && (at.flags & ts.SymbolFlags.Alias) ? checker.getAliasedSymbol(at) : at;
            if (resolved === symbol) found.push(n);
          }
          ts.forEachChild(n, walk);
        };
        walk(file);
        for (const id of found) {
          if (id === d.name || inTypePosition(id) || ts.isExportSpecifier(id.parent)) continue;
          if (ts.isExportAssignment(id.parent)) return no(exported);
          // `ns.NAME` is the use; the node whose value is read is the whole access.
          const use = ts.isPropertyAccessExpression(id.parent) && id.parent.name === id ? id.parent : id;
          if (!flows(use)) return no(exported);
        }
      }
    }
    return { ok: true, exported };
  }

  // The declaration an identifier stands for, through imports.
  const declarationOf = id => {
    let s = checker.getSymbolAtLocation(id);
    if (!s) return undefined;
    if (s.flags & ts.SymbolFlags.Alias) s = checker.getAliasedSymbol(s);
    return s.valueDeclaration ?? s.declarations?.[0];
  };

  const inside = (d, n) => d.getSourceFile() === n.getSourceFile() && d.pos >= n.pos && d.end <= n.end;

  // Identifier nodes that are reads of a value (not a property name, a declaration or a type).
  const references = (root, visit) => {
    const walk = n => {
      if (isFunctionLike(n) && n !== root) { /* a nested function is read where it runs */ }
      if (ts.isIdentifier(n)) {
        const p = n.parent;
        const isName = (ts.isPropertyAccessExpression(p) && p.name === n)
          || (ts.isPropertyAssignment(p) && p.name === n)
          || (ts.isBindingElement(p) && p.propertyName === n)
          || (ts.isVariableDeclaration(p) && p.name === n)
          || (ts.isParameter(p) && p.name === n)
          || (ts.isBindingElement(p) && p.name === n)
          || ts.isTypeReferenceNode(p) || ts.isQualifiedName(p)
          || (ts.isFunctionDeclaration(p) && p.name === n)
          || (ts.isCatchClause(p.parent) && p.parent.variableDeclaration === p);
        if (!isName) visit(n);
      }
      if (n.kind === ts.SyntaxKind.ThisKeyword) visit(n);
      ts.forEachChild(n, walk);
    };
    walk(root);
  };

  const awaitsOf = fn => {
    const found = [];
    const walk = n => {
      if (n !== fn && isFunctionLike(n)) return;
      if (ts.isAwaitExpression(n)) found.push(n);
      ts.forEachChild(n, walk);
    };
    ts.forEachChild(fn, walk);
    return found;
  };

  const loopsWithAwait = (fn, awaits) => {
    const loops = [];
    const walk = n => {
      if (n !== fn && isFunctionLike(n)) return;
      if (ts.isIterationStatement(n, false) && awaits.some(a => a.pos >= n.pos && a.end <= n.end)) loops.push(n);
      ts.forEachChild(n, walk);
    };
    ts.forEachChild(fn, walk);
    return loops;
  };

  // Everything the rule says about one function. `hazards` is empty for a function that may
  // be read sequentially. `arguments` lists the reads that rest on A1.
  return function analyze(fn) {
    const awaits = awaitsOf(fn);
    const result = { awaits: awaits.length, hazards: [], arguments: [], constants: [] };
    if (!awaits.length) return result;
    const loops = loopsWithAwait(fn, awaits);
    const after = id => {
      const at = id.getStart();
      if (awaits.some(a => a.end <= at)) return true;
      return loops.some(l => at >= l.pos && at < l.end);
    };

    // Variables that hold, or alias, an argument whose type is not immutable.
    const flagged = new Set();
    for (const p of fn.parameters) {
      const mark = n => {
        if (ts.isIdentifier(n)) {
          const s = checker.getSymbolAtLocation(n);
          if (s && !immutable(checker.getTypeOfSymbolAtLocation(s, n))) flagged.add(s);
        } else if (ts.isObjectBindingPattern(n) || ts.isArrayBindingPattern(n)) {
          for (const e of n.elements) if (!ts.isOmittedExpression(e)) mark(e.name);
        }
      };
      mark(p.name);
    }
    for (let grew = true; grew;) {
      grew = false;
      const derive = (target, source) => {
        const names = [];
        if (ts.isIdentifier(target)) names.push(target);
        else if (ts.isObjectBindingPattern(target) || ts.isArrayBindingPattern(target)) {
          const collect = p => { for (const e of p.elements) if (!ts.isOmittedExpression(e)) (ts.isIdentifier(e.name) ? names.push(e.name) : collect(e.name)); };
          collect(target);
        }
        let touches = false;
        references(source, id => { const s = checker.getSymbolAtLocation(id); if (s && flagged.has(s)) touches = true; });
        if (!touches) return;
        for (const id of names) {
          const s = checker.getSymbolAtLocation(id);
          if (s && !flagged.has(s) && !immutable(checker.getTypeOfSymbolAtLocation(s, id))) { flagged.add(s); grew = true; }
        }
      };
      const walk = n => {
        if (n !== fn && isFunctionLike(n)) return;
        // An awaited value comes from the oracle (or an async callee), not from the argument.
        if (ts.isVariableDeclaration(n) && n.initializer && !ts.isAwaitExpression(n.initializer)) derive(n.name, n.initializer);
        if (ts.isBinaryExpression(n) && ts.isAssignmentOperator(n.operatorToken.kind) && ts.isIdentifier(n.left) && !ts.isAwaitExpression(n.right)) derive(n.left, n.right);
        ts.forEachChild(n, walk);
      };
      ts.forEachChild(fn, walk);
    }

    const seen = new Set();
    references(fn.body, id => {
      if (!after(id)) return;
      if (id.kind === ts.SyntaxKind.ThisKeyword) {
        result.hazards.push({ node: id, message: "`this` is read after an `await`, and other code may change it" });
        return;
      }
      const d = declarationOf(id);
      if (!d) return;
      if (inside(d, fn)) {
        const s = checker.getSymbolAtLocation(id);
        if (s && flagged.has(s) && !seen.has(s)) { seen.add(s); result.arguments.push({ node: id, name: id.text }); }
        return;
      }
      if (ts.isFunctionDeclaration(d) || ts.isClassDeclaration(d) || ts.isEnumDeclaration(d) || ts.isModuleDeclaration(d)
        || ts.isImportSpecifier(d) || ts.isNamespaceImport(d)) return;
      // `Math`, `Error`, `JSON`: the standard library. The translator refuses code that patches them.
      if (program.isSourceFileDefaultLibrary(d.getSourceFile())) return;
      if (ts.isVariableDeclaration(d)) {
        const constant = (d.parent.flags & ts.NodeFlags.Const) !== 0;
        const type = checker.getTypeAtLocation(d.name);
        if (constant && immutable(type)) return;
        if (constant) {
          const table = untouched(d);
          if (table.ok) {
            if (table.exported && !result.constants.some(c => c.name === id.text)) result.constants.push({ node: id, name: id.text });
            return;
          }
        }
        if (constant && process.env.HAZARD_WHY) appendFileSync(process.env.HAZARD_WHY, `${id.text}\t${(d.initializer?.getText() ?? "").replace(/\s+/g, " ").slice(0, 90)}\t${checker.typeToString(type).slice(0, 60)}\n`);
        result.hazards.push({ node: id, message: constant
          ? `\`${id.text}\` is a module-level object that other code may change, and it is read after an \`await\``
          : `\`${id.text}\` is a module-level \`${(d.parent.flags & ts.NodeFlags.Let) ? "let" : "var"}\` that other code may change, and it is read after an \`await\`` });
        return;
      }
      if (ts.isParameter(d) || ts.isBindingElement(d)) {
        // A variable of an enclosing function: a closure over something that may change.
        result.hazards.push({ node: id, message: `\`${id.text}\` belongs to an enclosing function and is read after an \`await\`` });
      }
    });
    return result;
  };
}
