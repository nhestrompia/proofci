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

const flag = (ts, type, f) => Boolean(type.flags & f);

export function createHazards(ts, checker, program) {
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
    const result = { awaits: awaits.length, hazards: [], arguments: [] };
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
