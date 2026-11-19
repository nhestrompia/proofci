// What to change when the translator refuses code. `fail` adds the first hint whose
// pattern matches its reason, so a fail site needs no hint of its own. A hint names the
// smallest rewrite the translator accepts, or says there is none yet.
import ts from "typescript";

export const PREFIX = "How to fix: ";
const NONE = "there is no rewrite the translator accepts yet; keep this code out of the functions a guarantee reaches";
const none = why => `${NONE} (${why})`;

const TYPES = "use `number`, `bigint`, `boolean`, `string`, `T | null`, `T | undefined`, an interface, a string-literal union, a union tagged by `kind`, an array, `Map` or `Set`";
const REGEX = "use string methods instead of a regular expression (`startsWith`, `endsWith`, `includes`, `indexOf`, `split(\",\")`, `replaceAll(\"a\", \"b\")`, a loop over `charCodeAt`)";
const COPY = "change a copy (`const next = [...xs]` or `{ ...obj }`) and return it";
const TAGGED = "declare the union as a named `type` whose members each have a string literal field named `kind` (`type Shape = { kind: \"circle\"; r: number } | { kind: \"square\"; side: number }`), and read members inside `switch (x.kind)`";
const FUNCTION = "call a module-level function by name inside an inline callback (`xs.map(x => g(x))`); function values and function types have no translation yet";
const NULL_FIRST = "test the value for `null` on its own, first (`if (x !== null && ...)`), or return early (`if (x === null) return ...`)";
const PACKAGE = "list the call under `assumes` in proofci.yaml (a named import from a package, a function of its inputs; see docs/typescript.md#outside-calls), or under `effects` if it is awaited";

// Calls the translator can't see: built-ins with no model, package imports, calls through values.
function callHint({ node, checker }) {
  if (!node || !ts.isCallExpression(node)) return undefined;
  const callee = node.expression;
  const text = callee.getText();
  if (ts.isPropertyAccessExpression(callee)) {
    const receiver = callee.expression;
    const type = checker.getTypeAtLocation(receiver);
    if (ts.isRegularExpressionLiteral(receiver) || type.symbol?.name === "RegExp") return REGEX;
    if (/^(Object|Reflect)\./.test(text)) return "read the fields by name, or keep the data in a `Map` (`m.has(k)`, `m.get(k)`, `m.size`); an object can have keys its type doesn't list, so `Object.keys` and other reflection aren't translated";
    if (/^JSON\./.test(text)) return none("`JSON` has no model; parse at the boundary and pass typed values in");
    if (/^Array\.(from|of)$/.test(text)) return "build the array with a literal, spread (`[...set]`) or a loop";
    if (/^Array\.isArray$/.test(text)) return "drop the test: the declared type already says whether it is an array";
    if (/^Date\.|^performance\./.test(text)) return none("the clock is not a function of the inputs; pass the time in as a `number` parameter");
    if (/^(crypto|Math\.random)/.test(text)) return none("randomness is not a function of the inputs");
    if (/^console\./.test(text)) return "remove the logging from the function a guarantee reaches";
  }
  if (ts.isIdentifier(callee)) {
    if (/^(parseInt|parseFloat|Number|String|Boolean|BigInt|isNaN|isFinite|encodeURIComponent|decodeURIComponent|structuredClone|setTimeout|setInterval|fetch)$/.test(callee.text)) {
      if (callee.text === "String") return "use a template (`${n}`) or `n.toString()`";
      if (callee.text === "Boolean") return "compare explicitly (`x !== null`, `s.length > 0`)";
      if (callee.text === "Number") return "test for `null` or `undefined` first, so `Number` gets a plain `string`, `boolean` or `number`";
      return none(`\`${callee.text}\` has no model yet`);
    }
    const site = checker.getSymbolAtLocation(callee)?.declarations?.[0];
    if (site && ts.isImportSpecifier(site) && !site.parent.parent.parent.moduleSpecifier.text.startsWith(".")) {
      const module = site.parent.parent.parent.moduleSpecifier.text;
      const signature = checker.getResolvedSignature(node);
      const shown = signature ? `, \`signature: "${checker.signatureToString(signature)}"\`` : "";
      return `list it under \`assumes\` in proofci.yaml as \`call: ${module}::${(site.propertyName ?? site.name).text}\`${shown} (only for a function whose result depends on nothing but its arguments)`;
    }
    if (site && (ts.isParameter(site) || ts.isVariableDeclaration(site) || ts.isPropertySignature(site))) return FUNCTION;
  }
  if (ts.isPropertyAccessExpression(callee)) return "call a module-level function of the package by name; methods of objects and classes can't be called yet";
  return undefined;
}

// A named type: tell enums, classes and library types apart.
function namedTypeHint({ message, node, checker, program }) {
  const named = /the type `([A-Za-z_$][\w$.]*)[`<]/.exec(message)?.[1];
  if (!named || !node) return undefined;
  const [first, ...rest] = named.split(".");
  let symbol = checker.resolveName(first, node, rest.length ? ts.SymbolFlags.Namespace | ts.SymbolFlags.Alias : ts.SymbolFlags.Type | ts.SymbolFlags.Alias, false);
  if (symbol && symbol.flags & ts.SymbolFlags.Alias) symbol = checker.getAliasedSymbol(symbol);
  if (!symbol) return undefined;
  const declaration = symbol.declarations?.[0];
  if (symbol.flags & ts.SymbolFlags.Enum) return `replace the \`enum\` with a string-literal union (\`type ${named} = "a" | "b"\`) and compare with the strings`;
  if (named === "Date") return none("`Date` has no model; pass a timestamp as a `number` of milliseconds");
  if (named === "RegExp") return REGEX;
  if (named === "Promise") return "await it inside an `async` function; a promise can't be stored or passed";
  if (declaration && (program.isSourceFileDefaultLibrary(declaration.getSourceFile()) || declaration.getSourceFile().isDeclarationFile)) {
    return `pass the plain values the function needs (strings, numbers, an interface) instead of the library object \`${named}\`; library and DOM types are opaque outside \`async\` code`;
  }
  if (symbol.flags & ts.SymbolFlags.Class) return `pass the fields the function needs in an interface instead of an instance of the class \`${named}\`; classes have no translation yet outside \`async\` code`;
  return undefined;
}

function emptyRecordHint({ node, checker }) {
  const type = node && checker.getTypeAtLocation(node);
  if (type && checker.getNonNullableType(type).getCallSignatures().length) return FUNCTION;
  return "give the type at least one field, or drop the value: a type with no fields (`{}`) carries nothing a proof could use";
}

const METHODS = {
  pow: "write the product out with one factor per power (`a * a * a` for `Math.pow(a, 3)`)",
  round: "for `Math.round(a / b)` with `b > 0`, write `Math.floor((2 * a + b) / (2 * b))`; a whole number rounds to itself",
  sign: "compare with 0 (`a > 0 ? 1 : a < 0 ? -1 : 0`)",
  random: none("randomness is not a function of the inputs"),
  sort: none("`sort` has no model; keep the input sorted, or prove the guarantee for the unsorted list"),
  reverse: "build the reversed array with a loop from the end, pushing onto a new local array",
  pop: "read the last element with `xs[xs.length - 1]`",
  shift: "read the first element with `xs[0]` and continue from `xs.slice(1)`",
  push: "push onto a local array the function created (`const out: T[] = []`), then store it",
  splice: "build the new array with `slice` and spread (`[...xs.slice(0, i), ...xs.slice(i + 1)]`)",
  forEach: "use a `for...of` loop",
  entries: "loop over the array with a `for` loop over the indices",
  keys: "loop over an array of the keys kept alongside the `Map`",
  values: "loop over an array of the values kept alongside the `Map`",
  match: REGEX,
  matchAll: REGEX,
  search: REGEX,
  test: REGEX,
  localeCompare: "compare with `<` and `===`, which compare UTF-16 code units",
  toFixed: "work in whole units (cents, not dollars) so no rounding is needed",
};
function calledMethod(node) {
  if (node && ts.isPropertyAccessExpression(node.parent) && ts.isCallExpression(node.parent.parent)) node = node.parent.parent;
  const callee = node && ts.isCallExpression(node) ? node.expression : undefined;
  return callee && ts.isPropertyAccessExpression(callee) ? METHODS[callee.name.text] : undefined;
}
const method = text => /`(?:\.|Math\.|Number\.)?(\w+)(?:\(\.\.\.\))?`/.exec(text)?.[1];

const KINDS = {
  RegularExpressionLiteral: REGEX,
  TypeOfExpression: "drop the `typeof` test: the declared type already says what the value is; values whose type is `any`, `unknown` or a union of primitives have no translation yet",
  NewExpression: "build a plain object literal of an interface type; only `new Map()`, `new Set(array)` and `new Error(message)` can be created",
  ForInStatement: "loop over an array or a `Set` with `for...of`",
  DoStatement: "write `while (true) { ...; if (!(condition)) break; }`",
  LabeledStatement: "move the inner loop into a function that returns, instead of `break label`",
  ArrowFunction: FUNCTION,
  FunctionExpression: FUNCTION,
  FunctionDeclaration: "move the nested function to module level and pass it what it reads",
  ClassDeclaration: none("classes have no translation yet"),
  ThisKeyword: none("`this` has no translation yet; pass the object as a parameter of a module-level function"),
  DeleteExpression: "build a new object with only the fields to keep",
  SpreadElement: "pass the arguments one by one",
  VoidExpression: "remove `void`",
  TaggedTemplateExpression: none("tagged templates call a function the translator can't see"),
  ConditionalType: TYPES,
};

// [pattern on the reason, hint or a function of { message, node, checker, program }], first match wins.
export const HINTS = [
  // files and setup
  [/turns off compiler errors/, "remove the `@ts-ignore`, `@ts-expect-error` or `@ts-nocheck` comment and fix the error it hides"],
  [/an import that exists only for its side effects/, "remove the import, or move the function a guarantee reaches into a file without one"],
  [/replaces a built-in/, "move the function into a file that doesn't change built-ins (no `prototype`, `globalThis` or `Object.defineProperty` on a built-in)"],
  [/sits beside the TypeScript source/, "delete the compiled file next to the `.ts` file"],
  [/is outside the translated package/, `use types and functions of the package itself; for a call into another package, ${PACKAGE}`],
  [/^\S+ does not exist$/, "fix the path of the target's `function` in proofci.yaml"],
  [/is not a top-level function in/, "name a module-level `function` or `const f = (...) => ...` in proofci.yaml; methods and nested functions can't be targets yet"],
  [/TypeScript error: Element implicitly has an 'any' type because expression/, "keep the data in a `Map` and use `m.get(k)`; an object can't be indexed by a computed key"],
  [/TypeScript error: .*implicitly has an? '?any'? type|TypeScript error: Parameter has a name but no type/, "write the type out; the check reads code with `strict` on"],
  [/TypeScript error: .*(lacks ending return|Not all code paths return)/, "end every path with `return` or `throw`"],
  [/TypeScript error: .*is of type 'unknown'/, "give the value a declared type (a caught error can only have `message` and `name` read)"],
  [/TypeScript error: Cannot find (name|module|namespace)/, "add the package that declares it to the lockfile (ProofCI installs from it), or import the name"],
  [/TypeScript error: /, "fix the compiler error; the check reads code with `strict` on, so errors the project's own settings allow still count"],
  [/has no Lean spelling yet/, "rename it with ASCII letters, digits and `_`"],
  [/a variable can't be called/, "rename the variable"],

  // types
  [/only numbers, strings, booleans and string-literal unions can be keys/, "key the `Map` or `Set` by a `number`, `string`, `boolean`, `bigint` or string-literal union, for example an object's `id`"],
  [/the type `(any|unknown)(\[\])?`/, "write the type the value really has; `any` and `unknown` can only be narrowed by an `effects` entry's `narrowed` signature for awaited calls"],
  [/the type `Record</, "use `Map<K, V>`, or an interface with named fields"],
  [/the type `(Partial|Required|Readonly|Pick|Omit|NonNullable|ReturnType|Parameters|Awaited|Exclude|Extract)</, "write the fields out as an interface (`?:` for optional ones) instead of the utility type"],
  [/the type `\w+\.(infer|input|output)</, "write the type out as an interface and use it instead of the type inferred from the schema"],
  [/the type `(object|\{\})`/, "write an interface with the fields the code reads"],
  [/the type `\[/, "use an interface with named fields instead of the tuple"],
  [/the type `[^`]*=>/, FUNCTION],
  [/the type `[^`]*\|/, TAGGED],
  [/the type `/, ctx => namedTypeHint(ctx) ?? TYPES],
  [/^this type is not supported yet|the type of this variable is not supported yet|this object literal is not supported yet/, TYPES],
  [/empty records are not supported/, emptyRecordHint],
  [/an inline object type over a type parameter/, "declare the object type as a generic `interface` (`interface Box<T> { value: T }`) and use it (`Box<T>`)"],
  [/`Array\.isArray` is only supported on values typed as arrays/, "give the value a type that is an array or `null`/`undefined` (`string[] | undefined`)"],
  [/could itself be `null` or `undefined`/, "write `T extends {}` on the type parameter, so `T | undefined` adds exactly one value"],
  [/a generic type over a type parameter with a bound|a generic type over a type parameter is not supported yet when its own parameters have a bound/, "drop the bound (`T extends ...`) where the generic type or the function is declared, or use the generic type at a concrete type (`Page<string>`)"],
  [/a generic type that contains itself at a growing type argument/, "use the same type arguments where the type contains itself (`next: Node<T> | null`)"],
  [/this generic type is not supported yet|a generic union over a type parameter has no description yet/, "write the union without type parameters, as one named `type` per type argument the code uses"],
  [/type parameter `[^`]*` can't be read off this call/, "make the type parameter appear in a parameter or the result type, or drop it"],
  [/is called at `.*` where it takes `.*`, which is not supported yet/, "pass arguments whose types match the declared parameter types, or call a function that isn't generic"],
  [/this use of a generic type has no arguments to read/, "write the type arguments out where the generic type is used (`Page<string>`)"],
  [/a generic type over a type parameter/, "use the generic type at a concrete type (`Page<string>`), not at the function's own type parameter"],
  [/recursive types are not supported yet|holds a value of the type it sits in/, "in `async` code a recursive type is cut to an opaque handle, also in the functions it calls: pass the parts the function needs as parameters"],
  [/a generic type that holds itself/, "use it at concrete type arguments (`Tree<number>`), not at a type parameter"],
  [/a type that recurs through another type/, "let the type hold itself directly, in one named interface (`children: Tree[]`, `next: Tree | null`), not through a second interface or an inline object"],
  [/a recursive type that holds itself inside/, "hold the type itself in an array, `T | null` or an optional field (`children: Tree[]`), not in a `Map`, `Set` or tuple"],
  [/a recursive type with no finite value/, "make the field that holds the type nullable, optional or an array (`next: T | null`), so a value can end"],
  [/`lastIndexOf` with a start index/, "search the front of the array (`xs.slice(0, i + 1).lastIndexOf(v)` for `i >= 0`)"],
  [/`at` takes one index/, "pass one index (`xs.at(-1)`)"],
  [/`at` on an array that may hold/, "index from the end explicitly (`xs[xs.length - 1]`)"],
  [/only `flat\(\)` without a depth/, "call `flat()` once per level (`xs.flat().flat()`)"],
  [/`flat` is only supported on an array of arrays/, "spread each inner collection into an array first (`xs.map(s => [...s]).flat()`)"],
  [/`flatMap` is only supported with a callback that returns an array/, "return an array from the callback (`x => [f(x)]`), or use `map`"],
  [/would share a Lean name/, "rename one of the two declarations"],
  [/is not a plain field/, "declare it as a field (`name: T`), not a method, getter or computed key"],
  [/unions must be tagged records|union members need a string/, TAGGED],
  [/is not a safe integer/, "work in whole units (cents, basis points); `number` is a safe integer and fractions have no model yet"],

  // functions
  [/mutual recursion/, "merge the two functions into one self-recursive function"],
  [/this function has no body to translate/, `translate a function with a body (not an overload or \`declare\`); for a package function, ${PACKAGE}`],
  [/must write out their types/, "write them into the function's signature"],
  [/async generators|generators are not supported/, "return an array instead of using `yield`"],
  [/a recursive `async` function/, "rewrite the recursion as a loop"],
  [/must have a return type of the form `Promise<T>`/, "write the return type as `Promise<T>`"],
  [/can't be read as if nothing else ran between its `await`s/, "read what the code needs into local `const`s before the first `await`, or pass it as an argument; see docs/typescript.md#async-code"],
  [/returns nothing, so it can only be called for its effects/, "call it as its own statement"],
  [/rest parameters/, "take an array parameter (`xs: number[]`) instead of `...xs`"],
  [/this parameter shape/, "take a plain parameter and destructure it in the body"],
  [/only plain destructuring/, "destructure without defaults, nesting or `...rest` (`const { a, b } = x`), or read the fields (`x.a ?? 0`)"],
  [/array destructuring/, "read the elements by index (`const first = xs[0]`)"],
  [/reaches the end of the function without `return`/, "end every path with `return` or `throw`"],
  [/`return` without a value/, "return a value on every path"],
  [/`return` here is not supported yet/, "set a variable and `break`, then return after the loop"],
  [/labels are not supported/, KINDS.LabeledStatement],
  [/this `break` or `continue` is not supported yet/, "use a flag variable in the loop condition"],
  [/a nested block that returns/, "remove the braces of the bare `{ }` block"],

  // in-place changes and assignment
  [/reading a module-level `let` or `var`/, "declare it `const`, or pass the value as a parameter"],
  [/may be shared with the caller/, COPY],
  [/is an element of an array that is changed in place/, "copy the element (`{ ...item }`), or build a new array with `map`"],
  [/changing an array while looping over it/, "loop over a copy (`for (const x of [...xs])`), or collect the changes in a new array"],
  [/must start as a new array or object/, `start it as a literal or a copy: ${COPY}`],
  [/can't be passed around or stored here/, "store or pass a copy (`[...xs]`, `{ ...obj }`), made after the last change"],
  [/assignment inside a nested function/, "move the assignment out of the nested function: a `for...of` loop or a `forEach` callback can update an outer variable, and `reduce` can carry a running value"],
  [/assignment to module-level state/, "keep the state in a local variable and return the new value"],
  [/changing a nested array/, "assign a new array to the field (`c.items = [...c.items, v]`)"],
  [/writing to a nested field/, "replace the inner object (`a.b = { ...a.b, c: v }`)"],
  [/writing to a nested element/, "assign a whole new inner array (`grid[i] = [...grid[i].slice(0, j), v, ...grid[i].slice(j + 1)]`)"],
  [/^this write is not supported yet/, ({ node }) => calledMethod(node)],
  [/^this write is not supported yet|assigning to a field or element is not supported yet/, "assign to a local variable, or to a field or element of one (`x.f = v`, `xs[i] = v`)"],
  [/only `=` is supported on a field or element/, "write `x.f = x.f + v` instead of `x.f += v`"],
  [/assigning to a variable inside its own null check/, "assign the new value to another variable"],
  [/this assignment operator is not supported yet/, "write it out with `=` (`x = x ?? v`, `x = x || v`)"],
  [/is not assigned on every path|may be read before it is assigned/, "give it an initial value, or assign it on every path before the read"],
  [/is never assigned/, "give it a value or remove it"],
  [/is assigned values of different types/, "write its type (`let x: T;`)"],
  [/a declaration without a value needs a plain name/, "give it a value, or write `let x: T;` with a plain name"],
  [/a declaration without a value can't hold/, "start it with a value (`let x: T | null = null;`)"],
  [/`var` is not supported/, "use `let` or `const`"],
  [/^this statement is not supported yet/, "write the line as an assignment, an update (`i++`), or a call"],
  [/this statement has no effect/, "remove the statement"],

  // errors
  [/only `throw new SomeError|only `throw new Error\(message\)`/, "throw `new Error(message)` or another built-in error class"],
  [/an error with options/, "drop the second argument (`new Error(message)`)"],
  [/the message of a thrown error must be a string/, "pass a string (`new Error(`bad ${x}`)`)"],
  [/`finally` that returns, jumps or assigns/, "keep `return`, `break` and assignments to outer variables out of `finally`"],
  [/`finally` is not supported yet/, none("`finally` only works in `async` code; move the cleanup after the `try` if it can't throw")],
  [/reading the caught value is not supported yet/, "drop the variable (`catch { ... }`)"],
  [/assigning to an outer variable inside `try`/, "return from the `try` and the `catch`, or assign after the `try`"],
  [/`try` must either always return or never return/, "make every path through `try` and `catch` return, or none"],
  [/a destructured catch variable/, "catch a plain name (`catch (e)`) and read `e.message`"],
  [/of a caught error is not supported; only/, "read only `message` and `name` of the caught error"],
  [/`instanceof` is only supported/, "test a `kind` field instead of the class"],

  // loops
  [/`for await`/, "`await` inside a plain `for...of` loop"],
  [/`for\.\.\.of` is only supported on arrays and sets/, "loop over an array or a `Set`; a `Map` can't be iterated yet, so keep its keys in an array"],
  [/`for\.\.\.of` needs a plain variable/, "loop with a plain name (`for (const entry of xs)`) and read its fields inside"],
  [/a `for` loop needs|this `for` update/, "write `for (let i = 0; i < n; i++)` (the update can be `i++`, `i--`, `i += k` or `i = ...`)"],

  // null checks and conditions
  [/only a variable or field can be tested against null/, "store the value in a `const` and test that"],
  [/this null check is always false|can't tell `null` from `undefined`/, "use `== null` or `!= null`, which cover both"],
  [/the nullish value must be on the right/, "write `x === null`, with `null` or `undefined` on the right"],
  [/this field can't be null here/, "drop the check; the type says the field is never `null`"],
  [/this (kind of )?null check is not supported yet/, NULL_FIRST],
  [/`null` where the type doesn't allow it/, "add `| null` to the type"],
  [/this `&&` or `\|\|` is not supported here|`&&` on a value that may be/, `use \`??\`, or ${NULL_FIRST}`],
  [/this value is always truthy/, "remove the test, or compare with `null` if the type should allow it"],
  [/truthiness of this type/, "compare explicitly (`x !== null`, `xs.length > 0`, `n !== 0`)"],
  [/`===` is only supported on/, "compare a field (`a.id === b.id`) or the values' string form"],

  // switch
  [/`default` must be the last case/, "move `default` to the end"],
  [/a case that shares `default`/, "give `default` its own body"],
  [/an empty last case|an empty `default`/, "give it a body (`break` or `return`), or remove it"],
  [/falling through to the next case/, "end each non-empty case with `return`, `throw` or `break`, repeating shared code"],
  [/only a final `break` is supported in a case/, "end the case with one `break`, and use `if`/`else` inside instead of an earlier `break`"],
  [/`switch` on this expression|`\?\.` on an expression/, "store the value in a `const` first (`const k = xs[0].kind; switch (k)`)"],
  [/`switch` on `\.kind` needs|`switch` needs a tagged union/, "use `if`/`else` comparisons, or give the value a string-literal union or tagged union type"],
  [/case labels must be string literals/, "write the labels as string literals, or use `if`/`else`"],

  // values and expressions
  [/is used as a `/, "write the target type where the value is created (`const c: B = { ... }`)"],
  [/tuples are not supported yet/, "use an interface with named fields instead of the tuple"],
  [/arrays with holes/, "write every element out"],
  [/only arrays and sets can be spread/, "spread only arrays and sets (`[...xs]`), or list the elements"],
  [/only an empty `new Map\(\)`/, "start with `new Map()` and `set` the entries in a loop"],
  [/an object literal needs a declared type/, "write its type (`const p: Point = { ... }`, or the function's return type)"],
  [/a spread must come first/, "put `...base` before the other properties"],
  [/spreading a value with an index signature/, "copy the named fields one by one"],
  [/this kind of property is not supported yet/, "write `name: value` or the shorthand `name`; no methods, getters or computed keys"],
  [/a union value needs a literal `kind`/, "write `kind` as a string literal in the object (`{ kind: \"circle\", r }`)"],
  [/`\[\]` is only supported on arrays/, "use a `Map` and `m.get(k)`, or read the field by name"],
  [/`\?\.` is only supported on fields|optional calls|`\?\.` is not supported yet/, NULL_FIRST],
  [/type assertions/, "remove the `as` or `satisfies` and write the type where the value is created, or test it (`if (x.kind === ...)`); `as const` is fine"],
  [/this operator is not supported/, "use `+ - * / %`, comparisons, `!`, `&&`, `||` and `??`; write `a ** 2` as `a * a`; bitwise operators, `in` and unary `+` have no model yet"],
  [/`\+` between a string and another type/, "use a template (`${text}${n}`)"],
  [/mixing `number` and `bigint`/, "keep both sides the same type"],
  [/only `number` operands are supported here/, "keep both operands `number`"],
  [/can't go in a template, because it isn't known which word prints/, "use `${x ?? \"\"}`, or test for `null` first"],
  [/only strings, numbers, booleans and their optional forms can go in a template/, "put a string, number or boolean in the template (a field, or `xs.join(\",\")`)"],
  [/is not declared in the translated code/, "pass the value as a parameter, or import it from a file of the package"],
  [/functions as values/, FUNCTION],
  [/this field isn't available in this case/, "read the field in a `case` whose member declares it"],
  [/reading a field of a union outside a `switch`/, "read it inside `switch (x.kind)`, in each case"],
  [/read through an index signature/, "declare the field in the interface, or use a `Map<string, T>`"],
  [/whose fields and methods can't be read/, "pass the plain values the function needs instead of the object"],

  // calls
  [/`Promise\.\w+` is not supported/, none("concurrency has no model yet; awaiting the calls one after another is a different program")],
  [/on a promise is not supported yet; use `await`|returns a promise that is never awaited|is called without `await`/, "`await` the call where it is made"],
  [/is a call on an opaque/, "list the method under `effects` in proofci.yaml, as the reason says"],
  [/this `await` is (not on an `async` function|on a function with no source)/, "list the awaited call under `effects` in proofci.yaml (see docs/typescript.md#listing-the-outside-world)"],
  [/this call isn't to a function the translator can see|this function has no source in the package/, ctx => callHint(ctx) ?? PACKAGE],
  [/`await` on a call to a function that isn't `async`/, "remove the `await`"],
  [/`await` outside an `async` function/, "mark the function `async` with a `Promise<T>` return type"],
  [/`await` is only supported on a call/, "await the call where it is made (`await f(x)`), not a stored promise"],
  [/too many arguments/, "pass only the parameters the function declares"],
  [/a missing argument/, "pass every argument, or give the parameter a default or `?`"],
  [/is generic in a way that can't be assumed yet|has a type parameter with a bound, so it can't be assumed yet/, none("only generic functions whose type parameters have no bound can be listed")],
  [/is generic, so it can't be|takes a rest parameter, so it can't be|a call through an object or a function-typed parameter/, none("such calls can't be assumed or listed as effects")],
  [/has the signature .*, but `(assumes|effects)` lists/, "copy the signature the compiler reports into proofci.yaml (a policy change, so a maintainer approves it), or change the code back"],
  [/takes no arguments, so it can't be a function of its inputs/, "call it outside and pass its result in as a parameter"],
  [/narrowing `any` is only supported|`narrowed`|`signature` could not be read/, "fix the `effects` entry in proofci.yaml as the reason says"],
  [/is only supported as its own statement/, "read what you need before the call, then call it on its own line (`const last = xs[xs.length - 1]; xs.pop();`, `xs.push(v); const n = xs.length;`)"],
  [/a type parameter could be an object/, "bound the type parameter to primitives (`T extends string | number`), or compare a field"],
  [/with a start index is not supported yet/, "search a slice (`xs.slice(i).includes(v)`; for `indexOf`, add `i` to `xs.slice(i).indexOf(v)` when it isn't -1)"],
  [/on objects compares identity/, "compare a field (`xs.some(x => x.id === y.id)`)"],
  [/`join` is only supported on strings/, "map to strings first (`xs.map(x => `${x}`).join(\",\")`)"],
  [/only `concat` of one array/, "spread instead (`[...a, ...b, ...c]`)"],
  [/`reduce` needs an initial value/, "pass an initial value (`xs.reduce((a, b) => a + b, 0)`); an empty array then gives it instead of throwing"],
  [/is only supported with a string here, because it would otherwise take a regular expression/, `pass a string; ${REGEX}`],
  [/with (these )?arguments is not supported yet/, "call it with the arguments listed for strings in docs/typescript.md"],
  [/only an inline function is supported here/, "write the callback inline (`xs.map(x => g(x))`)"],
  [/this function must take exactly \S+ parameter/, "drop the extra parameters; for an index, use a `for` loop over the indices"],
  [/^`async` is not supported yet/, "await the calls in a `for...of` loop; note that runs them one after another"],
  [/only (plain parameters|a plain parameter) (are|is) supported/, "give the callback plain parameter names and read fields inside"],
  [/^`(Math|Number)\.\w+` is not supported|is not supported (on arrays|on strings|here) yet|^`\w+` is not supported yet/, ctx => METHODS[method(ctx.message)] ?? KINDS[method(ctx.message)]
    ?? "use a supported method (see the Arrays, Strings and Numbers rows in docs/typescript.md), or a loop that computes the same result"],
];

const FALLBACK = "ProofCI has no hint for this reason yet; docs/typescript.md lists what the translator accepts";

export function hintFor(message, context = {}) {
  const text = message.split("\n")[0].replace(/^\S*:\d+: /, "");
  for (const [pattern, hint] of HINTS) {
    if (!pattern.test(text)) continue;
    let found;
    try {
      found = typeof hint === "function" ? hint({ ...context, message: text }) : hint;
    } catch {
      found = undefined;
    }
    if (found) return found;
  }
  return FALLBACK;
}

export function withHint(message, context) {
  return message.includes(`\n${PREFIX}`) ? message : `${message}\n${PREFIX}${hintFor(message, context)}`;
}
