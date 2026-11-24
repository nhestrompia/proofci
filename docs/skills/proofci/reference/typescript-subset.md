# The supported TypeScript subset

Verified against the translator; `constructs.json` has one tested snippet per
row. Roughly 8% of real-world pure functions translate unchanged — plan on
extracting and rewriting, not pointing at existing code.

**"Supported" means the code translates to the Lean view — not that its proof
or bridge succeeds.** Rows marked ⚠ bridge below translated in the pilots but
their generated faithfulness proof often ended STUCK (→ `tested, not proved`).
Design around them when a guarantee must reach `verified`.

## Supported (tested)

- `number` (safe integers; fractions/`NaN`/`Infinity` flip the function to
  `Js.Dbl` binary64 mode or refuse), `bigint`, `boolean`, `string`,
  `T | null`, `T | undefined`; interfaces with plain fields; string-literal
  unions; unions tagged by `kind`; arrays; `Map`/`Set` (limited method sets);
  `Record<string, V>` as a dynamic-key record (`r[k]`, `k in r`, `Object.keys`).
  ⚠ bridge: record parameters often STUCK — pass the plain fields instead.
- `if`/early return, `switch`, `for`, `for...of`, `while`, `break`, `continue`,
  `throw`, `try`/`catch`.
- `??`, `?.`, `||`, `&&`; `===`/`!==` null/undefined narrowing.
  ⚠ bridge: `?.` chains and optional fields often STUCK — prefer `=== null`
  narrowing with named reads.
- Arrays: `length`, `[i]`, `push` (on a fresh copy), `map`, `filter`, `reduce`,
  `find`, `some`, `every`, `slice`, `includes`, `indexOf`, `join` (strings only).
  ⚠ bridge: `filter(...).includes().map()`-style chains often STUCK — rewrite
  as `switch` on the inductive (proved in ~5 s vs the 120 s cap).
- Strings: `length`, `[i]`, `slice`, `startsWith`, `includes`, `split`, `trim`,
  `replace` (string arg), templates, `toUpperCase`/`toLowerCase` (ASCII).
- Numbers: `+ - * / %` (`/` only where the quotient is whole, else Dbl mode),
  comparisons, `%`, `Math.floor/ceil/trunc(a / b)`, `Math.abs/min/max`.
- Reassignment, `+=`, `++`, `let x;` assigned before read; in-place changes to a
  value only one name can see (a fresh `[...xs]` or `{ ...o }` copy).
- Module-level function calls, self-recursion, inline callbacks that call named
  functions (`xs.map(x => g(x))`).
- `async`/`await` in a narrow form (listed `effects`, sequential awaits only —
  no `Promise.all`, loops/`finally` downgrade the bridge to `tested`).

## Refusals: construct → smallest rewrite that worked in the pilots

The `code` column is the stable refusal code from `scan --json` — use it as
the `code` field in `proofci/gaps.jsonl` (`other` means the reason text
carries the detail).

| Code | Refused | Rewrite |
|---|---|---|
| `typeof-expression` | `typeof x === "string"` guard | Test for `null`/`undefined` (`x == null`); the declared type already says it. |
| `null-check` | `a != null && b != null` one-condition check | Separate nested tests: `if (a === null) return …; if (b === null) return …` |
| `type-any`, `type-unknown` | `any`, `unknown` | Write the real type (or `narrowed` on an `effects` entry). |
| `type-date` | `Date` param/field | Split at the boundary: pass the `string`/`number` the pure core needs; `.toISOString()` in a thin wrapper. |
| `other` | `enum` / Prisma enum import (`Type as ActivityType`) | String-literal union `type T = "a" \| "b"`, compare strings. |
| `compile-error`, `missing-types` | Missing parameter/return type (implicit `any`) | Annotate everything a guarantee reaches — the manifest requires written types. |
| `other` | `?.[key]` optional indexing | `v !== undefined ? v[key] : fallback`. |
| `in` | `'k' in obj` on an interface | `obj.k !== undefined` (only when the field is set when defined). |
| `in-place-mutation` | `xs.push(…)` into a parameter / shared value | `const ys = [...xs]; ys.push(…); return ys`. |
| `other` | Literal-union member like `"NOT IN"` | Rename to a Lean-safe ASCII name (letters, digits, `_`). |
| `other` | `Record`/`Map` lookup into a module const map | Inline the literal, or `switch` returning per-case literals. |
| `type-<name>` | `NoInfer<T>`, `z.infer`, schema-derived types | Write the resolved type out by hand. |
| `type-<class>` | Class/library object param, method calls | Pass the plain fields in an interface; no methods outside `async` handles. |
| `unsupported-*`, `type-tuple`, `other` | Rest params `...xs`, tuples, method members in interfaces | Array param; named-field interface; plain fields only. |
| `other` | `JSON.*`, `Object`/`Reflect` reflection, `console.*`, `crypto`, `Math.random`, `Date.now` | No rewrite — keep them out of guaranteed functions; `console.log` can be an `assumes` entry in practice. |
| `other` | `Math.pow` and unmodelled `Math.*` | Inline literal arithmetic (`a * a * a`; `quota * 8 / 10` for `Math.ceil(q*0.8)`). |
| *(translates)* | `filter(...).includes().map()` over literal lists | The generated bridge proof goes STUCK — rewrite as `switch` on the inductive returning literals (proved in ~5 s vs timeout). |
| `type-<name>`, `outside-package` | Package calls (`prisma.*`, `zod.*`, `date-fns`, imported fns) | `assumes` for pure named imports (exact signature), `effects` for awaited calls; else unreachable. |
| `type-promise`, `unsupported-*` | `Promise.all`, `.then`, timers, generators, `for await` | Out of scope — keep orchestration outside guaranteed functions. |

## Picking worthwhile functions

- Look for a decision a wrong answer breaks: authorization/permission
  predicates, quota/percent arithmetic, parsing/validation, comparators and
  ordering, response mapping (`favorited`, `following`).
- Extract the pure core of async/Prisma handlers: a function taking plain
  values (`string`, `number`, interfaces, unions) and returning a decision;
  leave I/O in a thin wrapper. `mapArticle` over string fields + a mapper that
  calls `.toISOString()` at the edge is the pattern.
- Prefer functions whose doc comment already promises something — the promise
  is the theorem.
- `scan --json` reports every exported function with its refusal `reason`,
  `hint` and stable `code` (`summary.by_code` ranks the blockers). Copy `code`
  into `proofci/gaps.jsonl` entries.
