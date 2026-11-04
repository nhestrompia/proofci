# TypeScript support

TypeScript support is experimental and isn't in a release yet. This page covers
what works, what a proof means, and the survey behind the plan.

## What works today

The manifest names the language and the package, and functions by file:

```yaml
version: 1
language: typescript
package: .
lean: proofci
targets:
  - id: transfer
    function: src/ledger.ts::transfer
    guarantees:
      - id: conservation
        theorem: transfer_conserves
```

Lean sees `src/ledger.ts::transfer` as `src.ledger.transfer`, in a module named after
the package, so `ts-bank` is `import TsBank`. See [`examples/ts-bank`](../examples/ts-bank).
Proofs work the same way as for Rust, including `step*`. Start with
[proving TypeScript](proving-typescript.md), and see
[`examples/ts-real`](../examples/ts-real) for proofs about functions from real projects.

| Supported | Details |
|---|---|
| Values | `number`, `bigint`, `boolean`, `string`, `T \| null`, `T \| undefined` |
| Types | Interfaces, string-literal unions, unions tagged by `kind`, arrays, `Map`, `Set` |
| Functions | Module-level functions and arrow functions across files, self-recursion, inline callbacks |
| Control flow | `if`, `switch`, `for`, `while`, `for...of`, `break`, `continue`, `throw`, `try`/`catch` |
| Local changes | Reassignment, `+=`, `++`, and in-place changes to a value only one name can see |
| Arrays | `length`, `[i]`, `push`, `map`, `filter`, `reduce`, `find`, `some`, `every`, `slice`, `includes`, `join` and more |
| Strings | `length`, `[i]`, `slice`, `startsWith`, `includes`, `split`, `trim`, `replace` with a string, templates, ASCII case changes |
| Numbers | `+ - * / %`, comparisons, `Math.floor/ceil/trunc(a / b)`, `Math.abs/min/max` |

Everything else is `unsupported`, with the source line. That includes fractions,
regular expressions, classes, `async`, `??`, `?.` and calls into packages.

### In-place changes

A value in Lean only behaves like a JavaScript object if nothing else can see the
object change. So a changed array, map or object must start as a new value in that
function, and can only be read, returned or copied. Changing a parameter, storing a
changed array in another object or passing it to a function is `unsupported`.

### Proving loops

A loop translates to Aeneas's `loop`, so `loop.spec_decr_nat` applies. Give it what
shrinks and what stays true. See `sum_exact` in
[`examples/ts-bank`](../examples/ts-bank/proofci/Proofs.lean). `throw` is `fail .panic`,
so "this input throws" is stated as `f x = fail .panic`.

### What `number` means

`number` is a safe integer. If any step would produce a fraction, `NaN`, `Infinity`
or a value past `Number.MAX_SAFE_INTEGER`, the model fails. So a proof that a function
returns a value also proves it never lost precision. Code that needs fractions stays
unproven, and is never judged wrongly.

Each check also runs the translated functions in Node on generated inputs. See the
[security model](../SECURITY.md#typescript).

## Survey

### How it works

[`typescript/survey`](../typescript/survey) reads a repository with the TypeScript
compiler and classifies every exported function that makes at least one decision.
A function counts as covered only if everything it reaches is covered. It never
runs code from the repositories it reads.

The numbers below come from 21 public repositories and 22,652 functions.
"Pure" functions (5,701) compute a result from their inputs, without I/O, async,
object state or third-party calls. Those are the natural proof targets.

| Reached | All functions | Pure functions |
|---|---:|---:|
| Milestone 2: core language | 7% | 27% |
| Milestone 3: ownership, `this`, `async`, callbacks | 11% | 35% |
| Also with library models | 22% | not measured |

What blocks pure functions, as a share of the 5,701:

| Blocker | Reaches it | Only blocker |
|---|---:|---:|
| Library calls with no model yet, such as `toLowerCase` | 24% | 8% |
| `Object.keys`, `JSON` and other reflection | 23% | 7% |
| Unchecked casts and `any` | 23% | 6% |
| Regular expressions | 15% | 5% |
| Keys that aren't known types | 9% | 3% |
| Aliased mutation | 7% | 1% |
| Fractional numbers | 5% | 2% |

### What this changed

- **The plan's stop condition didn't trigger.** Fractions and aliasing are not what
  holds pure functions back, so binary64 numbers and a heap model stay later.
- **Library models move earlier.** They matter more than classes or `async` for pure
  code, so a models milestone goes between milestones 2 and 3.
- **Pure logic is the honest target.** ProofCI covers most of a code base's kernels
  long before it covers the code around them, and that's where proofs pay off.
- **Casts can become listed assumptions.** A downcast can't be checked, but a report
  can say that a result depends on it. That is worth trying before rejecting them.

### What the translator accepts today

The table above is what a finished subset would reach. `survey/try.mjs` runs the real
translator on the pure functions of nine of those repositories instead. Today it
accepts 82 of 1,457, about 6%. Acceptance only means the translator produced Lean: of
36 accepted functions that were also compiled, 35 built. The failures are now a long tail, and most of it is
about mapping TypeScript's types onto Lean's: recursive types, generic types,
untagged unions, `any` and `unknown`.

### Limits of these numbers

- The classifier is heuristic. It under-counts aliasing, because it doesn't follow
  values stored in collections and mutated later.
- Dependencies weren't installed, so some types are unresolved. That inflates casts
  from `any` and third-party calls.
- `Pure` still includes plumbing that nobody would prove.
- The repositories were hand-picked, and each is sampled to 1,500 files.
- Library internals skew low: `immer` and `zod` are metaprogramming by nature.

Reproduce it with:

```sh
cd typescript && npm ci --ignore-scripts
node --max-old-space-size=8192 survey/run.mjs <repository> <output.json>
python3 survey/report.py <directory of outputs>
```

## Getting to full TypeScript

"Full" can't mean every program. `eval`, `Proxy` and reflection on unknown objects
have no useful proofs. The realistic goal is that every function gets a sound verdict,
pure logic can usually be proved, and everything else becomes a listed assumption.

The current design maps each TypeScript type to a Lean type, which is why each new
type shape is a new feature. The plan is to add a second path that doesn't need that:

1. **Finish the cheap wins.** Install packages for their types with `--ignore-scripts`,
   add recursive and generic types, and make `unsupported` say how to fix the code.
2. **Try a dynamic path.** Translate to a single Lean type of JavaScript values plus an
   explicit heap, so TypeScript types become preconditions. That one change covers
   unions, `unknown`, aliasing, classes and closures. The typed path stays as the fast
   path. This depends on a spike showing proofs stay practical.
3. **Fill in the runtime.** Library models, promises as an event queue, and binary64
   numbers with safe integers as lemmas on top.
4. **Prove the translation.** Generate a proof, per function, that the typed output
   matches the dynamic semantics, so the translator leaves the trusted base.
