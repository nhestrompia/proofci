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
Proofs work the same way as for Rust, including `step*`.

| Supported | Details |
|---|---|
| Values | `number`, `boolean`, `T \| null`, `T \| undefined` |
| Types | Interfaces, string-literal unions, unions tagged by `kind` |
| Functions | Module-level functions and arrow functions, across files |
| Control flow | `if` with early return, `switch`, `? :`, `&&`, `\|\|` |
| Objects | Literals, destructuring, a leading spread |
| Numbers | `+ - * / %`, comparisons, `Math.floor/ceil/trunc(a / b)`, `Math.abs/min/max` |

Everything else is `unsupported`, with the source line. That includes strings,
arrays, loops, mutation, classes, `async`, `throw` and calls into packages.

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
