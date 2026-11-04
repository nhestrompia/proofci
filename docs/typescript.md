# TypeScript support: survey and plan

ProofCI's TypeScript path is being built on the `typescript-support` branch. This
page records what the first survey measured and how it changed the plan.

## How the survey works

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

## What this changed

- **The plan's stop condition didn't trigger.** Fractions and aliasing are not what
  holds pure functions back, so binary64 numbers and a heap model stay later.
- **Library models move earlier.** They matter more than classes or `async` for pure
  code, so a models milestone goes between milestones 2 and 3.
- **Pure logic is the honest target.** ProofCI covers most of a code base's kernels
  long before it covers the code around them, and that's where proofs pay off.
- **Casts can become listed assumptions.** A downcast can't be checked, but a report
  can say that a result depends on it. That is worth trying before rejecting them.

## Limits of these numbers

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
