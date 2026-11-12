# Core spike

The follow-up tests on real functions are in [SLICE.md](SLICE.md), [SLICE2.md](SLICE2.md) and [SLICE3.md](SLICE3.md).

A small-scale test of the proposed TypeScript architecture: one formal model of
JavaScript (Core), with today's typed output tied to it by a generated theorem.

## Verdict

The design can work. Every risk tested here held up or has a known fix, and the one
real failure, proof scaling, led to a better proof method. This code is a throwaway: it
shows feasibility, not coverage.

| Question | Result |
|---|---|
| Does Core match Node on values? | 1,200 of 1,200 runs agree, comparing results and mutated inputs, with inputs that share objects |
| Does binary64 match Node? | 3,000,000 random operations agree bit for bit, including subnormals, overflow, `-0` and `NaN` |
| Do safe integers stay exact in binary64? | Proved for `+`, `-`, `*`, comparison, `===` and indexing. `*` can give `-0`, which comparisons and `+` can't tell from 0 |
| Do bridges generate on doubles? | Yes, all 4 tuned functions: 4.6 s, standard axioms only |
| Does a wrong translation fail? | Yes, 4 of 4 one-line corruptions were rejected, tested before binary64 |
| Does a user's proof reach JavaScript? | Yes: `transfer_conserves` from `ts-bank` carries through a bridge to a statement about Core |
| Do closures, classes and `async` run correctly? | 1,140 runs: 1,109 match Node, 31 stop in the model, none wrong |
| Can they be proved? | Yes, see below |
| Do proofs scale? | The first method failed at 10 statements. Stepwise proofs check 640 statements in 17 s |
| Do bridges work on unseen functions? | 6 of 10 after adding coverage, on the integer model and on doubles |

## What was proved on Core

Each is in `Spike/` and depends only on Lean's standard axioms.

| Risk | Theorem |
|---|---|
| Shared objects | `moveMoney` conserves money on one shared account, and the look-alike creates it |
| Fractions | `0.01 - 0.03 + 0.03` isn't `0.01`, and `clamp01` is in range for every double except `NaN`, which passes straight through |
| `unknown` input | `amountOf` for every possible value |
| Closures | A closure shares a mutable variable with its function |
| Classes | An inherited method calls the object's own override. Checked for one concrete run |
| `async` | For all amounts, a stale read loses a withdrawal. The safe version is right in all 6 orders of turns, and the stale one depends on the order |
| `return` in a loop | `firstNegative` stops at the first negative and misses none before it |
| Loops that change the heap | `positivesLoop` builds exactly the filtered array |
| Calls | `sumPlusOne` uses `sumAll`'s theorem without seeing its loop |
| Recursion | `treeSum` on any tree, including one whose branches are the same object |

## Scaling

The first proof method simplified the whole remaining program at every step. It took
over 170 s at 10 statements and ran out of memory at 40. The stepwise method treats each
statement as a closed step on an abstract state:

| Shape | Size | Time |
|---|---|---|
| Straight line | 640 statements | 17 s |
| Early returns | 320 branches | 12 s |
| Consecutive `if`s that rejoin | 160, about 2^160 paths if taken apart | 9 s |

These are generated number-only functions. Times include about 4 s of startup.

## Problems found

- **Proof method:** see Scaling. The stepwise generator covers number code only so far.
- **Library models:** a plain `map` written in TypeScript gave a wrong answer in 31 of 60
  runs where the callback shrinks the array. Following the spec's order of steps fixed it.
  Library models need conformance tests, because they look right when they aren't.
- **Silent results:** `-0` is real. `0 * -5` is `-0`, and `1 / -0` is `-Infinity`. The typed
  view stops on division by zero, so it stays sound, but bridges through `*` need `IsInt`,
  not exact equality, and the generator doesn't do that yet.

## Unseen functions

| Function | Result | Reason |
|---|---|---|
| `isCellMatch` | Proved | |
| `maybeIncrementLevel` | Proved | |
| `getNextRunningBalance` | Proved | |
| `deriveAuctionOutcome` | Proved | |
| `clamp` | Proved | |
| `rangePosition` | Proved | |
| `calculateTrend` | Failed | The generic script can't take apart an array element read at a computed index |
| `trimIntervalDataToRange` | Not attempted | Needs a model of `slice` |
| `daysToWeeks` | Not attempted | Needs fractions and `Math.trunc` |
| `getV3HopCount` | Not attempted | Needs fractions and `startsWith` |

The 0 of 10 run used the generator as tuned on the first four functions. Getting to 6
took new lowering and encodings, plus changes to the tactics and generator. So 6 of 10
isn't a clean held-out score: these functions informed the fixes.

## What this doesn't show

- **Rounding arguments.** Nothing here proves a property that depends on how fractions
  round, such as a bound on a price with tax. This is the largest open question.
- **`try`/`catch`, generators, getters, `switch`, spread, and most built-ins.** Core has
  no `try`, and strings have almost no methods.
- **`await` inside loops or branches, rejected promises, or awaiting another `async`
  function.** Only top-level `await` of a settled value is modelled.
- **`async` order is all orders of two small tasks,** enumerated, not a general theorem.
- **Bridges for closures, classes and loops that change the heap.** Those proofs are
  direct specs on Core, so they aren't connected to a typed view.
- **Most fixtures are written for this spike,** not taken from real code.
- **`lower.mjs` is still trusted,** and Core hasn't been run against test262.
- **The sticky bit in division rounding** was never exercised by the random tests.
- **Inputs are assumed to be plain data.** A getter, `Proxy` or array hole falls outside
  the encoding, so a proof says nothing about such a value, and nothing checks this at
  runtime.

## Reproducing

```sh
node mk.mjs                 # Core for the samples, and the Node comparison
rm -f work/src/*.mjs work/src/config/*.mjs   # the translator rejects compiled files
node view.mjs               # the typed view
node bridge.mjs src/ledger.ts::transfer src/ledger.ts::sumAmounts \
  src/phases.ts::getActiveSpendingPhase src/config/price.ts::deriveAuctionPricing
lake build Spike.Bridges
node mk2.mjs                # closures, classes, async and the rest
lake build Spike.Alias Spike.Async Spike.Closures Spike.Loops Spike.Extra Spike.EndToEnd
node f64cases.mjs work/f64.txt 300000
lake env lean --run Spike/CheckF64.lean work/f64.txt
```

Paths assume a sibling `typescript-support` worktree with `node_modules` installed, and
Lean runs in the `proofci-toolchain` image.

[RANKING.md](RANKING.md) ranks the remaining work by how many functions each piece frees.
