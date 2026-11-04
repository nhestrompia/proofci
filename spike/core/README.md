# Core spike

A small-scale test of the proposed TypeScript architecture: one formal model of
JavaScript (Core), with today's typed output tied to it by a generated theorem.

## Verdict

The design can work, and the riskiest assumption held on these samples. This code is a
throwaway: it shows feasibility, not coverage.

| Question | Result |
|---|---|
| Does Core match Node? | 1,200 of 1,200 runs agree, comparing results and mutated inputs, with inputs that share objects |
| Can bridge theorems be generated? | Yes, for all 4 tuned functions: 5.5 s to check, 149 generated lines, standard axioms only |
| Does a wrong translation fail? | Yes, 4 of 4 one-line corruptions of the typed output were rejected |
| Can shared objects be proved on Core? | Yes, 3 theorems in a fixture written for the spike, 29 lines of proof |
| Does it work on unseen real functions? | 0 of 10 at first; 6 of 10 after adding missing features |

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

- **Numbers are exact integers, not binary64.** This is the largest untested risk.
- **No closures, classes, async, or `return` inside a loop.**
- **Loops must leave the heap alone** for the bridge. Mutating loops are unbridged.
- **Calls are inlined** in bridges, so nothing here is compositional yet.
- **The aliasing test is one small fixture**, not real code, and has no loops.
- **`lower.mjs` is still trusted.** A bridge ties the typed output to what lowering
  produced, not to the TypeScript.
- **Core has only been tested against Node here**, not against test262.
- **Tactics are fragile.** One added lemma broke a passing bridge during this spike.
- **Bridges say nothing when the typed output fails,** as with the rest of ProofCI.

## Reproducing

```sh
node mk.mjs                 # Core for the samples, and the Node comparison
rm -f work/src/*.mjs work/src/config/*.mjs   # the translator rejects compiled files
node view.mjs               # the typed view
node bridge.mjs src/ledger.ts::transfer src/ledger.ts::sumAmounts \
  src/phases.ts::getActiveSpendingPhase src/config/price.ts::deriveAuctionPricing
lake build Spike.Bridges Spike.Alias
```

Paths assume a sibling `typescript-support` worktree with `node_modules` installed, and
Lean runs in the `proofci-toolchain` image.
