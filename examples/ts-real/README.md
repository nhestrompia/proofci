# Proofs about real code

The functions here are copied unchanged from two open-source projects, so that CI
proves real code on every run. They were translated with the rest of each repository
in place before being reduced to this copy.

| File | Source | Licence |
|---|---|---|
| `src/config/price.ts`, `src/constants.ts` | [Uniswap/sdks](https://github.com/Uniswap/sdks) at `187a621`, `liquidity-launcher-sdk` | MIT, Copyright (c) 2021 Uniswap Labs |
| `src/phases.ts` | [actualbudget/actual](https://github.com/actualbudget/actual) at `a3a1c7f`, `monteCarloSimulation.ts` | MIT, Copyright James Long |

## What is proved

- **Tick spacing is always positive**, for every `bigint`.
- **The floor price is on a tick boundary and not above the requested price**, so the
  `TickPriceNotAtBoundary` revert described in the doc comment can't happen.
- **The floor drifts by less than 1%**, which is the claim in the same doc comment.
- **The active spending phase is the last of the leading started phases**, a loop with a
  `break`, and **the earliest phase is active before any has started**.

The spending-phase theorems take a list with at least one phase. On an empty list the
TypeScript returns `undefined` despite its declared type, and the model stops, so
nothing is claimed there. `resolveSpendingPhases` in the original never returns an
empty list, but this repository doesn't prove that.
