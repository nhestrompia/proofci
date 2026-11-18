# Dynamic path spike

Roadmap step 2 in [docs/typescript.md](../../docs/typescript.md): translate to one Lean type of
JavaScript values plus an explicit heap, so TypeScript types become preconditions instead of
Lean types. Not wired into the action.

## Verdict

Go, with one condition: the proofs need generated step lemmas before users can write them.
The translation itself was easy: real corpus functions that the typed path rejects translate,
run like Node, and can be proved. The proofs are slower to write than typed ones, not slower
to check.

| Question | Result |
|---|---|
| Does one value type cover the rejected shapes? | Yes: `unknown`, unions, shared objects, closures that assign captured variables, and classes, from 6 corpus functions and 2 fixtures |
| Does it match Node? | 1,080 random runs over 18 functions: 987 agree on the result and on every input after the call, 93 stop in the model, none differ |
| Can users prove things about it? | Yes, 6 theorems below, standard axioms only |
| Does a wrong translation fail? | 35 of 35 one-line mutants of the proved functions fail to check |
| Proof checking time vs typed | Same order: 3.1-3.3 s for this file, 2.1-2.7 s for `ts-bank`'s typed proofs, both mostly startup |
| Proof writing effort vs typed | Higher: `transfer_conserves` is 24 lines here and 2 (`unfold; step*`) on the typed path |

The differential test found a real bug in Core: its `Math.min` and `Math.max` lose `-0`
(`Math.min(-0, 500)` is `-0` in Node and `0` in Core). This spike uses its own `minMax` on
doubles; Core still has the bug.

## What's here

| File | What it is |
|---|---|
| [Dyn.lean](Dyn.lean) | The monad `M` over `Core.Val` and `Core.Heap` (result, throw or `stuck`), operations, loops, array callbacks, methods, `Ty`/`Is` preconditions, and the step lemmas the proofs use |
| [dyn.mjs](dyn.mjs) | The translator: TypeScript to `M`, plus a `.pre` per function from its parameter types. Anything else is `unsupported` or `stuck` |
| [gen.sh](gen.sh) | Regenerates [Gen/](Gen) from the corpus checkouts |
| [Proofs.lean](Proofs.lean) | User-level theorems |
| [diff.mjs](diff.mjs) | Random inputs from the TypeScript types, with shared objects, run in Node and in Lean |
| [mutate.mjs](mutate.mjs) | Plants wrong translations in the proved functions |
| [check.sh](check.sh) | Runs the proofs, the mutants and the replay in the toolchain image |

The functions, all rejected by the typed path today:

| Shape | Function |
|---|---|
| `unknown` | AppFlowy `parseChartGroupByFieldId`, `parseChartDecimalPlaces` |
| Unions | AppFlowy `isDashboardPrivateKeyOfUser`, `dashboardPrivateStorageKey` |
| Shared objects | continue `addSpaceToAnyEmptyMessages` mutates the caller's messages and returns them |
| Closures | continue `renderContextItemsWithStatus`; fixture `colorIndexes` assigns two captured variables |
| Classes | immich `SlideshowHistory`, AppFlowy `FormulaEvaluationBudget`; fixture `Counter` |
| Both paths | `ts-bank` `calculateFee`, `transfer`, `sumAmounts`, for the comparison |

## What was proved

| Theorem | Shape |
|---|---|
| `groupByFieldId_string` | For every value, the result is the value if it's a string and `""` otherwise |
| `bump_adds` | A method call adds to the object it is called on |
| `bumpBoth_shared` | The same counter passed twice is bumped twice |
| `bumpBoth_separate` | Two counters are bumped once each |
| `transfer_conserves` | `transfer` keeps the total and never overdraws, the typed path's theorem restated |
| `queue_keeps_reference` | `queue` stores the caller's object, so the history ends with the same reference |

Preconditions are facts about the heap (`h[l]? = some (.record fs)`, `fs.lookup "n" = some (num k)`),
which say the same as `Is` for the fields a proof needs.

## What it costs

Checking is cheap: each generated module takes about 1.8 s, the same as the typed module for
`ts-bank`, and the proofs file 3.2 s. Writing is the cost. A typed proof is often
`unfold; step*` because each operation already has a spec on its Lean type. Here each heap read
and write is a step that has to be rewritten by hand, and `simp` can't be used on whole
programs: deciding that two different string literals differ by evaluation (`"n" == "__class"`)
times out, so any `simp` that unfolds a record lookup on a literal list hangs. Proofs instead go
through lemmas (`field_rec`, `setField_rec`, `isMethodOf_rec`, `push_arr`, `bin_add_num`, ...)
and keep records abstract. That is mechanical, which is why it should be generated.

## Not done

- Loops: no theorem about a loop or an array callback yet, so `addSpaceToAnyEmptyMessages`
  and `colorIndexes` are only differential-tested. Core's spike shows loop invariants work on
  the same heap model; they need an `eachLoop` invariant lemma here.
- `parseChartDecimalPlaces` and `calculateFee` need lemmas for `Number.isInteger` and
  `Math.floor` on `num`; unfolding `num` makes Lean evaluate `2^1074`.
- Library calls outside a small list are `stuck`: `throw new` of an unseen class, callbacks
  stored in fields (`this.onChange(...)`), `Number`-to-string on non-integers. That accounts
  for the 93 stopped runs.
- Inheritance, getters, `static`, recursion, `async` and generators are `unsupported`.
- Preconditions stop at depth 3 of nested types (deeper types become `any`), and recursive types
  aren't expressible.

## What productising needs

1. A step generator, like Core's stepwise method: one lemma per statement, so a proof only
   states loop invariants and the final claim.
2. Specs for each library call on `Val` (strings, arrays, `Math`), proved once.
3. The `Is` precondition turned into the facts proofs use (field lookups, array contents) by
   a generated lemma per type.
4. A bridge per function from the typed view to this one, so the typed path stays the fast
   path and both read the code the same way (roadmap step 4).
5. Fixtures and mutants in the action like the typed path's, before any verdict uses it.

## Running it

```sh
CORPUS=~/corpus ./gen.sh          # only if the corpus changed; Gen/ is committed
node diff.mjs gen 60              # writes Diff.lean and diff-expected.json
# in the toolchain image, with the repository at /src:
OUT=/tmp/dyn-olean ./check.sh     # proofs, mutants, then the replay into /tmp/dyn-diff.txt
node diff.mjs check /tmp/dyn-diff.txt
```
