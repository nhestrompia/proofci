# Dynamic path spike

Roadmap step 2 in [docs/typescript.md](../../docs/typescript.md): translate to one Lean type of
JavaScript values plus an explicit heap, so TypeScript types become preconditions instead of
Lean types. Not wired into the action.

## Verdict

Go. Real corpus functions that the typed path rejects translate, run like Node, and can be
proved. The go condition from the first round, proofs as short as typed ones, is met for
straight-line code: one tactic, `dsteps`, runs a generated function statement by statement,
so `transfer_conserves` is `unfold; dsteps` plus the final arithmetic, as on the typed path.
Loops cost what they cost on the typed path: the user writes the invariant.

| Question | Result |
|---|---|
| Does one value type cover the rejected shapes? | Yes: `unknown`, unions, shared objects, closures that assign captured variables, and classes, from 6 corpus functions and 2 fixtures |
| Does it match Node? | 1,200 random runs over 20 functions: 1,107 agree on the result and on every input after the call, 93 stop in the model, none differ |
| Can users prove things about it? | Yes, 10 theorems below, including a `for ... of` loop, a loop with captured variables and array callbacks over shared objects |
| Does a wrong translation fail? | 74 of 74 one-line mutants of the proved functions fail to check |
| Proof checking time vs typed | Same order: about 2 s for imports, then under 0.1 s for `transfer_conserves` and about 4 s for the two loop proofs; `ts-bank`'s typed file takes 2.1-2.7 s |
| Proof writing effort vs typed | Same for straight-line code: `transfer_conserves` is 2 lines here and 2 (`unfold; step*`) typed. Loops: 16 lines for `sumAmounts`'s `for ... of`, 50-105 when the loop writes to the heap, most of it heap bookkeeping after each write |

The first round's differential test found that Core's `Math.min` and `Math.max` lost `-0`
(`Math.min(-0, 500)` is `-0` in Node). Core now computes them on doubles (`F64.fmin`/`fmax`,
checked against Node in `f64cases.mjs`), and this spike uses Core's again.

## Step 4: the typed view equals the dynamic one

[bridge.mjs](bridge.mjs) reads a function list, runs the production translator
(`typescript/translate.mjs` with `requireTypes`) for the typed view and `dyn.mjs` for the
dynamic one, and writes one Lean file per function with a theorem of this form:

```lean
theorem src_ledger_transfer_dyn (h0 : crep h p0 v0) (h1 : crep h p1 v1)
    (hr : src.ledger.transfer p0 p1 = ok r) :
    Spec (D.transfer v0 v1) h fun v h' => h <+: h' ∧ crepOpt .null h' r v
```

`crep h a v` ([Bridge.lean](Bridge.lean)) says typed value `a` is JavaScript value `v` in heap
`h`: a number as any double equal to it, `-0` included (`NumIs`, as Core's `IsInt`), a string
as itself, arrays and records at a location with each element related, `none` as `null` or
`undefined`. It is the `Is` precondition made exact. The proof is the same for every function:
unfold both sides, then `rsteps` steps them together. It uses `Rel t d h Q` ("if typed `t`
returns `r`, dynamic `d` from `h` returns a value related to `r` by `Q`") and one lemma per
typed operation, proved once in [Bridge.lean](Bridge.lean): `rel_add`, `rel_sub`, `rel_mul`,
`rel_rem`, `rel_floorDiv`, `rel_ceilDiv`, `rel_truncDiv` and `rel_neg` pair a typed operation
with its dynamic twin on any operands related by `NumIs`; `bin_lt_is` and the other
comparisons turn a dynamic comparison into the typed one; `rel_min_ok` relates `Math.min`;
`rel_len`/`rel_slen` relate `length`; `rel_map`, `rel_filter` and `rel_findIndex` relate the
array callbacks on numbers through `Js.map`'s recursion on one side and `eachLoop` on the other;
`rel_padStart` relates `padStart` through Core's primitive; `rel_some`, `rel_every` and
`rel_reduce` relate those callbacks the same way; `rel_div`, `rel_max`, `rel_dneg`,
`rel_dtoNum`, `rel_trim`, `rel_lastIndexOf` and the `rel_isArray_*` lemmas relate `/`,
`Math.max`, unary `-`, `+b` on booleans, `trim`, `lastIndexOf` and `Array.isArray`;
`rel_arr` relates an array literal; `CRep (Option α)` covers optional fields; `rel_forOf` relates a `for ... of`
loop with one mutable variable, Aeneas's `loop` on one side (by `Core.loop_ind`) and `forLoop`
on the other; `rel_tail` handles an operation in tail position; `rel_ok` ends both sides;
`rel_dbind` takes a dynamic step the typed view doesn't have (a field read). A typed `if` is
split together with the dynamic one, with contradictory branches closed by `omega`. `Rel`
allows any dynamic result type, so a loop body (`M (ForInStep Val)`) steps with the same
lemmas. Nothing is written per function.

| Measure | Result |
|---|---|
| Functions tried | 83: `ts-bank` (3), `corpus-gaps.tsv` (45), `corpus-rem.tsv` (35) |
| Generated | 72 (65 before); `dyn.mjs` now translates `while` and `for (;;)` |
| Proved | 57 (38 before): `transfer`, `calculateFee`, `sumAmounts`, 25 gaps fixtures, 29 in `corpus-rem.tsv` |
| Check time | 15 files take 2 s, 26 take 3 s, 11 take 4 s, 3 take 5-6 s, `listCount` 23 s, `validateDate` 34 s |
| Timeouts (45 s) | 0 |
| Wrong typed views | MUTS, counting proved bridges only; 3 new kinds: `some` for `every`, `every` for `some`, `Math.min` for `Math.max` |
| Not proved | 15: 6 stop at a call with no lemma, 3 call something `dyn.mjs` turns into `stuck`, 3 are `while`/`for` loops, 3 test a nullable field for `null` or `undefined` |

New since the last round: `/` (`halfIfEven`), `some` (`anyMultiple`), `every` (`allOdd`),
`reduce` (`pagesFor`), `Math.max` (`orCall`), `trim` with `slice` (`andCall`), `+b`
(`flagCount`), `Array.isArray` (`listCount`), `lastIndexOf` (`lastTag`), optional fields
(`withHole`, `withUndefined`, `withNulls`, `nested`, `slotOf`). The 4 open goals are closed:
`orConditional` and `negativeLiterals` needed number truthiness (`truthy_numIs`),
`callFour` and `validateDate` call other functions, which the generator now unfolds.
`sumPresent` proves through `rel_arr`. `dyn.mjs` changes: `+true` is `1` and `lastIndexOf`
works on arrays of strings; `while (c) S` and `for (init; c; u) S` become a Lean `for` over
`fuel`, at most 2^20 rounds, then `stuck`. A `continue` in a `for (;;)` body, a non-`let`
initializer and a loop variable captured by a closure are unsupported. `whileLoop_spec` in
[Dyn.lean](Dyn.lean) is the invariant rule: each round keeps the invariant and lowers a measure
below the fuel. The Node comparison now has 22 functions, including `sumIndexed` (`for (;;)`)
and `halvings` (`while`): 2,200 runs, 2,056 agree, 144 stop, 0 differ.

Still not proved: `at`/`!` (`orIndex`), `padEnd`, string-to-number, `flat`, number-to-string,
and `at`/`strAt`/`repeat`, which `dyn.mjs` still turns into `stuck`. `boxOrZero`,
`boxIsUndef` and `slotUndef` test a field typed `number | null` (or `| undefined`) for one of the two;
`crep` relates `none` to both, so the comparison can't be decided. The generator would need the
nullable kind per type. No relational lemma pairs the typed path's loops with `whileLoop` yet,
so `digitSum`, `gcd` and `powersOfTwo` stop at the loop; no fixture proof uses
`whileLoop_spec` yet.

Verdict: go for continuing, still no-go for replacing Core's bridges. 57 of 72 generated
bridges prove with no timeouts; Core's bridges cover 22 of 24 original gaps fixtures and 32 of
35 in `corpus-rem.tsv`. What's left is the typed-loop lemma for `while`/`for`, the nullable
kind in `crep`, and a lemma per remaining call.

How it fits with Core's bridges: today `bridge3.mjs` proves the typed view simulates Core, and
Core is trusted to be JavaScript, checked against Node by `differential.mjs`. This bridge
proves the typed view against `M` instead. In a product it would take over where it proves,
with the Core bridge as fallback. Either way `typescript/translate.mjs` stays outside the
trusted base, because its output is checked. Replacing the Core bridge also removes the
lowering (`lower.mjs`) and the per-form simulation lemmas (`Spike/Sim.lean`) from what a proof
depends on. What stays trusted: Lean, `dyn.mjs`'s reading of TypeScript, `Dyn.lean`'s
operations (checked against Node by `diff.mjs`), and `crep`, which is small but says what a
typed value means. `M` reuses Core's `Val`, `Heap` and `F64`, so there is one model of values
to trust, not two.

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
| [bridge.mjs](bridge.mjs), [Bridge.lean](Bridge.lean) | Step 4: generates, per function, a proof that the production translator's typed view equals the dynamic one |
| [bridgecheck.sh](bridgecheck.sh), [mutate_bridge.mjs](mutate_bridge.mjs) | Checks the generated bridges; plants wrong typed views in the proved ones |

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
| `addSpace_spec` | `addSpaceToAnyEmptyMessages` returns the same messages, and every message whose content trims to nothing now has `" "` and the others keep theirs, even when a message is listed twice |
| `colorIndexes_spec` | Each item comes out colored `"none"` if empty and `c` plus its place among the non-empty ones otherwise; an item that already has its color is returned as is, the others are copies |
| `bump_adds` | A method call adds to the object it is called on |
| `bumpBoth_shared` | The same counter passed twice is bumped twice |
| `bumpBoth_separate` | Two counters are bumped once each |
| `transfer_conserves` | `transfer` keeps the total and never overdraws, the typed path's theorem restated |
| `queue_keeps_reference` | `queue` stores the caller's object, so the history ends with the same reference |
| `sumAmounts_sum` | `sumAmounts` over an array of integers returns their sum when every partial sum is a safe integer, and leaves the heap alone |
| `messageIsEmpty_arr` | A message with array content is empty exactly when every part has type `"text"` and text that trims to nothing |

Preconditions are facts about the heap (`h[l]? = some (.record fs)`, `fs.lookup "n" = some (num k)`),
which say the same as `Is` for the fields a proof needs.

## What it costs

Checking is cheap: each generated module takes about 1.7 s, the same as the typed module for
`ts-bank`. Writing straight-line proofs is now cheap too. `dsteps` (in [Dyn.lean](Dyn.lean))
rewrites with one lemma per operation (`spec_field`, `spec_setField`, `spec_get`, `spec_put`,
`bin_add_num`, ...), finds the heap facts each one needs through the writes made since
(`dheap`), proves arithmetic safe with `omega` and splits each branch. It never unfolds a whole
program, which would make Lean decide that two string literals differ by evaluation, or
evaluate `num`'s `2^1074`; both time out. So no lemma is generated per function: the
translator's output is regular enough that the per-operation lemmas cover every statement, and
`dyn.mjs` only had to emit object literals with distinct keys as plain lists.

Loops are the remaining cost. `eachLoop_spec`, `jsMap_spec` and, for `for ... of`,
`forLoop_spec` take an invariant and prove the loop from one step; `dsteps` does the step.
`sumAmounts_sum` is 16 lines with `forLoop_spec`, and `messageIsEmpty_arr`, the array branch,
is 25 with `jsEvery_spec`. What's left is stating where each object is after
the writes: `Frame` (objects from before the call are untouched), and for `colorIndexes` that
the two captured variables live in cells after the original heap. That bookkeeping is most of
the 105 lines of `colorIndexes_spec` and could be generated from which cells a function
allocates. That generation is not done, so `addSpace_spec` (50 lines) and `colorIndexes_spec`
(105) are unchanged.

## Not done

- Frame and cell facts are not generated per function, so loops that write to the heap still
  state where each object is by hand.
- `parseChartDecimalPlaces` and `calculateFee` need lemmas for `Number.isInteger` and
  `Math.floor` on `num`; unfolding `num` makes Lean evaluate `2^1074`.
- Library calls outside a small list are `stuck`: `throw new` of an unseen class, callbacks
  stored in fields (`this.onChange(...)`), `Number`-to-string on non-integers. That accounts
  for the 93 stopped runs.
- Inheritance, getters, `static`, recursion, `async` and generators are `unsupported`.
- Preconditions stop at depth 3 of nested types (deeper types become `any`), and recursive types
  aren't expressible.

## What productising needs

1. Frame and cell facts generated per function, so a loop proof states only its invariant.
2. Specs for each library call on `Val` (strings, arrays, `Math`), proved once.
3. The `Is` precondition turned into the facts proofs use (field lookups, array contents) by
   a generated lemma per type.
4. A bridge per function from the typed view to this one, so the typed path stays the fast
   path and both read the code the same way (roadmap step 4, spiked above): first a
   relational lemma per typed operation.
5. Fixtures and mutants in the action like the typed path's, before any verdict uses it.

## Running it

```sh
CORPUS=~/corpus ./gen.sh          # only if the corpus changed; Gen/ is committed
node diff.mjs gen 60              # writes Diff.lean and diff-expected.json
# in the toolchain image, with the repository at /src:
OUT=/tmp/dyn-olean ./check.sh     # proofs, mutants, then the replay into /tmp/dyn-diff.txt
node diff.mjs check /tmp/dyn-diff.txt
CORPUS=../../examples node bridge.mjs bridge-bank.tsv BGen   # step 4, typed views from translate.mjs
CORPUS=../core/fixtures node bridge.mjs ../core/corpus-gaps.tsv BGen/gaps
# in the image, after check.sh:
OUT=/tmp/dyn-olean ./bridgecheck.sh BGen    # proved or first error, per function
OUT=/tmp/dyn-olean node mutate_bridge.mjs BGen B0.lean
```
