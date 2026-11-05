# Core slice 2: callbacks, loops and long functions

The first slice left two risks: nothing bridges closures or loops, and the general generator
lost the spike's linear scaling. This slice tests both before a full build.

## Criteria, fixed before the work

**Corpus:** functions the translator accepts from ten public repositories that no earlier
test used. The list is fixed before any new proof work. These functions aren't read or run
until the generator is frozen, and it isn't changed after that run.

**Tuning set:** the 189 functions from slice 1, including its 87 held-out functions.

The slice passes if all of these are true on the fresh corpus:

1. **Feature coverage:** at least 50% of functions whose typed view has a loop or a callback
   get a checked bridge.
2. **Overall coverage:** at least 60% of all functions get a checked bridge.
3. **Soundness:** every counted bridge uses only standard axioms, and at least 20 planted
   mistranslations inside loops and callbacks are all rejected.
4. **Node:** no disagreement with Node on bridged functions.
5. **Speed:** no real function takes more than 60 s.
6. **Scaling:** 640 statements, 320 early returns and 160 consecutive `if`s each check in
   60 s or less.

A function counts as bridged only if its callees and callbacks are bridged too.

## Results

The generator was frozen at commit `e8b687d`, then run once on 130 functions from ten
repositories it had never seen. Four criteria passed and two failed.

| Criterion | Required | Result | |
|---|---|---|---|
| Feature coverage | At least 50% | 9 of 25, or 36% | **Failed** |
| Overall coverage | At least 60% | 86 of 130, or 66% | Passed |
| Axioms | Standard only | Every counted bridge | Passed |
| Mistranslations in loops and callbacks | At least 20, all rejected | 54 rejected by the proof, none accepted | Passed |
| Node | No disagreement | 3,227 agree, 0 disagree | Passed |
| Speed | 60 s at most | 28.7 s at worst, 1.4 s median | Passed |
| Scaling: 160 consecutive `if`s | 60 s | 15 s | Passed |
| Scaling: 320 early returns | 60 s | 37 s | Passed |
| Scaling: 640 statements | 60 s | 71 s | **Failed** |

Of the 25 feature functions, 16 have loops (5 bridged) and 10 have callbacks (4 bridged);
one has both.

Details on the soundness and Node results:

- **Mutants:** 63 were planted in functions with loops or callbacks. Beyond the 54 the proof
  rejected, 6 didn't compile and 3 timed out, so those 9 aren't counted as rejections.
- **Node:** this compared 83 of the 86 bridged functions. The other 3 sit in files that don't
  load in Node. 53 inputs left the safe-integer model.

The tuning set, which these changes were built against, reached 135 of 189, up from 119.

## What changed since slice 1

- **Callbacks:** `map`, `filter`, `some`, `every` and `find` are proved by induction. An arrow
  written in place runs in the caller's variables, and lowering refuses one that writes
  outside itself.
- **Loops:** `for...of`, `while`, C-style `for`, `forEach`, `break`, `continue` and `return`
  inside a loop. `loop_ind` gives induction over Aeneas's `loop` with no termination measure.
- **`push`:** on a local array, lowering treats `xs.push(v)` as a new array. It does this only
  when a syntactic check finds no alias, so this rule is trusted, not proved.
- **The walker:** Core and the typed function advance together, statement by statement, so
  early returns no longer explore every path. A join rule handles `if (c) x = e`.

## What stopped the rest

Of the 16 feature functions that failed, 10 reached the prover and 6 stopped in lowering.

| Reason | Functions |
|---|---:|
| Lowering: `new`, spread, `replace` and generics | 6 |
| Loop state the invariant doesn't describe | 2 |
| Reading a string by index | 2 |
| Proof timeout | 2 |
| `reduce`, which has Core semantics but no proof rule | 1 |
| Reading a field of an indexed array element | 1 |
| A value expression the rules don't cover | 1 |
| A term Lean's kernel rejected | 1 |

## Bugs this found

- **Lowering:** `while (i < n)` was lowered as `while (true)`, because `.condition` only exists
  on `for` statements. The bridge refused to check, which is how it was found.
- **Generator:** a failed step was logged and replaced with `sorry` while the search carried
  on. The axiom check would have rejected the result, so nothing unsound was counted, but it
  sent proofs down wrong paths.
- **Kernel:** on one function the tactics built a term that Lean's kernel rejected. It's
  counted as failed, and the cause isn't diagnosed yet.

## What this doesn't show

- **Rounding.** Division and fractions are still unproved.
- **Closures as values.** A callback stored in a variable has no bridge. Only arrows written
  in place do, so this slice doesn't remove the closure risk from the spike.
- **Classes.** Still no bridge.
- **Mutation beyond `push`.** Writes to fields, or to an index, have no rule.
- **`lower.mjs` grew.** It is trusted and now holds the `push` and callback checks.
