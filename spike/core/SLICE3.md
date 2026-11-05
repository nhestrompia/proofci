# Core slice 3: closing the gaps in loops and callbacks

Slice 2 reached 66% overall but only 36% of functions with loops or callbacks, against a
50% target. Most failures were narrow gaps, not proof failures. This slice closes them.

## Criteria, fixed before the work

**Corpus:** functions the translator accepts from ten public repositories that no earlier
test used. The list is fixed before any new proof work, and its functions aren't read or run
until the generator is frozen. The generator isn't changed after that run.

**Tuning set:** the 319 functions from slices 1 and 2.

The slice passes if all of these are true on the fresh corpus:

1. **Feature coverage:** at least 50% of functions whose typed view has a loop or a callback
   get a checked bridge. This is measured from each function's typed view.
2. **Overall coverage:** at least 65% of all functions get a checked bridge.
3. **Soundness:** every counted bridge uses only standard axioms. At least 20 planted
   mistranslations inside loops and callbacks are rejected by the proof, and none is accepted.
   Mutants that don't compile or that time out aren't counted either way.
4. **Node:** no disagreement with Node on bridged functions.
5. **Speed:** no real function takes more than 60 s.
6. **Scaling:** 640 statements, 320 early returns and 160 consecutive `if`s each check in
   60 s or less, each run alone.

A function counts as bridged only if its callees and callbacks are bridged too. The kernel
rejection seen in slice 2 is diagnosed and reported, whatever the cause.
