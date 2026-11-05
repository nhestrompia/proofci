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
