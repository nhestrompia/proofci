# Core slice: does the architecture hold on real code?

The spike showed the idea can work on samples. This slice asks a harder question: can
one general generator tie the typed view to Core for the functions the translator
already accepts, without per-function tuning?

## Criteria, fixed before the generator was written

**Corpus:** every function the translator accepts from the 23 surveyed public repositories.

**Split:** sort by the SHA-256 of `repo/file::name`. Odd last hex digit is the dev set, and
even is the held-out set. Held-out functions aren't read or run until the generator is
frozen, and it isn't changed after that run.

The architecture holds if all of these are true on the held-out set:

1. **Coverage:** at least 50% of functions get a checked bridge theorem.
2. **Generality:** the proof text comes from the function's signature and a shared
   tactic. Nothing in the generator names a function, file or repository.
3. **Soundness:** every bridge depends only on Lean's standard axioms. Every one of at
   least 10 deliberate mistranslations is rejected.
4. **Speed:** no function takes more than 60 s, not counting Lean's startup.

A function counts as bridged only if its callees are bridged too. Failures are reported
by reason, and any failure that turns out to be a translator bug is reported as one.
