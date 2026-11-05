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

## Results

The generator was frozen at commit `22eb67d`, then run once on 196 functions from ten
repositories it had never seen. All six criteria passed.

| Criterion | Required | Result |
|---|---|---|
| Feature coverage | At least 50% | 26 of 41, or 63% |
| Overall coverage | At least 65% | 138 of 196, or 70% |
| Axioms | Standard only | Every counted bridge |
| Mistranslations in loops and callbacks | At least 20 rejected, none accepted | 97 rejected, 0 accepted |
| Node | No disagreement | 4,915 agree, 0 disagree |
| Speed | 60 s at most | 14.2 s at worst, 1.5 s median |
| 640 statements, run alone | 60 s | 25 s |
| 320 early returns, run alone | 60 s | 36 s |
| 160 consecutive `if`s, run alone | 60 s | 14 s |

Of the 41 feature functions, 18 have loops (13 bridged) and 25 have callbacks (14 bridged).
Two have both, and one of those is bridged.

The tuning set reached 251 of 319.

### Limits on those numbers

- **The Node result needed a fix.** The first run showed 29 disagreements in one function.
  `differential.mjs` was running that function against a stub, because its constant was
  imported through a package index the translation didn't reach. After fixing that and
  rerunning everything, nothing disagrees. The fix changed the comparison, not the frozen
  generator.
- **Node covers 128 of the 138 bridged functions.** The other 10 are in files that don't load
  in Node or that ran out of memory. 165 inputs left the safe-integer model.
- **Mutants:** 116 were planted, across 25 functions. Besides the 97 rejected by the proof, 17
  didn't compile and 2 timed out, so those 19 aren't counted either way.
- **The scaling numbers come from before the freeze,** on the same generator code.

## What stopped the rest

| Reason | Functions |
|---|---:|
| Proof failures, not yet sorted by cause | 22 |
| Division or rounding | 17 |
| Lowering: `.has` on a `Set`, and one `new` | 6 |
| Lowering: object spread and other object shapes | 4 |
| Lowering: tagged unions | 3 |
| Lowering: `case` fall-through | 3 |
| Proof timeout | 3 |

## The kernel rejection from slice 2

`carry` assumed that every variable a step assigns belongs to the enclosing loop's frame. A
variable assigned in a callback nested inside a loop doesn't. The tactic then built a proof
of a false membership claim, and Lean's kernel rejected it. So the system behaved safely, and
the tactic now drops that frame fact.

## Bugs this found

- **Translator:** `xs[i]!.length` produced `tmp.length`, a Lean `Nat` where a `Js.Num` belongs.
  That code didn't type-check, so it failed closed. Fixed.
- **Translator, not fixed:** `getRunCommand` in the slice 2 corpus returns an enum where the
  typed code needs a `Js.Str`. It fails closed in the same way.
- **Node check:** the stubbed import above. It was a false alarm that would have blocked a
  correct pull request.
- **Generator:** `tauto` took most of the time on large conditions, and rule order made the
  search exponential on long `||` chains. Fixing both took 640 statements from 71 s to 25 s.

## What this doesn't show

- **Rounding.** 17 of the 58 failures here need division or rounding, which is still unproved.
- **`Set` and `Map`.** Core has no model of them.
- **Stored closures and classes.** Still no bridges.
- **Mutation beyond `push`.** Field and index writes have no rule.
- **`lower.mjs` is still trusted,** and it has grown again.
- **Core hasn't been run against test262.**
- **Translator coverage is still the larger limit.** Bridges only cover what the translator
  accepts.
