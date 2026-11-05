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

## Results

The generator was frozen at commit `cc36635`, then run once on the held-out set. All four
criteria passed.

| Criterion | Required | Result |
|---|---|---|
| Coverage | At least 50% of held-out functions | 52 of 87, or 60% |
| Generality | No function-specific proof text | The generator names no function, file or repository |
| Soundness: axioms | Standard axioms only | Every counted bridge uses only `propext`, `Classical.choice` and `Quot.sound` |
| Soundness: mistranslations | At least 10, all rejected | 87 of 87 rejected, all inside the proof |
| Speed | 60 s at most | 36.7 s at worst, 2.3 s median |

The dev set reached 67 of 102, so 119 of the 189 accepted functions have a bridge. One
reporting bug was corrected after the run, with no change to the generator: the report
script excluded any function whose name contained the word "error". That moved the
held-out count from 50 to 52.

### What stopped the rest

| Reason | Held-out | Dev |
|---|---:|---:|
| Callback methods such as `map`, `filter` and `find` | 10 | 12 |
| `for`, `while` or `continue` | 6 | 4 |
| Division or rounding | 6 | 5 |
| A missing proof rule | 7 | 2 |
| Lowering crash on a class-typed call | 4 | 0 |
| Other syntax the lowering lacks | 2 | 8 |
| Local array mutation | 0 | 2 |
| Tagged unions | 0 | 1 |
| Proof timeout | 0 | 1 |
| Total | 35 | 35 |

### Comparison with Node

The bridge ties the typed view to Core, and the action's differential check ties the view
to Node. Run together on the bridged functions, 4,163 inputs agree, none disagree, and 98
leave the safe-integer model, where the view stops. That covers 107 of the 119 functions:
12 sit in files that don't load in Node. One of the 107 replayed only part of its inputs,
because its generated cases didn't compile.

Core's built-ins use the runtime's own functions, so their match to JavaScript rests on
this comparison, not on a proof.

### Scaling

Real functions are small: the longest typed view in the dev set is 75 lines. Synthetic
functions show a limit, though, because this generator splits every path before it walks
Core. It doesn't yet use the spike's joining rule.

| Shape | Size | Result |
|---|---|---:|
| Straight line | 40 statements | 10 s |
| Straight line | 160 statements | 54 s |
| Straight line | 640 statements | Over 120 s |
| Early returns | 20 branches | 116 s |
| Early returns | 80 branches | Over 120 s |
| Consecutive `if`s | 6 | 31 s |
| Consecutive `if`s | 12 | Over 120 s |

The spike's number-only generator handled the same shapes in linear time, so a fix is known,
but it hasn't been carried into this generator. Long functions will fail until it is.

### What this doesn't show

- **Translator coverage.** A bridge can only exist for code the translator accepts: 189 of
  the surveyed functions. The surveyed repositories hold about 1,457 pure functions.
- **Failure.** A bridge says that when the typed view returns a value, Core returns the
  same one. It says nothing about inputs where the view stops.
- **Features outside these functions.** Closures, loops and classes still have no bridge,
  only the direct Core proofs from the spike.
- **`lower.mjs` is still trusted.** It was extended for this slice, and it defines what the
  code means.
- **Input shape.** Inputs are assumed to be plain data that matches the declared types.
  Nothing checks this at runtime.

## Reproducing

```sh
node bridge3.mjs corpus-heldout.tsv out    # one Lean file per function
lake env lean out/F0.lean                  # checks one bridge
python3 mutate.py out mutants 8            # plants mistranslations
node diffchain.mjs out chain /tmp/ts-corpus  # prepares the Node comparison
```

The corpus is the survey's checkout of public repositories, at `CORPUS` or `/tmp/ts-corpus`.
