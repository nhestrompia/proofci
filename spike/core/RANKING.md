# What to build next

## Score on code the rules weren't tuned on

Eight repositories never used for tuning or earlier held-out tests (tldraw, Rocket.Chat,
plane, AFFiNE, medusa, umami, trigger.dev, cal.com; commits in the run's notes), with the
generator and tactics as of `fc125b0`, nothing changed during the run:

| | Count | Share |
|---|---:|---:|
| Pure functions | 2,785 | |
| Accepted | 224 | 8.0% of pure |
| Bridge generated | 213 | |
| Proved at 120 s, standard axioms | 176 | 78.6% of accepted, 6.3% of pure |

The proof rate matches the tuned 76% within noise (about ±5 points at this size), so the
tactics weren't overfitted. Acceptance is a lower bound: these clones had no packages
installed, unlike the tuned sample, so imported types counted as unknown. One repository
supplies 41% of the accepted functions.

The translator stops at a function's first problem, so a tally of its failures
undercounts everything behind that problem. Package types showed this: `extends`
errors fell from 90 to 0 across eight repositories, yet accepted functions only
rose from 106 to 110 of 2,677.

`typescript/survey/blockers.mjs` lists every blocker a function reaches, including
through its calls. It wraps the translator from outside, so it can't change what a
real translation accepts. On a small test its clean functions match the real
translator exactly.

The sample is the nine repositories from the third slice with real dependencies
installed: 13,767 top-level logic functions, of which 4,872 are pure. Another 5,152
class methods aren't counted, because the translator doesn't reach methods.

An early version of the tool missed a type's blockers after the first function that
used it, which inflated every clean count. The numbers here are from the fixed tool.

Pure functions the translator accepts:

| | Clean | Share |
|---|---:|---:|
| Before conditions | 211 | 4.3% |
| After conditions | 339 | 7.0% |
| After `lastIndexOf` and `charCodeAt` | 365 | 7.5% |
| After values in templates | 391 | 8.0% |
| After `new Set(array)` | 420 | 8.6% |
| After number built-ins and `?.` chains on strings | 464 | 9.5% |

The conditions work freed 128 functions, about half of the 243 forecast. The rest of
that row is mostly tests on `any` and `unknown`: `typeof` reaches 981 pure functions,
and those tests can't be translated until those types can.

Of those 339, 219 are proved: 140 of the third slice's 196, with none of its earlier
138 lost, and 79 of the other 143, whose rules were not tuned on them. The second
group ran on a busy machine with a 120-second limit, and 11 of its failures were
timeouts.

A later run on an idle machine, after fixing comparisons on narrowed enums, raised the
second group to 87. That fix reached proofs in functions already accepted: after
`a === "x"`, TypeScript reports `a` as the remaining literal, so `a === "y"` compared
a string with an enum. Of the 26 functions `lastIndexOf` and `charCodeAt` added, 18
are proved. Of the 26 that templates added, 18 are proved, and of the 29 that sets added, 13 are.
Of the 44 that number built-ins and `?.` chains added, 16 were proved at first.

Number division and `Math.floor`, `ceil` and `trunc` had no proof rules until these
functions needed them, and adding them raised the third slice from 142 to 151. Division
stays exact: `(n / 1000).toFixed(1)` only stays in the model when `n` is a multiple of
1000, so proofs of formatting code like that cover few inputs.

Work on the proof rate then took the total to 320 of the 464 accepted functions (69%):
every argument of `push` now lowers, `add` works on a set the function owns, and a value
assigned from a chain and tested later bridges. What's left is 87 stuck, 21 past the
120-second limit, 8 with other errors, and 28 that don't generate.

A further round took it to 350 of 464 (75%), losing none. Most of the gain was translator bugs,
not proof search: `filter` with a type guard, fields narrowed by tsc, `T extends {...}`, and
records used only inside a constant or callback. Raising the limit from 120 to 600 seconds
proved only 2 of the 21 timeouts, so timeouts need less search, not more time.

`switch` on a plain string, number or field then took it to 363 of 475. It reaches 273
functions but freed only 11 at once, because most of them have other blockers.

Reranking on single blockers instead of groups shows no large item left: each frees 40 to
80 functions. Dynamic data is not next, despite its size above: `any` reaches 1,235
functions but is the only blocker on 27, and all its kinds together are the only blocker
on about 60. The list below overstates it.

`add` and `delete` on sets aren't lowered, because they need proofs about mutation,
so those functions are accepted but can't bridge.

## Work ranked by what it frees, on pure functions

Each row counts the functions freed once everything above it is done.

| Work | Freed | Clean after |
|---|---:|---:|
| Smaller gaps: regex, `Map`, destructuring, names, array methods | 250 | 670 (13.8%) |
| Calls and types from outside: packages, classes, `new`, globals | 431 | 1,101 (22.6%) |
| Dynamic data: `any`, `unknown`, `Record`, casts, loose objects | 741 | 1,842 (37.8%) |
| Remaining conditions, mostly `typeof` and tests on dynamic data | 890 | 2,732 (56.1%) |
| Mutation of shared values | 667 | 3,399 (69.8%) |
| Recursive types | 795 | 4,194 (86.1%) |
| Closures | 483 | 4,677 (96.0%) |
| TypeScript settings and `async` | 194 | 4,872 |

Regular expressions sit inside the smaller gaps but aren't small: about 70 of that
row's functions pass one to `replace`, `replaceAll` or `split`, and the JavaScript
regex language has no model yet. It needs its own plan.

## Written types and assumptions

The rule that functions must write out their types costs little: 74% of pure functions
already do, through everything they reach. Of the 420 accepted, 116 would need an edit,
and 104 of those need just one function annotated.

Assumptions unlock much less than the rows above suggest. The row called calls and
types from outside is nearly all JavaScript's own built-ins, not packages. Pure functions
touching each kind of outside call:

| Declared in | Functions |
|---|---:|
| JavaScript's built-ins | 1,780 |
| The repository, such as methods on its own classes | 385 |
| Packages | 57 |
| Unresolved | 27 |

Of the 125 functions blocked only by outside calls, 120 need a built-in and 5 need a
package. `assumes` can't list built-ins, so its effect on this sample is about 5 functions.
Built-ins have public semantics that can be compared with Node, so they should be
modelled, not assumed.

The most used are `Array.isArray` (458 functions), `RegExp.test` (282), `Number.isFinite`
(186), `?.trim()` on an optional string (151 for `undefined`, 47 for `null`), `RegExp.exec`
(137), `Number()` (125), `Object.keys` (116) and `JSON.stringify` (107). Many of them take
`any`, which is why published types seemed not to translate.

## Limits

- These count what the translator would accept, not what bridges. Functions the rules
  weren't tuned on bridged at 55%, so every row overstates what gets proved.
- The freed counts depend on the order, and a later row can't be read alone.
- Placing a blocker in a group is a judgement call, made by matching its message.
- Skipping a failed statement can hide or add a follow-on blocker.
- Dynamic data is the largest row and the least certain: a cast or an `any` may have
  to become a stated assumption, which isn't the same as supporting it.
