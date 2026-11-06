# What to build next

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
In all, 279 of the 420 accepted functions are proved.

`add` and `delete` on sets aren't lowered, because they need proofs about mutation,
so those functions are accepted but can't bridge. A module constant computed through
a callback, such as `const NAMES = ROLES.map(...)`, doesn't bridge either: it reaches
the proof as one unsplit chain.

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

What the assumptions unlock is smaller than the rows above suggest, because a function
usually has other blockers too:

| Allowed | Clean | With the smaller gaps |
|---|---:|---:|
| Today | 420 (8.6%) | 670 (13.8%) |
| Outside calls whose published types translate | 493 (10.1%) | 810 (16.6%) |
| And casts, if they were listed | 504 (10.3%) | 833 (17.1%) |
| And `any` and `unknown` replaced with real types | 514 (10.6%) | 897 (18.4%) |

Only outside calls can be listed so far. Published types translate for 975 of the outside
calls' blockers and not for 1,476. Why those 1,476 fail hasn't been measured.

## Limits

- These count what the translator would accept, not what bridges. Functions the rules
  weren't tuned on bridged at 55%, so every row overstates what gets proved.
- The freed counts depend on the order, and a later row can't be read alone.
- Placing a blocker in a group is a judgement call, made by matching its message.
- Skipping a failed statement can hide or add a follow-on blocker.
- Dynamic data is the largest row and the least certain: a cast or an `any` may have
  to become a stated assumption, which isn't the same as supporting it.
