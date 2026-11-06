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

The conditions work freed 128 functions, about half of the 243 forecast. The rest of
that row is mostly tests on `any` and `unknown`: `typeof` reaches 981 pure functions,
and those tests can't be translated until those types can.

Of those 339, 219 are proved: 140 of the third slice's 196, with none of its earlier
138 lost, and 79 of the other 143, whose rules were not tuned on them. The second
group ran on a busy machine with a 120-second limit, and 11 of its failures were
timeouts.

## Work ranked by what it frees, on pure functions

Each row counts the functions freed once everything above it is done.

| Work | Freed | Clean after |
|---|---:|---:|
| Smaller gaps: destructuring, `new Set(...)`, some string methods, names | 336 | 675 (13.9%) |
| Calls and types from outside: packages, classes, `new`, globals | 439 | 1,114 (22.9%) |
| Dynamic data: `any`, `unknown`, `Record`, casts, loose objects | 735 | 1,849 (38.0%) |
| Remaining conditions, mostly `typeof` and tests on dynamic data | 890 | 2,739 (56.2%) |
| Mutation of shared values | 666 | 3,405 (69.9%) |
| Recursive types | 794 | 4,199 (86.2%) |
| Closures | 479 | 4,678 (96.0%) |
| TypeScript settings and `async` | 194 | 4,872 |

## Limits

- These count what the translator would accept, not what bridges. Functions the rules
  weren't tuned on bridged at 55%, so every row overstates what gets proved.
- The freed counts depend on the order, and a later row can't be read alone.
- Placing a blocker in a group is a judgement call, made by matching its message.
- Skipping a failed statement can hide or add a follow-on blocker.
- Dynamic data is the largest row and the least certain: a cast or an `any` may have
  to become a stated assumption, which isn't the same as supporting it.
