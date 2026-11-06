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

| | Functions | Clean today |
|---|---:|---:|
| All top-level logic | 13,767 | 232 (1.7%) |
| Pure | 4,872 | 227 (4.7%) |

Most functions need several things: 7,788 of the 13,767 reach six or more blockers,
and only 632 reach exactly one.

## Work ranked by what it frees, on pure functions

Each row counts the functions freed once everything above it is done.

| Work | Freed | Clean after |
|---|---:|---:|
| Conditions: truthiness, `===`, `&&` and `\|\|`, null checks | 308 | 535 (11.0%) |
| Smaller gaps: destructuring, `new Set(...)`, regex-free string methods, names | 433 | 968 (19.9%) |
| Calls and types from outside: packages, classes, `new`, globals | 649 | 1,617 (33.2%) |
| Dynamic data: `any`, `unknown`, `Record`, casts, loose objects | 1,246 | 2,863 (58.8%) |
| Mutation of shared values | 713 | 3,576 (73.4%) |
| Recursive types | 642 | 4,218 (86.6%) |
| Closures | 473 | 4,691 (96.3%) |
| TypeScript settings and `async` | 181 | 4,872 |

## Limits

- These count what the translator would accept, not what bridges. The third slice
  bridged 70% of accepted functions, so every row overstates what gets proved.
- The freed counts depend on the order, and a later row can't be read alone.
- Placing a blocker in a group is a judgement call, made by matching its message.
- Skipping a failed statement can hide or add a follow-on blocker.
- Dynamic data is the largest row and the least certain: a cast or an `any` may have
  to become a stated assumption, which isn't the same as supporting it.
