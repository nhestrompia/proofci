# Arithmetic contract review

These fixtures specify equations for every natural-number input `x`. A separate
reviewer checked the base and equivalent expressions in `corpus.py` against
these equations and supplied the counterexamples below for the defective
variants. This is a mathematical review of the fixtures, not maintainer
approval of a product baseline.

| Fixture | Required result | Defective variant fails at |
| --- | --- | --- |
| 1 | `x` | `x = 0` |
| 2 | `0` | `x = 0` |
| 3 | `x + 1` | `x = 0` |
| 4 | `x + x` | `x = 0` |
| 5 | `x * 3` | `x = 0` |
| 6 | `7` | `x = 0` |
| 7 | `(x + 1) * 2` | `x = 0` |
| 8 | `(x + 2) + 3` | `x = 0` |
| 9 | `x * 0 + 3` | `x = 0` |
| 10 | `x + 2 * x` | `x = 1` |

The separate precedence cases check `x + 1 * 2` and `(x + 1) * 2` against
`x + 2`. The latter fails at `x = 1`. The hostile-solution suite also tries a
shadow implementation, a substituted specification helper, a weakened
statement, a custom axiom, and `sorry` against a defective candidate.
