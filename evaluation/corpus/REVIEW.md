# Reviewed evaluation properties

Each property is an approved contract `target x = rhs` for every natural number `x`,
optionally restricted by a precondition on `x`. The verifier admits one definition,
`def target (x : Nat) : Nat`, built from `x`, literals, `+`, `*` and parentheses. Collections
and state transitions are therefore modelled by a size or successor function over `Nat`. The
companion Lean modules in each package are real collection or state-machine code that the
verifier does not admit; scenarios use them to measure unsupported-input reporting.

The truth columns were reviewed by hand and are rechecked by `oracle.py`, which normalizes
both sides to polynomials (or enumerates the bounded precondition domain). The oracle does not
reuse the verifier's parser. `evaluate.py check` fails if a reviewed value and the oracle disagree.
A counterexample is the smallest input at which the property fails.

## arithmetic (arithmetic)

Metered fee schedule: three fee units per item plus a fixed charge of two.

| Candidate | Definition |
| --- | --- |
| base | `def target (x : Nat) : Nat := x * 3 + 2` |
| equivalent | `def target (x : Nat) : Nat := 2 + (x + x + x)` |
| violating | `def target (x : Nat) : Nat := x * x + 2 * x + 2` |
| shadow | `def target (x : Nat) : Nat := 3 * x + 2` |

| Property | Contract | Meaning | Base | Equivalent | Violating (counterexample) |
| --- | --- | --- | --- | --- | --- |
| `fee-definition` | `target x = x * 3 + 2` | The fee is three units per item plus two. | holds | holds | fails (x = 2) |
| `fee-commuted` | `target x = 2 + 3 * x` | The same schedule written with the fixed charge first. | holds | holds | fails (x = 2) |
| `fee-repeated-addition` | `target x = x + x + x + 2` | Charging each item as three separate units gives the same fee. | holds | holds | fails (x = 2) |
| `fee-split-schedule` | `target x = (x + 1) * 2 + x` | A two-unit schedule on x + 1 items plus one unit per item equals the fee. | holds | holds | fails (x = 2) |
| `fee-grouped-charge` | `target x = x * 2 + (x + 2)` | Two units per item plus one unit and the fixed charge equals the fee. | holds | holds | fails (x = 2) |
| `fee-literal-coefficients` | `target x = x * (1 + 1 + 1) + 1 * 2` | The coefficient three and charge two may be written as sums. | holds | holds | fails (x = 2) |
| `fee-empty-order` | `x = 0 → target x = 2` | An empty order costs only the fixed charge. | holds | holds | holds |
| `fee-single-item` | `x = 1 → target x = 5` | One item costs five. | holds | holds | holds |
| `fee-four-items` | `x = 4 → target x = 14` | Four items cost fourteen. | holds | holds | fails (x = 4) |
| `fee-small-orders` | `x < 2 → target x = x * 3 + 2` | Orders below two items follow the schedule. | holds | holds | holds |

## collections (collections)

Flattened grid buffer: x rows of x + 1 cells (one terminator cell per row) plus a two-cell header.

| Candidate | Definition |
| --- | --- |
| base | `def target (x : Nat) : Nat := x * (x + 1) + 2` |
| equivalent | `def target (x : Nat) : Nat := x * x + x + 2` |
| violating | `def target (x : Nat) : Nat := x * x + 2` |
| shadow | `def target (x : Nat) : Nat := (x + 1) * x + 2` |

| Property | Contract | Meaning | Base | Equivalent | Violating (counterexample) |
| --- | --- | --- | --- | --- | --- |
| `size-definition` | `target x = x * (x + 1) + 2` | Each of x rows has x + 1 cells, plus a two-cell header. | holds | holds | fails (x = 1) |
| `size-expanded` | `target x = x * x + x + 2` | Cell count expanded into payload, terminators and header. | holds | holds | fails (x = 1) |
| `size-row-major` | `target x = (x + 1) * x + 2` | Counting by row width first gives the same size. | holds | holds | fails (x = 1) |
| `size-header-first` | `target x = 2 + x + x * x` | Header, terminators and payload may be counted in any order. | holds | holds | fails (x = 1) |
| `size-split-header` | `target x = x * (x + 1) + 1 + 1` | The header is two single cells. | holds | holds | fails (x = 1) |
| `size-empty` | `x = 0 → target x = 2` | An empty grid contains only the header. | holds | holds | holds |
| `size-one-row` | `x = 1 → target x = 4` | One row holds one cell and its terminator. | holds | holds | fails (x = 1) |
| `size-two-rows` | `x = 2 → target x = 8` | Two rows of three cells plus the header. | holds | holds | fails (x = 2) |
| `size-three-rows` | `x = 3 → target x = 14` | Three rows of four cells plus the header. | holds | holds | fails (x = 3) |
| `size-small-linear` | `x < 2 → target x = x * 2 + 2` | Below two rows the size grows by two per row. | holds | holds | fails (x = 1) |

## state (state transitions)

Two-phase counter transition: increment the state, double it, then add a three-step settle.

| Candidate | Definition |
| --- | --- |
| base | `def target (x : Nat) : Nat := (x + 1) * 2 + 3` |
| equivalent | `def target (x : Nat) : Nat := x + x + 5` |
| violating | `def target (x : Nat) : Nat := (x + 1) * 2 + 1` |
| shadow | `def target (x : Nat) : Nat := 5 + x * 2` |

| Property | Contract | Meaning | Base | Equivalent | Violating (counterexample) |
| --- | --- | --- | --- | --- | --- |
| `step-definition` | `target x = x * 2 + 5` | The step doubles the state and adds five. | holds | holds | fails (x = 0) |
| `step-two-phase` | `target x = (x + 1) * 2 + 3` | Increment, double, then settle by three. | holds | holds | fails (x = 0) |
| `step-additive` | `target x = x + x + 5` | Doubling is adding the state to itself. | holds | holds | fails (x = 0) |
| `step-offset-first` | `target x = 5 + 2 * x` | The offset may be written before the scaled state. | holds | holds | fails (x = 0) |
| `step-shifted` | `target x = (x + 2) * 2 + 1` | A two-step shift then doubling, settled by one. | holds | holds | fails (x = 0) |
| `step-initial` | `x = 0 → target x = 5` | The initial state steps to five. | holds | holds | fails (x = 0) |
| `step-from-five` | `x = 5 → target x = 15` | State five steps to fifteen. | holds | holds | fails (x = 5) |
| `step-from-fifteen` | `x = 15 → target x = 35` | State fifteen steps to thirty-five. | holds | holds | fails (x = 15) |
| `step-early-states` | `x < 3 → target x = x * 2 + 5` | States below three follow the doubling rule. | holds | holds | fails (x = 0) |
| `step-boolean-states` | `x ≤ 1 → target x = x * x * 2 + 5` | On states zero and one, the step equals the squared form. | holds | holds | fails (x = 0) |

The `shadow` definition is a separate correct definition used only by source-substitution
scenarios; every property holds for it. Reviewed for ticket 22; this is a review of the
evaluation fixtures, not maintainer approval of a production baseline.
