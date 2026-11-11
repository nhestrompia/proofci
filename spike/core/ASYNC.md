# `async` in the Core spike

What was added, why each part is trusted, and how each part is tested. The design and the
measurements behind it are in the study that preceded this work (`DESIGN.md` there).

## The model

An `async` function is a sequential computation over an **oracle** and a **history**. `await` of
an outside call asks the oracle, which may look at the call and at everything asked before it, and
adds the call and its answer to the history. A rejection is an outcome, an `Error` object. A
guarantee proved for every oracle holds for every real run, including runs where other tasks
changed the database in between, because a real run answers its n-th outside call with some value
or rejection, and some oracle does the same.

Three places hold the meaning, and they are checked against each other by tests, not by a theorem:

| | where | what it is |
|---|---|---|
| the view | `ProofciAsync.lean` (+ `typescript/translate.mjs`) | `Eff`, what users prove things about |
| Core's reading | `CoreAsync.lean` (+ `lower.mjs`) | an executable semantics of async statements on top of Core |
| Node | `typescript/differential.mjs`, `asynccheck.mjs`, `asynccore.mjs` | the real function against scripted stand-ins |

## Trusted changes, and why

* **`ProofciAsync.lean`** (new module, in `spike/core` and `proofci/lean`, byte-identical). It is
  new rather than part of `ProofciJs.lean` so that a workspace that has no async code builds the
  same libraries as before, and so that the synchronous proofs cannot be disturbed. It declares no
  axioms. The things in it that a proof leans on are `Eff.bind`, `Eff.call` (one step, one event in
  the history), `Eff.throw`, `Eff.tryCatch`, `Eff.tryFinally` and `Eff.loop`. `Result.fail` still means
  "left the model" and is never caught.
* **The hazard rule** (`typescript/hazard.mjs`, used by `translate.mjs` and `lower.mjs`). The
  sequential reading is wrong if another task changes in-process state the function reads after an
  `await`. The rule is syntactic: after the first `await` (or anywhere in a loop that contains one), no
  variable declared outside the function is read unless it is a function, an import of a function or
  class, or a `const` of an immutable type. It is the only thing between the sequential reading and
  a lost update, so `hazardcheck.mjs` is its negative control: the lost-update pattern is refused and
  loses an update in Node in 200 of 200 runs when run twice at once. The rule is conservative: it also
  refuses a counter that is incremented atomically after the `await`.
* **The standing assumption** (arguments are not changed by their caller while a call is pending)
  cannot be checked. The same file finds where a function relies on it, and the report says so for
  every guarantee.
* **`CoreAsync.lean`** adds a layer above Core and leaves `Core.lean` alone. This is deliberate:
  the synchronous Core and the 500 or so proofs about it keep exactly the semantics they were proved
  against, and the generated text of every existing bridge is byte-identical (checked on all 508
  functions of the tuned and fresh sets). The layer is small: `await`, `try`/`catch`/`finally`, `throw`,
  and loops and branches around them, with plain Core statements in between. It is executable and
  tested against Node, and it has no `sorry` because it has no theorem.
* **`lower.mjs`** lowers an async function to `CoreAsync` only when asked (`eff`). Without it the first
  spike's lowering (jobs split at each `await`) is used, as before. Awaits are moved before the
  statement that contains them, in evaluation order. An `await` that is not certain to run (right of
  `&&`, a branch of `?:`) is refused. One correction to the existing lowering came out of the tests:
  `xs?.includes(v)` on an array was lowered as the string method.

## Tests

* `typescript/translate.test.mjs`: the translator's async forms, what it refuses, and the hazard rule.
* `asynccheck.sh <out> [cases]`: the Lean view against Node, with the trace of calls compared.
* `mutate_async.sh <out> <mutants>`: wrong translations are planted in the view (dropped effect calls,
  swapped order, wrong catch paths, flipped branches, dropped throws and so on); each must be rejected.
* `asynccore.sh <out> [cases]`: Core's reading against Node, the same comparison.
* `mutate_core_async.sh <out> <mutants>`: the same planted bugs in the lowering.
* `hazardcheck.mjs`: the negative control for the hazard rule.
* `tests/test_scenarios.py` (`ts-async-*`): the example in the pull request flow.

## Not done

* **No bridge theorem** from the view to Core's reading of async code. The existing bridge machinery
  walks a `Result` do-block against Core statements and has no notion of a thrown outcome, so it needs
  a thrown-aware judgement and a rule per statement kind before it can drive an `Eff` view. The two
  test layers above are what stands in for it.
* `Promise.all`, `allSettled`, `race`, `.then`, timers, generators and `for await` fail closed.
* Effects of the `method` and `param` forms are accepted in the policy and stop the translator with a
  message: they need class and function types.
* Narrowing `any` in an effect's signature.
