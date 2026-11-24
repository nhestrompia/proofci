# Reading the report

The report is the deliverable a human reads — your guarantees, their doc-comment
claims, and how far each function's translation is trusted.

## Statuses

- **verified** (guarantee): the Lean kernel (and nanoda) accepted a proof of the
  exact protected statement about the code as translated. Covers only the
  listed guarantees.
- **proved** (function): the auto-generated *bridge* theorem checked — the
  Lean view means what the code means under ProofCI's model of JavaScript.
- **tested, not proved** (function): the bridge could not be generated or
  timed out (120 s cap), and the Node comparison found no difference. The
  guarantee still holds **of the Lean view**; that the view matches JavaScript
  is differentially tested, not proved. `require_bridge: true` in
  `proofci.yaml` makes this block.
- **failed**: Node and the view disagreed — blocked, and a translator/runtime
  bug; report it, never prove around it.
- **blocked** (verdict): a guarantee failed, a contract is stale, a downgrade
  wasn't accepted, or a required bridge didn't check.

## What to tell the human

- "Verified" is verified *of the Lean view*. The "Does the Lean view match
  JavaScript?" section says how far that translation is trusted per function.
- `compared with Node: N results agree, M inputs left the safe-integer model` —
  M inputs exceeded the model (e.g. past 2^53); the comparison can't speak to
  them.
- Vacuity warnings ("none of the 60 generated inputs satisfies the
  hypotheses") mean the fuzzer couldn't exercise the guarantee's hypotheses —
  not that the guarantee is weak; read it as a review signal.
- `contract warnings` flag statement shapes that may not constrain the code —
  including the `∃`-restatement the checker itself forces for relational
  properties. The doc-comment claim beside each theorem is what keeps it
  honest; a statement can satisfy the checker vacuously otherwise.
- `downgrades`: a function proved on the base that is anything less now blocks
  (fail closed). With `--base HEAD` on a fresh adoption the base can't be
  checked and the "was proved" wording is confusing — that's the temporary
  workaround's artefact, not a real downgrade.

## Where the report can mislead

- Hypotheses are rendered verbatim (`hlen : xs.length ≤ 9007199254740991`) —
  they read cryptic; the doc comment should translate them to English ("list
  shorter than JS's safe-integer max").
- `the bridge theorem did not check: STUCK` gives no reason and no next step —
  it names the tactics' limits OR a wrong view, and can't say which.
