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
- `scope: example` (`checks one fixed input only`) labels a guarantee whose
  statement applies the target only to literal arguments — it pins down that
  one input, not the general case. A warning, not a failure, unless
  `require_general: true` is set; a function whose guarantees are ALL examples
  is called out under its name.
- Function warnings sit next to each target: `nothing in the repository calls
  f; these guarantees don't cover shipped code` means no other source file
  imports the function (a proved parallel copy of shipped code does not count),
  and `f is not exported — Node generates no inputs` means the differential
  comparison had nothing to exercise.
- `the comparison with Node did not run — a ProofCI infrastructure failure,
  not a disagreement: <output tail>` means Node crashed, OOM'd or timed out.
  It still blocks (fail closed), but it is a tooling problem to report, not a
  verdict on the code.
- `the hypothesis-witness check could not run for <theorem>` names the
  theorem(s) the check failed on and carries the trimmed Lean error; other
  theorems are still checked individually.
- `downgrades`: a function proved on the base that is anything less now blocks
  (fail closed). On a first adoption (`first_adoption: true`) there is no base
  contract, so every guarantee counts as new and the run blocks until a
  maintainer — not the PR author — approves it.

## Where the report can mislead

- Hypotheses are rendered verbatim (`hlen : xs.length ≤ 9007199254740991`) —
  they read cryptic; the doc comment should translate them to English ("list
  shorter than JS's safe-integer max").
- `the bridge theorem did not check: STUCK` still means either the tactics'
  limits or a wrong view — but the reason now names the construct the proof
  was working on (e.g. `a \`while\` loop`, with the Core source), the same in
  `report.json`, so the rewrite to try starts there.
