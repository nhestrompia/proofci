# Evaluation

`evaluate.py` runs a frozen corpus of reviewed properties and change scenarios
through the public verifier commands and reports soundness, outcomes, latency,
usage and cost. It measures the verifier; it does not change acceptance rules.

## Corpus

[`corpus/`](corpus/) holds three small Lean packages with ten reviewed
properties each:

| Package | Domain | Bound target |
| --- | --- | --- |
| `arithmetic` | arithmetic | fee for `x` items, `x * 3 + 2` |
| `collections` | collections | flattened grid length, `x * (x + 1) + 2` |
| `state` | state transitions | successor state, `(x + 1) * 2 + 3` |

The verifier admits a single `def target (x : Nat) : Nat` over `x`, literals,
`+`, `*` and parentheses, so collections and state transitions are modelled by
a size or successor function. Each package also contains a real Lean module
(`Ledger.lean`, `Grid.lean`, `Machine.lean`) that the verifier does not admit;
scenarios use it to measure unsupported-input reporting.
[`corpus/REVIEW.md`](corpus/REVIEW.md) lists every property, its meaning and
its truth for each candidate. [`oracle.py`](oracle.py) rechecks those labels by
polynomial normalization (or bounded enumeration for preconditions) without
using the verifier's parser, and labels results as false acceptances.

[`corpus/scenarios.json`](corpus/scenarios.json) defines 33 scenarios. Each
scenario builds a Git repository with a base commit (the base target with
valid proofs) and a head commit, a protected baseline outside the checkout,
and a version 1 envelope:

| Category | What changes in the head commit |
| --- | --- |
| `correct_change` | equivalent target, regenerated proofs |
| `obsolete_proof` | equivalent target, proofs written for the old target |
| `intentional_violation` | defective target; new proofs for true properties, refutations for some false ones, obsolete proofs for the rest |
| `contract_mutation` | proof of a weaker contract or a narrower precondition |
| `source_substitution` | proofs about a correct shadow file; target replaced by unsupported Lean |
| `forbidden_axiom` | custom axiom, `sorry`, axiom used through a lemma |
| `forged_evidence` | trivial statement, shadow namespace, rebound digest, flipped claim, edited solution, moved witness, replayed refutation |
| `invalid_submission` | extra evidence file, malformed manifest, uncommitted content |
| `unsupported_input` | adds unsupported Lean and Python beside a correct change |
| `timeout` | correct change under a 20 second run budget |
| `persistence` | reviewed baseline store: weakened, deleted or rebound manifest, and an unapproved activation |

Every expectation in `scenarios.json` names the allowed public exit codes and
per-obligation decisions. Expectations are checked exactly for deterministic
runs. Assisted runs may repair more obligations, so only soundness is enforced
for them.

### Proofs inside the validator policy

The validator accepts only exports whose declarations are in
`experiments/source-binding/core-dependencies.json`. Proofs produced by `simp`,
`omega`, `decide` or the `cases` tactic are rejected as `invalid_evidence`.
The reviewed proofs therefore use `rfl` for properties definitionally equal to
the target, `Eq.ndrec` for point preconditions, nested `Nat.casesOn` terms for
bounded preconditions, and `Nat.lt_irrefl` with `Nat.le_of_ble_eq_true` for
refutations at a concrete witness. Of the verifier's fixed repair tactics
(`rfl`, `simp [target] <;> omega`), only `rfl` can produce admissible evidence.

`build_evidence.py` constructs every bundle inside the pinned image, playing
the pull request author. Positive proofs and refutations are kept only when the
validator accepts them. Forgeries bypass the construction-time syntax filter so
that they carry real Lean exports. Bundles are cached by the SHA-256 of the job,
image ID and builder (`~/.cache/proofci-evaluation` by default). Construction
is preparation and is not part of measured latency.

### Freezing

`corpus/lock.json` records the SHA-256 of every corpus file. `run` refuses to
start when the corpus differs from its lock. Change a property, scenario or
expectation only before measuring assistance, then refreeze:

```sh
python3 evaluation/evaluate.py check
python3 evaluation/evaluate.py freeze --reviewer NAME --replace
```

A new lock makes earlier results incomparable with later ones.

## Run

Requirements match the [portable verifier](../portable/README.md): an ARM64
Docker host with the pinned `proofci-validator-local` image loaded.

```sh
python3 evaluation/evaluate.py run --output evaluation-output --mode deterministic --repetitions 3
```

The first repetition of each scenario is cold (the first verifier container for
that scenario in this invocation). Later repetitions are warm. A complete run
needs every scenario and at least two repetitions. `--scenario ID` selects a
subset; the report then says the corpus was not complete and makes no release
assessment from it.

Deterministic runs call `portable/assist.py` without a model configuration.
That path validates submitted evidence and then tries the verifier's fixed
tactics. Assisted runs call the same command with `--model-config`, so the
model is the only difference. To measure assistance, set
`PROOFCI_OPENAI_API_KEY` in the control process and pass a profile:

```json
{"model": "gpt-4.1-mini", "authorized": true, "private": true, "private_source_consent": true,
 "limits": {"context_bytes": 32768, "input_tokens": 100000, "output_tokens": 5000, "cost_micros": 1000000,
            "input_micros_per_million": 400000, "output_micros_per_million": 1600000, "max_output_per_call": 1000}}
```

```sh
python3 evaluation/evaluate.py run --output evaluation-output --mode both --model-profile profile.json
```

The harness adds the repository, run, head and baseline identities for each
run. The token rates must be upper bounds for the selected model; they decide
the reported cost. Without a profile or key, the assisted section is reported as
`not_measured` and paid assistance is not eligible to become a default.

Exit status: 0 when no false acceptance occurred and every deterministic
expectation was met; 1 when the release is blocked; 2 when the evaluation
could not run.

## Artifacts

`evaluation.json` is the machine-readable result; `evaluation.md` is generated
from it (`evaluate.py render` regenerates it). Both contain:

- the release gate: false acceptances (also counted separately for soundness
  and persistence scenarios), unmet expectations, corpus completeness and the
  latency assessment. Every false acceptance is listed, whatever else the run
  selected.
- deterministic and assisted outcomes reported separately: decisions, unproven
  reasons, unsupported inputs, invalid submissions, timeouts, execution errors,
  repairs and failed repair attempts, model calls, tokens, settled cost, and
  the upper bound of cost that remains unknown.
- latency of the public command: cold and warm median, p95, minimum and maximum,
  per category and per obligation, assessed against a warm median below 60 s
  and p95 below 300 s under the unchanged resource policy.
- stability: deterministic outcomes that changed between repetitions and,
  separately, model nondeterminism.
- assistance utility: obligations verified only with assistance, regressions,
  and cost per additional verified obligation. Paid assistance is eligible to
  become a default only with measured gains, no regressions, no false
  acceptance, known cost and a complete corpus. Eligibility only allows a
  maintainer to decide; it never enables paid assistance.
- environment: host, CPUs, memory, Docker, verifier commit, image ID, toolchain,
  dependency, policy and bubblewrap digests, Lean commit, evidence cache state
  and the cold/warm definition.

A false acceptance is a `verified` result for a property that does not hold on
the head target, a passing public exit where the scenario forbids one or a
required property is false, or a change to the active reviewed baseline.

## Tests

```sh
python3 -m unittest discover -s evaluation -p 'test_*.py'
PROOFCI_TEST_PACKAGED=1 python3 evaluation/test_evaluate_linux.py
```

The Linux test runs a CLI subset and an assisted scenario with a scripted
provider inside the real broker and verifier; it makes no paid model request.

## Limits

- The portable launcher does not pass `--allow-unconfined-apparmor` through
  `assist.py` or `baselines.py`, so this evaluation does not run on GitHub's
  Ubuntu runners. Run it on a host where the verifier container runs without
  that option, or extend the launcher in a separate change.
- CI publication is not exercised; scenarios use the public exit status and
  authoritative report.
- The corpus covers only the admitted single-target language; results do not
  extend to other Lean or to deployed systems.
