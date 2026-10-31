# Independent evidence validation

`evidence.py` is the ticket 04 validation boundary. It accepts an unpacked
proof bundle plus the authoritative candidate and contract paths. The bundle
cannot provide a challenge, checker command, toolchain, policy, or acceptance
decision.

## Bundle format

The directory must contain exactly these regular files:

```text
manifest.json
solution.lean
challenge.ndjson
solution.ndjson
```

The manifest contains version `1`, SHA-256 digests for the authoritative
candidate and contract, the submitted solution and both exports, and the
literal claim `verified`. Candidate and contract digests are checked against
the caller-supplied bytes. The candidate is admitted through the ticket 01
restricted parser before any tool is invoked.

`challenge.ndjson` may contain the challenge-only `sorryAx` placeholder.
`solution.ndjson` may not. Both exports must contain the bound target and
`contract`; the identity theorem is checked by the fixed Comparator challenge
configuration even though it is not in the contract's exported dependency
closure. All other declarations come from the pinned dependency policy. The only explicitly permitted foundational axioms
are:

```text
propext
Quot.sound
Classical.choice
```

Direct or transitive `sorryAx`, custom axioms, native-evaluation escapes,
unvalidated declarations, forbidden proof commands, malformed exports, and
wrong-candidate digests are invalid evidence.

## Validation boundary

The validator reconstructs `CandidateCheck`, `Challenge`, and `Solution` from
the authoritative candidate, contract, and submitted proof body. It writes a
fixed comparator configuration and ignores any bundle configuration. It then
performs construction in one temporary workspace and fresh replay in a second
temporary workspace. Each fixed replay/checker script gets a fresh ephemeral
`.lake` mount; the scripts and final source/policy inputs are read-only in the
validation sandbox. Both workspaces run through the pinned read-only Lean
distribution and an offline bubblewrap sandbox.

The final decision requires matching fresh challenge and solution exports,
successful kernel replay, and agreement between the Lean kernel and Nanoda
checker. Missing or mismatched validation is never converted into acceptance.

Normalized reasons are `invalid_evidence`, `build_failure`,
`checker_disagreement`, `validation_unavailable`, and `unproven`. Only the
combined independent acceptance path returns `verified`.

On this macOS development host the pinned Linux arm64 validator is expected to
return `validation_unavailable`; the real positive-path replay is run in the
pinned Linux environment from ticket 01.
