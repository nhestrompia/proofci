## What to build

A reviewer sees exactly which definitions and properties the run covers, which changes lack coverage, and why unsupported behavior blocks a required guarantee.

## Acceptance criteria

- [ ] A complete Git object diff explains changed code without executing hooks or trusting an API file-list cap. Filenames and repository text remain untrusted data.
- [ ] Required dependencies containing excluded semantics produce unproven with a support reason and block the gate.
- [ ] Unsupported changed code and uncovered supported symbols are listed separately from property counts. Existing obligations are still rechecked for unrelated changes.
- [ ] Reports identify the support-policy version, assumptions, exclusions, and source-level guarantee boundary. Candidate support policy cannot expand the admitted subset.
- [ ] Legitimate trusted proof tooling is distinguished from excluded target-program behavior. This ticket consumes admission facts instead of introducing another parser.
- [ ] The report and contributor guidance never imply whole-repository, binary, deployment, or foreign-language verification. Rust/Aeneas is described only as deferred experimental work.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/5

## Agent ownership

Own diff summaries and public support/coverage diagnostics. The source adapter remains the sole admission authority.

## Specification coverage

Approved ProofCI MVP spec, user stories 10, 11, 19, 21, 43, 44. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:09 -->
