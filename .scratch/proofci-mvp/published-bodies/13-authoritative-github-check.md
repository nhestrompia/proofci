## What to build

A real pull request receives one stable ProofCI check on GitHub's actual test-merge commit, with validated outcomes, evidence, and recoverable publication.

## Acceptance criteria

- [ ] Resolve the actual GitHub test-merge commit, head, base, and baseline. A local commit with the same tree is not substituted. Missing, conflicting, or unresolved candidates produce a clear blocking result.
- [ ] The check reports the exact candidate, approved scope, assumptions, exclusions, and property outcomes. Provide a basic authenticated run-detail endpoint with the full report, immutable evidence digests, and retrieval of the persisted evidence bundle after worker cleanup. The later hosted-evidence ticket extends this boundary with object storage and retention.
- [ ] Only the authoritative validated report can yield success. Required unresolved properties, invalid policy, execution failures, cancellations, and timeouts cannot satisfy the enforcing gate.
- [ ] A publication outbox retries transient API errors without rerunning successful proof work or creating duplicate logical checks. Record publication latency through the shared timing contract. Installation publishing credentials never enter workers.
- [ ] More than 50 annotations publish in valid batches and preserve the aggregate outcome. Truncated summaries retain access to the full report.
- [ ] Before successful publication, recheck head, base, baseline, and run generation. A live pilot demonstrates correct check association and expected-App configuration.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/8
- https://github.com/nhestrompia/proofci/issues/12

## Agent ownership

Own test-merge resolution, Checks API publication, annotations, and the publication outbox. Use durable run generations and evidence interfaces instead of duplicating them.

## Specification coverage

Approved ProofCI MVP spec, user stories 20, 22, 23, 26, 30, 40. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:13 -->
