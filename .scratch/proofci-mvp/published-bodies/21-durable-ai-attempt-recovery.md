## What to build

A hosted assisted run survives interruption while preserving its budget, request history, and uncertainty about provider calls whose responses were lost.

## Acceptance criteria

- [ ] Persist reservations, request IDs, usage, completion, and cancellation across service restart. Recovered attempts cannot reset repository or run budgets.
- [ ] Duplicate dispatch of a logical attempt converges on the same durable record. Use provider idempotency only where its actual semantics support safe retries.
- [ ] A crash after a provider accepts a request but before a response is recorded produces reconciliation or an explicit uncertain attempt. It does not automatically resubmit an unsafe duplicate call.
- [ ] Reports account for failed and uncertain attempts without inventing exact usage. Stop or reserve further spending conservatively when the configured ceiling cannot be justified.
- [ ] Cancellation, supersession, consent revocation, and removed access survive restart and block new provider calls. Late results cannot replace a newer run generation.
- [ ] Fault injection covers reservation, send, response persistence, validation, and publication handoff. Hosted paid AI is not enabled until these recovery cases pass.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/10
- https://github.com/nhestrompia/proofci/issues/12

## Agent ownership

Own durable broker accounting and uncertain-call reconciliation. Reuse generic run recovery and the broker interface; do not duplicate GitHub publication state.

## Specification coverage

Approved ProofCI MVP spec, user stories 25, 28, 29, 30, 33, 34, 36. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:21 -->
