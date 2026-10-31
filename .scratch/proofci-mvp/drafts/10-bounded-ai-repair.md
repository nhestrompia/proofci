# 10: Repair proofs within consent and spending limits

**What to build:** An unresolved property can receive an optional proof-body repair through a credential-holding broker, with independent acceptance and visible total usage.

**Blocked by:** 05: Verify every approved obligation through a portable CLI.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/10

- [ ] A real Lean fixture with a correct implementation and obsolete proof becomes verified only after a valid proposed repair passes the existing independent validator.
- [ ] Committed proofs and deterministic tactics run first. Model-disabled and deterministic-success runs make zero model requests.
- [ ] Enforce five attempts, 120 seconds per obligation, 15 minutes per run, and configured context, token, and monetary ceilings. Exhaustion or provider failure leaves unresolved properties unproven.
- [ ] Private-source transmission defaults to disabled. Repository-scoped consent and request authorization are checked before source leaves the deployment.
- [ ] Candidate output and repository instructions cannot change statements, bindings, assumptions, required status, budgets, dependencies, or checker commands. Agents can edit only their proof workspace. Broker requests for arbitrary network access, publishing, unauthorized repository context, or workspace escape are denied. Provider keys stay outside proof execution.
- [ ] The report includes usage for successful and failed attempts and retains generated proof artifacts or patch suggestions. No automatic commits or comments occur.
- [ ] Persist or expose stable request identities and accounting transitions for later recovery integration. Do not claim exactly-once charging from an in-memory retry loop.

**Agent ownership:** Own proof assistance, broker operations, consent, budgets, and request-accounting interfaces. Keep the validator and public report schema with their existing owners.

**Spec coverage:** user stories 12, 13, 14, 17, 25, 33, 34, 36.
