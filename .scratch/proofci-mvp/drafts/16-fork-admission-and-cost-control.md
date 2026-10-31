# 16: Admit fork verification with explicit cost authorization

**What to build:** External contributors receive deterministic verification without secrets, while costly proof assistance requires maintainer approval and repository quota.

**Blocked by:** 10: Repair proofs within consent and spending limits; 12: Turn signed GitHub events into durable verification runs.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/16

- [ ] Resolve fork source and destination identities explicitly. Returned check-to-PR associations alone cannot authorize work.
- [ ] A real fork candidate completes deterministic isolated verification without provider, installation, signing, or other repository credentials entering candidate execution.
- [ ] Costly assistance is denied or deferred without an authorized maintainer decision, source-transmission consent, and available repository quota.
- [ ] Approval binds exact inputs and loses validity after a relevant push, baseline change, revocation, or changed resource policy. Candidate code and agent output cannot approve themselves.
- [ ] Closing access or cancelling a run prevents subsequent dispatch and broker requests. Existing in-flight calls follow an explicit documented revocation boundary.
- [ ] A malicious fork attempts credential, host, network, and cross-repository cache access and receives denied access with trusted diagnostics. Keep paid hosted requests disabled until durable request recovery passes; final release acceptance must demonstrate an authorized fork repair after that gate opens.

**Agent ownership:** Own fork admission and approval policy. Reuse installation authorization, isolated dispatch, and broker accounting rather than adding alternate execution paths.

**Spec coverage:** user stories 24, 25, 28, 31, 33, 34, 35.
