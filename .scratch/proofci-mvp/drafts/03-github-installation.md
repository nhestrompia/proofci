# 03: Enroll a GitHub installation and authorize repository access

**What to build:** A maintainer installs ProofCI, selects a repository, and sees its authorized access and enforcement configuration without exposing installation credentials.

**Blocked by:** None (can start immediately).

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/3

- [ ] A real test installation uses contents read, pull requests read, checks write, and metadata access. Any optional administration-read permission has an explicit policy-inspection purpose.
- [ ] Installation and selected repository IDs control authorization. An arbitrary repository name, removed repository, suspended installation, or uninstall cannot authorize new work.
- [ ] Repository-restricted installation credentials renew safely and remain in the control service. Responses and logs contain no private keys or access tokens.
- [ ] A trusted maintainer operation verifies the actor's current repository authority rather than accepting a caller-supplied actor name. This identity check is reusable by later rerun, fork, and migration operations.
- [ ] Onboarding reports enforcement as confirmed, misconfigured, or unconfirmed using actual available evidence. It explains the expected-App required check and fresh-merge policy.
- [ ] Enrollment alone never claims that contracts are activated or that verification protects merges. Missing external setup is reported as a concrete prerequisite.

**Agent ownership:** Own installation records, GitHub authentication, repository authorization, and trusted maintainer identity. Do not own baseline activation or event scheduling.

**Spec coverage:** user stories 1, 22, 24, 37.
