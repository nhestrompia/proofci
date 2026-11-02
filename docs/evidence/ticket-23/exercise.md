# Ticket 23 operational exercise

Duration: 22.2 minutes. Steps passed: 50. Failed: 0.

## Environment

- host: `Darwin 25.6.0 arm64`
- docker: `linux/arm64 29.6.2`
- kvm: `false`
- commit: `ee08381d72be66af5aaac0dd7c1d69c3f8dd0982`
- dirty: `false`
- controlImage: `sha256:d75e81dd961854ca69c3ffeb42b22ecbb28824f02d20c60a7ccd34dacff2d7f3`
- verifierImage: `sha256:166f221ee92c8e38ca0a211fe10d057d919216216c21e661b48cf73859a6acce`

## Steps

| Phase | Step | Result |
| --- | --- | --- |
| deploy | reviewed baselines activated through the pinned verifier | pass |
| deploy | preflight reports no failures | pass |
| deploy | fresh deployment records its schema | pass |
| enroll | maintainer signs in through OAuth | pass |
| enroll | ledger repository enrolled | pass |
| enroll | registry repository enrolled | pass |
| pull-request | signed pull_request webhook accepted | pass |
| pull-request | no credential reaches the dispatcher or the verifier VM | pass |
| pull-request | real Lean run finished | pass |
| pull-request | run binds the GitHub test merge commit | pass |
| pull-request | check published on the merge commit | pass |
| pull-request | maintainer downloads hosted evidence | pass |
| pull-request | evidence is not reachable through another repository or without a session | pass |
| pull-request | downloaded bundle replays in a fresh verifier VM | pass |
| crash | PR 2 webhook accepted | pass |
| crash | completed run with a failing publication stays pending | pass |
| crash | PR 3 webhook accepted | pass |
| crash | model attempt recorded as sending before the crash | pass |
| crash | control process killed during verification | pass |
| backup | full backup captures baselines, approvals, runs, evidence, reservations and pending publications | pass |
| backup | scoped backup excludes the other repository | pass |
| backup | backup verifies offline | pass |
| backup | tampered backup is rejected | pass |
| backup | backup refuses to run while the service is running | pass |
| recovery | publication retried from the database without repeating proof construction | pass |
| recovery | in-flight model attempt became uncertain and was not resent | pass |
| recovery | unsent reservation was preserved, not sent | pass |
| recovery | interrupted verification was reclaimed by a new generation | pass |
| recovery | diagnostics report the uncertain attempt with reconciliation instructions | pass |
| recovery | PR 3 close webhook accepted | pass |
| recovery | cancelled run released its reservation without contacting the provider | pass |
| recovery | operator reconciled the uncertain attempt from provider records | pass |
| rotation | webhook secret rotates without a restart | pass |
| rotation | PR 4 webhook accepted with the new secret | pass |
| rotation | old App key and client secret stop working | pass |
| rotation | OAuth works after rotating the client secret | pass |
| rotation | App publishing resumes with the new key | pass |
| diagnostics | known defect: runs cancelled and re-admitted with identical inputs (publication freshness race) | pass |
| diagnostics | diagnostics distinguish proof failure, infrastructure failure and superseded runs | pass |
| restore | restored database matches the backup row for row | pass |
| restore | restored baseline and authority stores match the backup | pass |
| restore | restore refuses a non-empty database | pass |
| restore | restored evidence downloads with the original digest | pass |
| restore | restored evidence stays repository scoped | pass |
| restore | restored pending publication completes without re-running proof construction | pass |
| restore | restored in-flight attempt is uncertain, never resent | pass |
| upgrade | preflight announces the pending upgrade | pass |
| upgrade | previous-release database upgrades in place and keeps its reports | pass |
| upgrade | a database from a newer release is refused with instructions | pass |
| upgrade | an unsupported report format is refused with instructions | pass |
