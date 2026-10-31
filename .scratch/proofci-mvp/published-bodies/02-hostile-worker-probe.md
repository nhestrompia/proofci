## What to build

An operator launches an adversarial probe in an ephemeral Linux VM and receives a report of denied access, resource limits, and complete cleanup before real repository verification is connected.

## Acceptance criteria

- [ ] A documented launcher boots an actual disposable VM or microVM and returns the probe result without requiring a verifier, GitHub installation, or model provider.
- [ ] Probe attempts to read host home, credential sentinels, another workspace, a container-management socket, or arbitrary network endpoints are denied. No real credentials are used as probe data.
- [ ] CPU, memory, disk, process-count, log-size, and time-limit probes terminate predictably and identify the exceeded limit.
- [ ] Cancellation terminates the entire guest job and its descendants. A subsequent job cannot read the previous job's temporary state.
- [ ] The report records the tested Linux host and isolation configuration. Unsupported virtualization or sandbox combinations fail with an explicit prerequisite error.
- [ ] The launcher exposes a narrow job input and artifact handoff interface. It does not label probe success as formal verification or accept hosted public PR jobs yet.

## Blocked by

None (can start immediately).

## Agent ownership

Own the VM launcher, guest resource limits, cancellation, and access probes. The later hosted-run ticket connects the real verifier.

## Specification coverage

Approved ProofCI MVP spec, user stories 31, 33, 35, 37. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:02 -->
