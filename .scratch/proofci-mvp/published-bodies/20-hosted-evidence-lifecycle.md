## What to build

An authorized maintainer downloads evidence from an operator-dispatched hosted run, replays it locally, and receives an explicit expiration result after the retention period, independently of GitHub webhook scheduling.

## Acceptance criteria

- [ ] Completed runs store immutable evidence references and digests consistent with their authoritative reports using the shared bundle format.
- [ ] Every upload and download enforces installation, repository, run, and actor scope. Cross-repository identifiers disclose neither existence nor contents.
- [ ] A downloaded bundle replays successfully in a fresh environment without model or platform calls. A forged or altered bundle cannot reproduce the historical result.
- [ ] Artifact sizes, names, archive paths, and content types are checked before ingestion. Candidate uploads cannot replace trusted configuration or security diagnostics.
- [ ] A configurable 30-day default expires promised hosted artifacts. Evidence links explain expiration without rewriting historical property outcomes.
- [ ] A retention/access demonstration covers revoked access, cross-repository requests, download, replay, and expiration against actual persisted artifacts.

## Blocked by

- https://github.com/nhestrompia/proofci/issues/3
- https://github.com/nhestrompia/proofci/issues/8
- https://github.com/nhestrompia/proofci/issues/11

## Agent ownership

Own hosted artifact storage, scoped delivery, and retention. Reuse local bundle/replay and installation authorization; do not invent another evidence format.

## Specification coverage

Approved ProofCI MVP spec, user stories 14, 20, 21, 31, 35, 37, 40. Test through the repository-snapshot and approved-contract input, authoritative report, public exit status, and applicable CI result, with real Lean validation where relevant.

<!-- proofci-mvp-ticket:20 -->
