# 20: Retrieve and expire repository-scoped hosted evidence

**What to build:** An authorized maintainer downloads evidence from an operator-dispatched hosted run, replays it locally, and receives an explicit expiration result after the retention period, independently of GitHub webhook scheduling.

**Blocked by:** 03: Enroll a GitHub installation and authorize repository access; 08: Export evidence and reproduce verification in a fresh environment; 11: Complete a real verification run through isolated dispatch.

**Status:** ready-for-agent

**Published issue:** https://github.com/nhestrompia/proofci/issues/20

- [ ] Completed runs store immutable evidence references and digests consistent with their authoritative reports using the shared bundle format.
- [ ] Every upload and download enforces installation, repository, run, and actor scope. Cross-repository identifiers disclose neither existence nor contents.
- [ ] A downloaded bundle replays successfully in a fresh environment without model or platform calls. A forged or altered bundle cannot reproduce the historical result.
- [ ] Artifact sizes, names, archive paths, and content types are checked before ingestion. Candidate uploads cannot replace trusted configuration or security diagnostics.
- [ ] A configurable 30-day default expires promised hosted artifacts. Evidence links explain expiration without rewriting historical property outcomes.
- [ ] A retention/access demonstration covers revoked access, cross-repository requests, download, replay, and expiration against actual persisted artifacts.

**Agent ownership:** Own hosted artifact storage, scoped delivery, and retention. Reuse local bundle/replay and installation authorization; do not invent another evidence format.

**Spec coverage:** user stories 14, 20, 21, 31, 35, 37, 40.
