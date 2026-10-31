<img src="assets/icon.svg" width="64" height="64" alt="">

# proofci

ProofCI aims to preserve approved correctness contracts across code changes through AI-assisted proof construction and Lean 4 validation.

The project is in the research and specification stage. No verifier is implemented yet.

- [Feasibility, architecture, and CI integration](docs/research/ci-and-architecture.md)
- [Verification trust model and language support](docs/research/verification-feasibility.md)
- [MVP implementation spec](docs/specs/proofci-mvp.md)

## GitHub enrollment

The Node.js 24 control service stores selected installation and repository IDs in PostgreSQL. The repository-authorization interface checks the stored selection and live App access. The scheduler is a separate, not yet implemented component and must call this interface before dispatch. Maintainers select a repository after signing in; enrollment, removal, and policy inspection recheck their current repository authority. GitHub App and user tokens remain in the control process. Sessions are held in memory and expire on restart.

Register a GitHub App with repository permissions for contents read, pull requests read, checks write, and metadata read. The service rejects contents or pull-request write access. Administration read is optional and is intended only for policy inspection. Install it on the selected repository. Configure an OAuth callback at `https://YOUR-ORIGIN/oauth/callback`. A pilot App was installed on `nhestrompia/proofci` and tested for repository-scoped token issuance, OAuth maintainer enrollment, rejection of an unselected public repository, and denial during an actual suspension followed by successful restoration.

Set `DATABASE_URL`, `GITHUB_APP_ID`, `GITHUB_CLIENT_ID`, `GITHUB_CLIENT_SECRET`, `GITHUB_PRIVATE_KEY_FILE`, and `PROOFCI_ORIGIN`. The origin must use HTTPS, except `http://127.0.0.1:3000` may be used for a local pilot. Run `npm ci`, then `npm start`. The service listens on localhost port 3000, or `PORT`. Remote use requires an HTTPS reverse proxy with request rate limits. Keep the private key file and environment secrets accessible only to the control service.

Run `npm test` and `npm run typecheck`. Set `PROOFCI_TEST_DATABASE_URL` to an isolated PostgreSQL database to run the persistence test. The test creates a `proofci_repository_selections` table and writes test IDs. Set `PROOFCI_TEST_SERVICE_URL` to a separately running test service to run the HTTP boundary test. To run the live GitHub test, set `PROOFCI_TEST_GITHUB_KEY_FILE`, `PROOFCI_TEST_GITHUB_APP_ID`, `PROOFCI_TEST_GITHUB_INSTALLATION_ID`, `PROOFCI_TEST_GITHUB_REPOSITORY_ID`, and `PROOFCI_TEST_GITHUB_UNSELECTED_REPOSITORY_ID`.

Enrollment does not activate contracts or protect merges. Policy inspection checks available default-branch protection and active rules. Missing permissions and unsupported rulesets leave the required-check configuration unconfirmed. A confirmed configuration means GitHub reports the expected App check, strict freshness, and administrator enforcement; it does not establish that checks are published or that any contract is active. Live repository removal, uninstall, and merge-enforcement tests have not yet been completed. Access checks fail closed while a repository is unavailable. An unambiguous revocation observed during an access check clears that enrollment; a removal and restoration between checks cannot be detected until installation events are integrated. Configure a required check restricted to the expected App and require fresh merge results or a merge queue. Administration read may be needed to inspect branch protection.
