# Security model

ProofCI runs code from people it does not trust: the Rust in a pull request,
its dependencies and their build scripts, and the Lean proofs. This document
states what ProofCI defends against, how, what it trusts, and what remains.

## What an attacker controls

A pull request author, human or agent, controls everything in the pull
request: Rust sources, `Cargo.toml`/`Cargo.lock` (so which crates.io
dependencies, with their build scripts and proc macros), the proofs
(`Proofs.lean`, `Proofs/**`), and any file in the repository, including
`proofci.yaml`, the contract and workflow files.

They want one of:

1. **A false "verified":** a required guarantee reported as verified when it
   does not hold for their code.
2. **A weaker policy:** a guarantee removed, made optional or restated.
3. **Secrets or tokens.**
4. **Control of the runner**, for example to forge the check's result.

## How each is prevented

| Goal | Defence |
|---|---|
| False "verified" | The Lean model is regenerated from the PR's Rust by the pinned Charon/Aeneas; committed translations are ignored. Statements come from the protected contract. `lake comparator` checks each theorem's statement and every constant it uses against the contract, allows only `propext`, `Quot.sound` and `Classical.choice`, and replays the proofs in **both** the Lean kernel and nanoda. Proof code (`#eval`, `run_cmd`, tactics) only ever runs in disposable copies of the workspace; each comparator run starts from a workspace where only the extracted model and the contract were built. Build scripts and proc macros run with every source file read-only. |
| Weaker policy | `proofci.yaml` and the contract are read from the **base** commit. Any difference is reported and blocks, unless someone allowed by the base policy (`policy.approvers`, or by default an owner/member/collaborator who is not the author) approved that exact commit. `approvers: []` makes the policy unchangeable in a PR. |
| Secrets | The workflow runs under `pull_request_target`, so it comes from the base branch. Both commits are checked out as data with no persisted credentials. The job has only a read-only token, used outside the container to read reviews. No secret is passed to any container. |
| Runner control | Below. |

### Isolation layers

1. **GitHub-hosted runner:** a fresh VM per job, discarded afterwards.
2. **Container**, per run:
   - `--network none` for the check (the separate `fetch` step has network but runs no package code, see below)
   - `--cap-drop ALL`, `--security-opt no-new-privileges`
   - read-only root filesystem with a `/tmp` tmpfs
   - CPU, memory and process limits
   - inputs mounted read-only
   - seccomp: Docker's default profile plus only `clone`, `unshare`, `mount`, `umount2`, `pivot_root` and `setns`, which bubblewrap needs ([`action/seccomp.json`](action/seccomp.json))
3. **bubblewrap**, per tool invocation (Cargo/Charon, Aeneas, Lake):
   - new user, mount, PID, network, IPC and UTS namespaces
   - read-only root, fresh `/tmp`
   - write access to one output directory only
   - killed with its parent
4. **`lake comparator`'s own sandbox** around the build and export of the proofs.

`proofci fetch` is the only step with network access. It runs `cargo vendor`,
which resolves, downloads and checks `Cargo.lock` checksums but does not
compile or run anything. Dependency code first runs in the offline check,
inside layers 2 and 3.

## What is trusted

A "verified" result is only as good as these components:

| Component | Role |
|---|---|
| Lean 4 kernel and nanoda | Both independently accept every proof |
| `lake comparator` (Lean's own) | Statement and axiom comparison |
| `rustc` frontend, Charon, Aeneas | That the Lean model faithfully describes the Rust code. A bug here can make a proof about the model not hold for the program. |
| ProofCI's standard-library models ([`proofci/models.py`](proofci/models.py)) | Rust behaviour of library functions Aeneas leaves undefined. Each model is checked against `rustc`: on boundary values for every width, and on every possible input for the 8- and 16-bit instances (a model's Lean code is the same template for every width) ([`tests/test_models.py`](tests/test_models.py)). They are tested, not proved. The models a guarantee depends on are listed next to its result. |
| ProofCI itself (Python) | Orchestration, policy comparison, the contract audit |
| The toolchain image | Every download in it is pinned by version and SHA-256, and it is built by this repository's CI. CI signs build provenance (a Sigstore attestation) binding the image digest to this repository, the CI workflow, `main` and the exact commit. The action resolves the digest for the commit it is pinned to, verifies that attestation, and runs the image by digest, so a moved tag cannot substitute another image. Check an image yourself with `gh attestation verify oci://ghcr.io/nhestrompia/proofci-toolchain@<digest> --repo nhestrompia/proofci`. An explicit `image:` input is used as given, without this check. |
| GitHub | `pull_request_target` semantics, review records, branch protection |
| Linux kernel, Docker, bubblewrap | Isolation |

## What "verified" means

| Level | Meaning | Who establishes it |
|---|---|---|
| Kernel-valid | Lean's kernel and nanoda accepted a proof of the protected statement, using only the standard axioms | ProofCI |
| Implementation-linked | The statement is about the function translated from the PR's Rust, and that function rests on no unmodelled code | ProofCI (contract audit, axiom audit), within the trust above |
| Meaningful | The statement says what the business actually needs | **People** reviewing the contract. ProofCI warns about statements of a shape that constrains nothing, but cannot judge intent. |

## Known residual risks

- **Kernel attack surface:** the container must allow user namespaces and mounts for bubblewrap, and runs without Docker's AppArmor profile and with `/proc` unmasked. A kernel exploit reachable from an unprivileged user namespace could escape to the runner VM. There it could read the job's read-only token, or alter the step's output and so forge the check result. Use ProofCI only on **ephemeral GitHub-hosted runners**, not on persistent self-hosted runners that also run trusted jobs.
- **Translation bugs** in Charon/Aeneas or a model would be invisible to the proofs. Report them upstream and here.
- **Weak contracts** pass if they are weak. Review contracts like code.
- **Collaborator approval:** without `policy.approvers`, any collaborator other than the author can approve a policy change. Name approvers, or use `approvers: []`, for strict repositories.
- **Denial of service:** a pull request can make the check slow or fail (timeouts, memory limits). That blocks the PR; it never makes it pass.

## TypeScript

TypeScript support is experimental and isn't released yet. The translator is
ProofCI's own code, so it is part of what you trust, without the outside review
Charon and Aeneas have. Each check reduces that risk by running the translated
functions in Node on generated inputs and comparing them with the Lean model.
Any disagreement blocks the guarantees.

The translator rejects what it can't model exactly, and only reads and
type-checks the code. It ignores the project's `tsconfig.json`, and it rejects
files with `@ts-` comments, compiled JavaScript beside the source, module-level
code other than declarations, and declaration files standing in for source.

### Installing packages

The type checker needs the declarations of the packages a project imports, so the
dependency step installs them from the project's lockfile. That is the one step with
network access, and the trade-offs are these:

- It runs `npm ci`, `pnpm install --frozen-lockfile` or `yarn install
  --frozen-lockfile` with install scripts off, in the same bubblewrap sandbox as
  every other step, inside the container's own network, on a private copy of the
  repository. The package managers are pinned in the toolchain image.
- The copy leaves out `.npmrc`, `.yarnrc*`, `.yarn/`, `.pnpmfile.cjs` and `.pnp.*`.
  They are pull request content, and some run code (`.pnpmfile.cjs`, Yarn's
  `yarnPath`), so no setting in the project reaches the installer. A consequence is
  that private registries and custom install settings aren't supported.
- Packages must come from `registry.npmjs.org` (or `registry.yarnpkg.com`) over
  HTTPS, so a pull request can't make the installer fetch from a host of its
  choosing, such as an internal address on the runner's network. The lockfile's
  integrity hashes decide the contents. npm packages from elsewhere are left out and
  named in the report; pnpm and Yarn lockfiles that contain one are refused. Yarn 2
  and later is refused, because it runs project code while installing.
- Network access isn't narrowed to those hosts at the network level; that would need
  an egress proxy. A package manager that follows a redirect could reach another host,
  but whatever it fetches is only ever read as package files, never run.
- A pull request can change the lockfile, and so which package versions the
  declarations come from. That is a change to the code the guarantees are judged
  against, like any other, and it goes through the same proof and comparison with Node.
  The installed packages are mounted read-only into a copy of the code for the
  translator and for the comparison with Node. The comparison runs functions in Node,
  and importing a module can load installed packages, which run in the sandbox without
  network, as the project's own code does.
- The install needs the network, which a malicious package can't use: its scripts
  never run, and the check that reads it is offline.

A TypeScript guarantee also assumes:

- Callers pass values of the declared types, without getters or proxies.
- Code elsewhere in the program doesn't replace built-ins such as `Math.floor`.
- The program runs the TypeScript source as written, so bundler replacements and
  macros are outside the guarantee.
- Each outside call listed under `assumes` has the listed type and gives the same
  result for the same arguments. ProofCI checks none of that code, and doesn't
  compare functions that rely on it with Node. Listing a call that isn't a function
  of its arguments makes a proof about it meaningless.
- A guarantee about `async` code holds for every answer the calls listed under `effects` could give,
  and says nothing about the code behind them. A rejection is modelled as an `Error` with a `name` and a
  `message`, so `e instanceof Error` is true of everything caught. Where the policy narrows an `any` in a
  call's signature (`narrowed`), the guarantee assumes the call answers with the narrowed type; the report
  lists it. Arguments aren't changed by their caller while a call is pending (the report names the ones a
  guarantee relied on). A module-level table read after an `await` is one nothing in the program writes, and,
  if it is exported, nothing outside the program does either (the report names those too). Objects of a
  class or library type are opaque: the guarantee assumes nothing about what they are, only that a listed
  method call on one is answered like any other outside call.

## Reporting a vulnerability

Please use GitHub's private vulnerability reporting on this repository
("Security" tab → "Report a vulnerability") rather than a public issue.
Especially valuable: any way to get a guarantee reported `verified` that does
not hold, or to bypass the policy check.
