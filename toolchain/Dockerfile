# ProofCI verifier toolchain: Rust nightly + Charon + Aeneas + Lean + Mathlib.
# Every download is pinned by version and SHA-256. Build once per release and
# publish by digest; CI jobs pull the image instead of rebuilding it.
# Builds for linux/amd64 and linux/arm64 (TARGETARCH is set by BuildKit).
ARG DEBIAN=debian:trixie-slim@sha256:f6b08b09a05725f9431502d3b5714f5c4576e82c1a84fa1debe0c24a7e0c3ec4

FROM ${DEBIAN} AS base
RUN apt-get update \
 && apt-get install -y --no-install-recommends ca-certificates curl git zstd xz-utils \
      gcc libc6-dev libgmp10 python3 python3-yaml bubblewrap \
 && rm -rf /var/lib/apt/lists/*

# ---------------------------------------------------------------- Lean 4.35.0
FROM base AS lean
ARG TARGETARCH
ARG LEAN_VERSION=4.35.0
ARG LEAN_SHA256_AMD64=7289597a44543246c9227b8cae501767e095ce17f6d448b95fc4a8dc97268f6d
ARG LEAN_SHA256_ARM64=c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028
RUN case "${TARGETARCH}" in \
      amd64) asset=linux sha="${LEAN_SHA256_AMD64}" ;; \
      arm64) asset=linux_aarch64 sha="${LEAN_SHA256_ARM64}" ;; \
      *) echo "unsupported architecture ${TARGETARCH}" >&2; exit 1 ;; \
    esac \
 && curl -fsSL --retry 3 -o /tmp/lean.tar.zst \
      "https://github.com/leanprover/lean4/releases/download/v${LEAN_VERSION}/lean-${LEAN_VERSION}-${asset}.tar.zst" \
 && echo "${sha}  /tmp/lean.tar.zst" | sha256sum -c - \
 && mkdir -p /opt && tar --zstd -xf /tmp/lean.tar.zst -C /opt \
 && mv /opt/lean-${LEAN_VERSION}-${asset} /opt/lean && rm /tmp/lean.tar.zst

# ------------------------------------------------- Rust nightly pinned by Charon
FROM base AS rust
ARG TARGETARCH
ARG RUSTUP_VERSION=1.28.2
ARG RUSTUP_SHA256_AMD64=20a06e644b0d9bd2fbdbfd52d42540bdde820ea7df86e92e533c073da0cdd43c
ARG RUSTUP_SHA256_ARM64=e3853c5a252fca15252d07cb23a1bdd9377a8c6f3efa01531109281ae47f841c
ARG RUST_TOOLCHAIN=nightly-2026-09-17
ENV RUSTUP_HOME=/opt/rustup CARGO_HOME=/opt/cargo PATH=/opt/cargo/bin:$PATH
RUN case "${TARGETARCH}" in \
      amd64) triple=x86_64-unknown-linux-gnu sha="${RUSTUP_SHA256_AMD64}" ;; \
      arm64) triple=aarch64-unknown-linux-gnu sha="${RUSTUP_SHA256_ARM64}" ;; \
      *) echo "unsupported architecture ${TARGETARCH}" >&2; exit 1 ;; \
    esac \
 && curl -fsSL --retry 3 -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/${RUSTUP_VERSION}/${triple}/rustup-init" \
 && echo "${sha}  /tmp/rustup-init" | sha256sum -c - \
 && chmod +x /tmp/rustup-init \
 && /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain "${RUST_TOOLCHAIN}" \
      --component rustc-dev,llvm-tools,rust-src \
 && rm /tmp/rustup-init

# Runtime copy of the same toolchain: charon-driver links librustc_driver from
# `rustc`; rustc-dev, rust-src and llvm-tools are only needed to build Charon.
FROM base AS rust-run
ARG TARGETARCH
ARG RUSTUP_VERSION=1.28.2
ARG RUSTUP_SHA256_AMD64=20a06e644b0d9bd2fbdbfd52d42540bdde820ea7df86e92e533c073da0cdd43c
ARG RUSTUP_SHA256_ARM64=e3853c5a252fca15252d07cb23a1bdd9377a8c6f3efa01531109281ae47f841c
ARG RUST_TOOLCHAIN=nightly-2026-09-17
ENV RUSTUP_HOME=/opt/rustup CARGO_HOME=/opt/cargo PATH=/opt/cargo/bin:$PATH
RUN case "${TARGETARCH}" in \
      amd64) triple=x86_64-unknown-linux-gnu sha="${RUSTUP_SHA256_AMD64}" ;; \
      arm64) triple=aarch64-unknown-linux-gnu sha="${RUSTUP_SHA256_ARM64}" ;; \
      *) echo "unsupported architecture ${TARGETARCH}" >&2; exit 1 ;; \
    esac \
 && curl -fsSL --retry 3 -o /tmp/rustup-init \
      "https://static.rust-lang.org/rustup/archive/${RUSTUP_VERSION}/${triple}/rustup-init" \
 && echo "${sha}  /tmp/rustup-init" | sha256sum -c - \
 && chmod +x /tmp/rustup-init \
 && /tmp/rustup-init -y --no-modify-path --profile minimal --default-toolchain "${RUST_TOOLCHAIN}" \
 && rm -rf /tmp/rustup-init /opt/rustup/toolchains/*/share/doc /opt/rustup/downloads /opt/rustup/tmp

# ------------------------------------------- Charon at the commit Aeneas pins
FROM rust AS charon
ARG CHARON_COMMIT=7b462d9159db2ed3015162352183906a30bfafc6
# Use the toolchain installed above rather than every target in rust-toolchain.
ENV RUSTUP_TOOLCHAIN=nightly-2026-09-17
RUN git init -q /src/charon && cd /src/charon \
 && git fetch -q --depth 1 https://github.com/AeneasVerif/charon "${CHARON_COMMIT}" \
 && git checkout -q FETCH_HEAD \
 && git submodule update -q --init --depth 1 \
 && cd charon && cargo build --release --locked --bins \
 && mkdir -p /opt/charon/bin \
 && cp target/release/charon target/release/charon-driver /opt/charon/bin/ \
 && cp ../rust-toolchain /opt/charon/rust-toolchain

# ------------------------------------- Aeneas binary + Lean library + Mathlib
FROM lean AS aeneas
ARG TARGETARCH
ARG AENEAS_RELEASE=nightly-2026.11.02-ab34bd2
ARG AENEAS_SHA256_AMD64=f8ea7c69036915c7330816b7f5a679efbe443b736e9058c03e91067c66ddade4
ARG AENEAS_SHA256_ARM64=34c6771a6bac6513df71a79adfbd8c1275c86802165da92547065c1af4cc962f
ENV PATH=/opt/lean/bin:$PATH
RUN case "${TARGETARCH}" in \
      amd64) asset=linux-x86_64 sha="${AENEAS_SHA256_AMD64}" ;; \
      arm64) asset=linux-aarch64 sha="${AENEAS_SHA256_ARM64}" ;; \
      *) echo "unsupported architecture ${TARGETARCH}" >&2; exit 1 ;; \
    esac \
 && curl -fsSL --retry 3 -o /tmp/aeneas.tar.gz \
      "https://github.com/AeneasVerif/aeneas/releases/download/${AENEAS_RELEASE}/aeneas-${asset}.tar.gz" \
 && echo "${sha}  /tmp/aeneas.tar.gz" | sha256sum -c - \
 && mkdir -p /opt/aeneas && tar -xzf /tmp/aeneas.tar.gz -C /opt/aeneas && rm /tmp/aeneas.tar.gz \
 && rm -rf /opt/aeneas/backends/fstar /opt/aeneas/backends/hol4 /opt/aeneas/backends/coq
WORKDIR /opt/aeneas/backends/lean
# Fetch the dependencies pinned by Aeneas' lake-manifest, then Mathlib's
# prebuilt cache, then build (or unpack) the Aeneas library itself.
# The workspace ProofCI assembles refers to these packages by path, so their
# Git metadata is not needed once the build is known to be up to date.
COPY toolchain/prune.py /tmp/prune.py
RUN lake exe cache get && lake build Aeneas && lake build --no-build Aeneas \
 && find .lake/packages -name .git -type d -prune -exec rm -rf {} + \
 && rm -rf .lake/*.tar.gz \
 && python3 /tmp/prune.py /opt/aeneas/backends/lean \
 && chmod -R a+rX /opt/aeneas

# --------------------------------------------------------------- Node 24.19.0
# Runs the TypeScript translator. package-lock.json pins the compiler, and
# --ignore-scripts keeps its installation from running anything.
FROM base AS node
ARG TARGETARCH
RUN case "${TARGETARCH}" in \
      amd64) asset=linux-x64 sha=14b342e71204f811bde6153be8e04b62aef63c236fef92b55f9c83154b409647 ;; \
      arm64) asset=linux-arm64 sha=01443c1e1a29e531ccad5a46fefa6df490d2189c49f7955904aecdbb0fe86fdc ;; \
      *) echo "unsupported architecture ${TARGETARCH}" >&2; exit 1 ;; \
    esac \
 && curl -fsSL --retry 3 -o /tmp/node.tar.xz "https://nodejs.org/dist/v24.19.0/node-v24.19.0-${asset}.tar.xz" \
 && echo "${sha}  /tmp/node.tar.xz" | sha256sum -c - \
 && mkdir -p /opt/node && tar -xJf /tmp/node.tar.xz -C /opt/node --strip-components=1 && rm /tmp/node.tar.xz
COPY typescript/package.json typescript/package-lock.json /opt/proofci/typescript/
# npm stays, and pnpm and Yarn 1 are added at pinned versions, because the
# dependency installation of a TypeScript project uses them (proofci/typescript.py).
# They run only in that step, which has the network and never runs project code.
COPY toolchain/package-managers/package.json toolchain/package-managers/package-lock.json /opt/proofci/tools/
RUN cd /opt/proofci/typescript && /opt/node/bin/node /opt/node/lib/node_modules/npm/bin/npm-cli.js ci --ignore-scripts --no-audit --no-fund \
 && cd /opt/proofci/tools && /opt/node/bin/node /opt/node/lib/node_modules/npm/bin/npm-cli.js ci --ignore-scripts --no-audit --no-fund \
 && cd /opt/proofci/typescript \
 && rm -rf node_modules/typescript/lib/*/ package.json package-lock.json /opt/proofci/tools/package.json /opt/proofci/tools/package-lock.json \
            /opt/node/include /opt/node/share /opt/node/lib/node_modules/corepack /opt/node/bin/npm /opt/node/bin/npx /opt/node/bin/corepack

# Checking proofs needs the Lean binaries, shared libraries and .olean files,
# not the static libraries used to compile Lean programs.
FROM lean AS lean-run
RUN find /opt/lean/lib -name '*.a' -delete

# ------------------------------------------------------------ toolchain base
# Everything except ProofCI's own code. It changes only when a pin changes, so
# CI publishes it under a hash of toolchain/ and pull requests reuse it.
FROM base AS toolchain
ENV RUSTUP_HOME=/opt/rustup CARGO_HOME=/opt/cargo \
    PATH=/opt/node/bin:/opt/charon/bin:/opt/aeneas:/opt/lean/bin:/opt/cargo/bin:/usr/local/bin:/usr/bin:/bin \
    PROOFCI_AENEAS_LEAN=/opt/aeneas/backends/lean PYTHONPATH=/opt/proofci
COPY --from=rust-run /opt/rustup /opt/rustup
COPY --from=rust-run /opt/cargo /opt/cargo
COPY --from=charon /opt/charon /opt/charon
COPY --from=lean-run /opt/lean /opt/lean
COPY --from=aeneas /opt/aeneas /opt/aeneas
COPY --from=node /opt/node /opt/node
COPY --from=node /opt/proofci/typescript /opt/proofci/typescript
# bubblewrap (used by ProofCI and lake comparator) mounts a tmpfs here. A volume
# mounted at /tmp/proofci-dev (`proofci dev`) copies this directory's mode on first use,
# so the non-root user can write to it.
RUN mkdir -p /run/user /tmp/proofci-dev && chmod 1777 /run/user /tmp/proofci-dev
ENV HOME=/tmp
USER 1000:1000
WORKDIR /work
ENTRYPOINT ["python3", "-m", "proofci"]

# --------------------------------------------------------------- final image
# The released image: the toolchain plus ProofCI. toolchain/Release.Dockerfile
# adds the same layer on top of a published toolchain base.
FROM toolchain
COPY proofci /opt/proofci/proofci
COPY typescript/translate.mjs typescript/differential.mjs typescript/paths.mjs typescript/lean-tokens.json /opt/proofci/typescript/
