# ProofCI's code on top of a published toolchain base (see toolchain/Dockerfile,
# target `toolchain`). Builds in seconds; produces the same image as the final
# stage of toolchain/Dockerfile.
ARG BASE
FROM ${BASE}
COPY proofci /opt/proofci/proofci
