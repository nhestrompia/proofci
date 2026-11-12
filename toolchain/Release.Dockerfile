# ProofCI's code on top of a published toolchain base (see toolchain/Dockerfile,
# target `toolchain`). Builds in seconds; produces the same image as the final
# stage of toolchain/Dockerfile.
ARG BASE=proofci-toolchain:base
FROM ${BASE}
COPY proofci /opt/proofci/proofci
COPY typescript/translate.mjs typescript/differential.mjs typescript/paths.mjs typescript/hazard.mjs typescript/narrow.mjs typescript/lean-tokens.json /opt/proofci/typescript/

# The TypeScript bridge: Core (the model of JavaScript), the number model and the tactics that tie a
# function's Lean view to it, built once here. They are the image's, never the pull request's.
USER root
COPY spike/core/Core.lean spike/core/F64.lean spike/core/ProofciJs.lean /opt/proofci/spike/core/
COPY spike/core/Spike/Rules.lean spike/core/Spike/LoopInd.lean spike/core/Spike/Safe.lean spike/core/Spike/Sim.lean spike/core/Spike/Tac.lean /opt/proofci/spike/core/Spike/
COPY toolchain/bridge/lakefile.lean /tmp/bridge-lakefile.lean
COPY toolchain/bridge/install.sh /tmp/bridge-install.sh
RUN /tmp/bridge-install.sh && rm /tmp/bridge-lakefile.lean /tmp/bridge-install.sh
COPY spike/core/lower.mjs spike/core/bridge3.mjs spike/core/action_bridge.mjs /opt/proofci/spike/core/
RUN chmod -R a+rX /opt/proofci/spike
USER 1000:1000
