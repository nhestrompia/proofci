# ProofCI control service. Base images are pinned by digest; see deploy/release.json.
FROM docker@sha256:625d9431a9f54c5a2bc90f24f0e1c3d55b1349fd857dd85035f98c2c9acbdd4d AS docker-cli

FROM node@sha256:c86ecead9e55a5210ac1727de38a4ca840bf03dcaf34dc9749addbf383b1920c
ARG DEBIAN_SNAPSHOT=20261101T000000Z
# Debian packages come from a fixed snapshot so a rebuild installs the same versions.
RUN printf 'deb [check-valid-until=no] http://snapshot.debian.org/archive/debian/%s bookworm main\ndeb [check-valid-until=no] http://snapshot.debian.org/archive/debian-security/%s bookworm-security main\n' "$DEBIAN_SNAPSHOT" "$DEBIAN_SNAPSHOT" > /etc/apt/sources.list \
 && rm -f /etc/apt/sources.list.d/debian.sources \
 && apt-get -o Acquire::Retries=5 update \
 && apt-get install -y --no-install-recommends python3 git ca-certificates tini \
 && rm -rf /var/lib/apt/lists/*
COPY --from=docker-cli /usr/local/bin/docker /usr/local/bin/docker
WORKDIR /opt/proofci
COPY package.json package-lock.json ./
RUN npm ci --omit=dev --ignore-scripts && npm cache clean --force
COPY src ./src
COPY portable ./portable
COPY experiments/source-binding ./experiments/source-binding
COPY deploy ./deploy
COPY LICENSE ./LICENSE
RUN rm -rf portable/test_* experiments/source-binding/test_* experiments/source-binding/evidence deploy/exercise/state \
 && find . -name __pycache__ -prune -exec rm -rf {} + \
 && python3 -c 'import sys; assert sys.version_info >= (3, 11)'
ENV NODE_ENV=production PYTHONDONTWRITEBYTECODE=1 PROOFCI_LISTEN_HOST=0.0.0.0
LABEL org.opencontainers.image.licenses="MIT" org.opencontainers.image.version="0.23.0"
USER node
EXPOSE 3000
ENTRYPOINT ["/usr/bin/tini", "--"]
CMD ["node", "src/server.ts"]
