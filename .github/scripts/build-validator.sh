#!/usr/bin/env bash
set -euo pipefail
root=$(git rev-parse --show-toplevel)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
curl --fail --location --retry 3 'https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux_aarch64.tar.zst' -o "$tmp/lean.tar.zst"
curl --fail --location --retry 3 'https://deb.debian.org/debian/pool/main/b/bubblewrap/bubblewrap_0.12.0-1~deb13u1_arm64.deb' -o "$tmp/bwrap.deb"
printf '%s  %s\n' c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028 "$tmp/lean.tar.zst" d1ac1d0d81c815fc15842b9f04fdf414830ed14a0a602bf6344740f90bb36c00 "$tmp/bwrap.deb" | sha256sum -c -
tar --zstd -xf "$tmp/lean.tar.zst" -C "$tmp"
mkdir "$tmp/bwrap"
(cd "$tmp/bwrap" && ar x "$tmp/bwrap.deb" && tar -xJf data.tar.xz)
docker buildx build --provenance=false --build-arg SOURCE_DATE_EPOCH=0 \
  --output "type=docker,dest=$tmp/image.tar,rewrite-timestamp=true" --platform linux/arm64 \
  --build-context "lean=$tmp/lean-4.35.0-linux_aarch64" --build-context "bubblewrap=$tmp/bwrap" \
  -f "$root/portable/Dockerfile" -t proofci-validator-local "$root"
docker load -i "$tmp/image.tar"
