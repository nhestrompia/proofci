#!/usr/bin/env bash
set -euo pipefail
root=$(git rev-parse --show-toplevel)
tmp=$(mktemp -d)
builder=proofci-$$
trap 'docker buildx rm "$builder" >/dev/null 2>&1 || true; rm -rf "$tmp"' EXIT
docker buildx create --name "$builder" --driver docker-container >/dev/null
curl --fail --location --retry 3 'https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux_aarch64.tar.zst' -o "$tmp/lean.tar.zst"
curl --fail --location --retry 3 'https://deb.debian.org/debian/pool/main/b/bubblewrap/bubblewrap_0.12.0-1~deb13u1_arm64.deb' -o "$tmp/bwrap.deb"
printf '%s  %s\n' c8f0f8a3920e839718b1343e6781fd80a3e9b1024fbcd7078eb30f54e806b028 "$tmp/lean.tar.zst" d1ac1d0d81c815fc15842b9f04fdf414830ed14a0a602bf6344740f90bb36c00 "$tmp/bwrap.deb" | sha256sum -c -
tar --zstd -xf "$tmp/lean.tar.zst" -C "$tmp"
mkdir "$tmp/bwrap"
(cd "$tmp/bwrap" && ar x "$tmp/bwrap.deb" && tar -xJf data.tar.xz)
docker buildx build --builder "$builder" --provenance=false --build-arg SOURCE_DATE_EPOCH=0 \
  --output "type=docker,dest=$tmp/image.tar,rewrite-timestamp=true" --platform linux/arm64 \
  --build-context "lean=$tmp/lean-4.35.0-linux_aarch64" --build-context "bubblewrap=$tmp/bwrap" \
  -f "$root/portable/Dockerfile" -t proofci-validator-local "$root"
docker load -i "$tmp/image.tar"
expected=sha256:0768934aa3f0d7d40edb6bbe879c97ef66f2fd825549861ee8bc2598adda4054
actual=$(docker image inspect --format '{{.Id}}' proofci-validator-local)
config=sha256:0fed6287e0b5723db99852e9aad1c45d35e284c5f1891c42c90240444793a594
if [ "$actual" != "$expected" ] && [ "$actual" != "$config" ]; then
  printf 'Built image identity %s does not match pinned identity %s\n' "$actual" "$expected" >&2
  exit 1
fi
