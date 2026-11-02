#!/bin/sh
# Generate deployment credentials and deploy/.env for a new ProofCI pilot.
# Usage: deploy/init.sh SECRETS_DIR STATE_DIR WORK_DIR
# Copy the GitHub App private key to SECRETS_DIR/github-app.pem and the OAuth
# client secret to SECRETS_DIR/github-client-secret afterwards.
set -eu
[ $# -eq 3 ] || { echo "usage: $0 SECRETS_DIR STATE_DIR WORK_DIR" >&2; exit 2; }
secrets=$1 state=$2 work=$3
for dir in "$secrets" "$state" "$work"; do
  case $dir in /*) ;; *) echo "$dir must be an absolute path" >&2; exit 2 ;; esac
done
here=$(cd "$(dirname "$0")" && pwd)
[ ! -e "$here/.env" ] || { echo "$here/.env already exists" >&2; exit 1; }
umask 077
mkdir -p "$secrets" "$state" "$work"
random() { od -An -N32 -tx1 /dev/urandom | tr -d ' \n'; }
pg=$(random); s3key=proofci$(random | cut -c1-12); s3secret=$(random)
printf '%s\n' "$pg" > "$secrets/postgres-password"
printf 'postgres://proofci:%s@postgres:5432/proofci\n' "$pg" > "$secrets/database-url"
printf '[default]\naws_access_key_id = %s\naws_secret_access_key = %s\n' "$s3key" "$s3secret" > "$secrets/s3-credentials"
random > "$secrets/github-webhook-secret"; echo >> "$secrets/github-webhook-secret"
docker_gid=$(stat -c %g /var/run/docker.sock 2>/dev/null || echo 0)
cat > "$here/.env" <<ENV
PROOFCI_ORIGIN=https://proofci.example.com
GITHUB_APP_ID=
GITHUB_CLIENT_ID=
PROOFCI_SECRETS_DIR=$secrets
PROOFCI_STATE_DIR=$state
PROOFCI_WORK_DIR=$work
PROOFCI_DOCKER_GID=$docker_gid
PROOFCI_S3_ACCESS_KEY=$s3key
PROOFCI_S3_SECRET_KEY=$s3secret
PROOFCI_EVIDENCE_RETENTION_DAYS=30
ENV
echo "Wrote $here/.env and credentials in $secrets."
echo "Next: add github-app.pem and github-client-secret, set the App IDs in .env, then follow deploy/README.md."
