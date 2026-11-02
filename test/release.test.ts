import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { readFileSync } from 'node:fs';
import { RELEASE, REPORT_VERSION, SCHEMA_VERSION } from '../src/deployment.ts';

const release = JSON.parse(readFileSync('deploy/release.json', 'utf8'));
const sha = (path: string) => createHash('sha256').update(readFileSync(path)).digest('hex');

test('the release manifest matches the deployment files and code it pins', () => {
  assert.equal(release.release, RELEASE);
  assert.equal(release.schema_version, SCHEMA_VERSION);
  assert.equal(release.report_version, REPORT_VERSION);
  const compose = readFileSync('deploy/compose.yaml', 'utf8');
  const dockerfile = readFileSync('deploy/Dockerfile', 'utf8');
  assert.ok(compose.includes(release.images.postgres.split('@')[1]) && compose.includes(release.images.object_store.split('@')[1]));
  assert.ok(dockerfile.includes(`FROM ${release.images.node}`) && dockerfile.includes(`FROM ${release.images.docker_cli}`));
  assert.ok(dockerfile.includes(`DEBIAN_SNAPSHOT=${release.debian_snapshot}`));
  // Every image reference in the deployment is pinned by digest.
  for (const line of [...compose.split('\n'), ...dockerfile.split('\n')].filter(line => /^\s*(image:|FROM )/.test(line) && !line.includes('PROOFCI_CONTROL_IMAGE'))) assert.match(line, /@sha256:[a-f0-9]{64}/, line);
  assert.equal(sha('package-lock.json'), release.npm_lockfile_sha256);
  assert.equal(sha('portable/resource_limits.json'), release.verifier.resource_limits_sha256);
  const pinned = JSON.parse(execFileSync('python3', ['-c', `import sys, json, hashlib; sys.path.insert(0, 'portable'); import proofci, vm_container, container
print(json.dumps({'toolchain': proofci.TOOLCHAIN_SHA256, 'policy': proofci.policy_digest(), 'dependency': hashlib.sha256((proofci.VALIDATOR / 'core-dependencies.json').read_bytes()).hexdigest(), 'vm': vm_container.VM_IMAGE_ID, 'validator': container.IMAGE_ID}))`], { encoding: 'utf8' }));
  assert.deepEqual(pinned, { toolchain: release.verifier.lean_toolchain_sha256, policy: release.verifier.trust_policy_sha256,
    dependency: release.verifier.core_dependencies_sha256, vm: release.images.verifier_vm, validator: release.images.validator_container });
});
