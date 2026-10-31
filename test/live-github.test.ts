import { test } from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createPrivateKey } from 'node:crypto';
import { GitHubApp } from '../src/github-app.ts';

const keyFile = process.env.PROOFCI_TEST_GITHUB_KEY_FILE;
const appId = Number(process.env.PROOFCI_TEST_GITHUB_APP_ID);
const installationId = Number(process.env.PROOFCI_TEST_GITHUB_INSTALLATION_ID);
const repositoryId = Number(process.env.PROOFCI_TEST_GITHUB_REPOSITORY_ID);
const otherRepositoryId = Number(process.env.PROOFCI_TEST_GITHUB_UNSELECTED_REPOSITORY_ID);
const enabled = !!keyFile && [appId, installationId, repositoryId, otherRepositoryId].every(value => Number.isSafeInteger(value) && value > 0);

test('real installation renews scoped access and rejects an unselected repository', { skip: !enabled }, async () => {
  assert.ok(keyFile);
  const github = new GitHubApp({ appId, privateKey: createPrivateKey(readFileSync(keyFile)) });
  const selected = { installationId, repositoryId };
  assert.equal(await github.checkInstallationAccess(selected), true);
  assert.equal(await github.checkInstallationAccess(selected), true);
  assert.equal(await github.checkInstallationAccess({ installationId, repositoryId: otherRepositoryId }), false);
  assert.equal(await github.checkInstallationAccess({ installationId: Number.MAX_SAFE_INTEGER, repositoryId }), false);
});
