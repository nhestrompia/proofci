/**
 * Exercise entry point: the production control service with only two substitutions.
 * GitHub HTTPS requests go to the local simulator, and snapshots are fetched from a
 * local bare repository instead of github.com. Everything else (PostgreSQL, S3,
 * protected stores, the VM verifier, webhooks, publication, evidence) is unchanged.
 */
import { spawn } from 'node:child_process';
import { mkdir } from 'node:fs/promises';
import { join } from 'node:path';
import { startControl } from '../../src/control.ts';
import type { GitHubApp } from '../../src/github-app.ts';

const simulator = process.env.PROOFCI_EXERCISE_GITHUB_URL;
const repositories = process.env.PROOFCI_EXERCISE_GIT_ROOT;
if (!simulator || !repositories) throw new Error('Set PROOFCI_EXERCISE_GITHUB_URL and PROOFCI_EXERCISE_GIT_ROOT');

const request: typeof fetch = (input, init) => {
  const url = new URL(typeof input === 'string' ? input : input instanceof URL ? input.href : input.url);
  if (url.origin !== 'https://api.github.com' && url.origin !== 'https://github.com') throw new Error(`Unexpected request to ${url.origin}`);
  return fetch(new URL(url.pathname + url.search, simulator), { ...init, redirect: 'error' });
};

function git(args: string[], cwd?: string): Promise<void> {
  return new Promise((resolve, reject) => {
    const child = spawn('git', args, { cwd, stdio: 'ignore', env: { PATH: '/usr/bin:/bin', HOME: '/tmp', GIT_CONFIG_NOSYSTEM: '1', GIT_CONFIG_GLOBAL: '/dev/null' } });
    child.once('error', reject);
    child.once('close', code => code === 0 ? resolve() : reject(new Error(`git ${args[0]} failed`)));
  });
}

const wrapGitHub = (app: GitHubApp): GitHubApp => {
  const wrapped = Object.create(app) as GitHubApp;
  wrapped.stageSnapshot = async (scope, input) => {
    // Resolve the repository through the App exactly as production does, then fetch locally.
    if (await app.installationAccess(scope) !== 'allowed') throw new Error('GitHub access unavailable');
    const name = process.env[`PROOFCI_EXERCISE_REPOSITORY_${scope.repositoryId}`];
    if (!name || !/^[A-Za-z0-9-]+\/[A-Za-z0-9_.-]+$/.test(name)) throw new Error('Unknown exercise repository');
    const snapshot = join(input.root, 'snapshot');
    await mkdir(snapshot);
    await git(['init', '-q', snapshot]);
    await git(['-C', snapshot, 'remote', 'add', 'origin', `https://github.com/${name}.git`]);
    await git(['-C', snapshot, 'fetch', '-q', '--no-tags', join(repositories, `${name.replace('/', '__')}.git`), input.head, input.base]);
    await git(['-C', snapshot, 'checkout', '-q', '--detach', input.head]);
    return { snapshot, repository: `https://github.com/${name}.git` };
  };
  return wrapped;
};

const control = await startControl(process.env, { request, wrapGitHub });
process.stdout.write(`ProofCI exercise control listening on ${control.port}\n`);
for (const signal of ['SIGTERM', 'SIGINT'] as const) process.once(signal, () => { void control.stop(); });
