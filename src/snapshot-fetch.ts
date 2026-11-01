import { spawn } from 'node:child_process';
import { mkdir, readdir, lstat } from 'node:fs/promises';
import { join } from 'node:path';

const MAX_BYTES = 256 * 1024 * 1024;
const MAX_FILE_BYTES = 128 * 1024 * 1024;
const MAX_FILES = 100_000;

async function withinLimits(root: string): Promise<boolean> {
  let bytes = 0, count = 0;
  const directories = [root];
  while (directories.length) {
    const dir = directories.pop();
    if (!dir) break;
    for (const entry of await readdir(dir, { withFileTypes: true })) {
      if (++count > MAX_FILES) return false;
      const path = join(dir, entry.name);
      if (entry.isDirectory()) directories.push(path);
      else if (entry.isFile()) {
        try {
          const size = (await lstat(path)).size;
          if (size > MAX_FILE_BYTES || (bytes += size) > MAX_BYTES) return false;
        } catch (error) { if (!(error instanceof Error) || !('code' in error) || error.code !== 'ENOENT') throw error; }
      }
    }
  }
  return true;
}

async function git(args: string[], env: NodeJS.ProcessEnv, root: string, signal: AbortSignal): Promise<void> {
  if (signal.aborted) throw new Error('Snapshot fetch cancelled');
  await new Promise<void>((resolve, reject) => {
    const child = spawn('git', ['-c', 'core.hooksPath=/dev/null', '-c', 'core.fsmonitor=false', '-c', 'submodule.recurse=false', '-c', 'protocol.file.allow=never', '-c', 'protocol.ext.allow=never', '-c', 'fetch.fsckObjects=true', ...args], { env, detached: true, stdio: 'ignore' });
    let failure: string | null = null, checking = false, finished = false;
    const stop = (reason: string) => {
      if (finished) return;
      failure ??= reason;
      try { if (child.pid !== undefined) process.kill(-child.pid, 'SIGKILL'); } catch {}
    };
    const abort = () => stop('Snapshot fetch cancelled');
    const deadline = setTimeout(() => stop('Snapshot fetch timed out'), 120_000);
    const monitor = setInterval(() => {
      if (checking) return;
      checking = true;
      void withinLimits(root).then(ok => { if (!ok) stop('Snapshot exceeds limits'); }, () => stop('Snapshot limit check failed')).finally(() => { checking = false; });
    }, 250);
    signal.addEventListener('abort', abort, { once: true });
    if (signal.aborted) abort();
    child.once('error', () => { failure ??= 'Snapshot fetch failed'; });
    child.once('close', code => {
      finished = true;
      clearTimeout(deadline); clearInterval(monitor); signal.removeEventListener('abort', abort);
      if (failure || code !== 0) reject(new Error(failure ?? 'Snapshot fetch failed'));
      else resolve();
    });
  });
}

/** Fetch only an immutable commit from the repository selected by GitHub's API. */
export async function fetchSnapshot(input: { owner: string; name: string; token: string; head: string; base: string; root: string; signal: AbortSignal }): Promise<{ snapshot: string; repository: string }> {
  if (!/^[A-Za-z0-9](?:[A-Za-z0-9-]{0,37}[A-Za-z0-9])?$/.test(input.owner) || !/^[A-Za-z0-9_.-]+$/.test(input.name) || input.name === '.' || input.name === '..' ||
      !/^[a-f0-9]{40}$/.test(input.head) || !/^[a-f0-9]{40}$/.test(input.base) || !input.token) throw new Error('Invalid snapshot identity');
  const snapshot = join(input.root, 'snapshot');
  const template = join(input.root, 'empty-template');
  await mkdir(snapshot); await mkdir(template);
  const repository = `https://github.com/${input.owner}/${input.name}.git`;
  const env: NodeJS.ProcessEnv = {
    PATH: '/usr/bin:/bin:/usr/local/bin:/opt/homebrew/bin', HOME: input.root, GIT_CONFIG_NOSYSTEM: '1',
    GIT_CONFIG_GLOBAL: '/dev/null', GIT_CONFIG_SYSTEM: '/dev/null', GIT_TERMINAL_PROMPT: '0',
    GIT_LFS_SKIP_SMUDGE: '1', GIT_TEMPLATE_DIR: template,
  };
  await git(['init', '-q', snapshot], env, input.root, input.signal);
  await git(['-C', snapshot, 'remote', 'add', 'origin', repository], env, input.root, input.signal);
  const auth = Buffer.from(`x-access-token:${input.token}`).toString('base64');
  await git(['-C', snapshot, 'fetch', '--no-tags', '--no-recurse-submodules', 'origin', input.head, input.base],
    { ...env, GIT_CONFIG_COUNT: '1', GIT_CONFIG_KEY_0: 'http.https://github.com/.extraheader', GIT_CONFIG_VALUE_0: `AUTHORIZATION: basic ${auth}` }, input.root, input.signal);
  await git(['-C', snapshot, 'checkout', '-q', '--detach', input.head], env, input.root, input.signal);
  if (!await withinLimits(input.root)) throw new Error('Snapshot exceeds limits');
  return { snapshot, repository };
}
