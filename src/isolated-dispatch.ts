import { spawn } from 'node:child_process';
import { constants } from 'node:fs';
import { open } from 'node:fs/promises';
import { fileURLToPath } from 'node:url';
import type { Candidate } from './run-store.ts';

const dispatcher = fileURLToPath(new URL('../portable/service_execute.py', import.meta.url));
type Inputs = { store: string; repository: string; snapshot: string; report: string };

/** Invoke the protected dispatcher with staged inputs and no service credentials. */
export async function isolatedDispatch(candidate: Candidate, input: Inputs, signal: AbortSignal): Promise<Record<string, unknown>> {
  if (signal.aborted) throw new Error('Dispatch cancelled');
  const code = await new Promise<number>((resolve, reject) => {
    const env: NodeJS.ProcessEnv = { PATH: process.env.PATH ?? '/usr/bin:/bin', HOME: process.env.HOME ?? '/tmp', PYTHONDONTWRITEBYTECODE: '1' };
    if (process.env.DOCKER_HOST) env.DOCKER_HOST = process.env.DOCKER_HOST;
    for (const key of ['PROOFCI_APPLE_RUNTIME', 'PROOFCI_APPLE_KERNEL', 'PROOFCI_APPLE_KERNEL_SHA256']) {
      if (process.env[key]) env[key] = process.env[key];
    }
    const child = spawn('python3', [dispatcher, '--store', input.store, '--repository', input.repository, '--head', candidate.head, '--base', candidate.base, '--baseline-digest', candidate.baseline, '--candidate-kind', candidate.kind, '--candidate-lane', candidate.lane, '--snapshot', input.snapshot, '--report', input.report], { env, detached: true, stdio: 'ignore' });
    let killTimer: NodeJS.Timeout | undefined;
    const stop = () => {
      if (child.pid === undefined) return;
      try { process.kill(-child.pid, 'SIGTERM'); } catch { return; }
      killTimer = setTimeout(() => { try { if (child.pid !== undefined) process.kill(-child.pid, 'SIGKILL'); } catch {} }, 15_000);
    };
    signal.addEventListener('abort', stop, { once: true });
    if (signal.aborted) stop();
    child.once('error', reject);
    child.once('close', status => {
      signal.removeEventListener('abort', stop);
      if (killTimer) clearTimeout(killTimer);
      if (signal.aborted || status === null) reject(new Error('Dispatch cancelled'));
      else resolve(status);
    });
  });
  const file = await open(input.report, constants.O_RDONLY | constants.O_NOFOLLOW);
  let bytes: Buffer;
  try {
    const stat = await file.stat();
    if (!stat.isFile() || stat.size > 8 * 1024 * 1024) throw new Error('Invalid dispatch report');
    const buffer = Buffer.alloc(8 * 1024 * 1024 + 1);
    let length = 0;
    while (length < buffer.length) {
      const result = await file.read(buffer, length, buffer.length - length, length);
      if (result.bytesRead === 0) break;
      length += result.bytesRead;
    }
    if (length > 8 * 1024 * 1024) throw new Error('Invalid dispatch report');
    bytes = buffer.subarray(0, length);
  } finally { await file.close(); }
  const report: unknown = JSON.parse(bytes.toString('utf8'));
  if (typeof report !== 'object' || report === null || !('version' in report) || report.version !== 1 ||
      !('status' in report) || !['passed', 'blocked', 'error'].includes(String(report.status)) ||
      (code === 0 && report.status !== 'passed') || (code === 1 && report.status !== 'blocked') ||
      (code === 2 && report.status !== 'error') || ![0, 1, 2].includes(code)) throw new Error('Invalid dispatch result');
  if (report.status !== 'error') {
    if (!('envelope' in report) || typeof report.envelope !== 'object' || report.envelope === null ||
        !('head' in report.envelope) || report.envelope.head !== candidate.head ||
        !('base' in report.envelope) || report.envelope.base !== candidate.base ||
        !('repository' in report.envelope) || report.envelope.repository !== input.repository ||
        !('baseline_sha256' in report.envelope) || report.envelope.baseline_sha256 !== candidate.baseline) throw new Error('Dispatch identity mismatch');
  }
  return Object.fromEntries(Object.entries(report));
}
