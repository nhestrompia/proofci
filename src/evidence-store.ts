import { createHash, randomUUID } from 'node:crypto';
import { execFile } from 'node:child_process';
import { mkdtemp, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { fileURLToPath } from 'node:url';
import { isDeepStrictEqual, promisify } from 'node:util';
import { DeleteObjectCommand, GetObjectCommand, PutObjectCommand, S3Client } from '@aws-sdk/client-s3';
import type { RepositoryScope } from './enrollment-store.ts';
import type { Lease, RunStore } from './run-store.ts';

const MAX_SIZE = 256 * 1024 * 1024;
const checkBundle = fileURLToPath(new URL('../portable/check_hosted_bundle.py', import.meta.url));
const run = promisify(execFile);

/** The control process alone can write bundles. Candidate workers never receive S3 credentials. */
export class EvidenceStore {
  private readonly runs: RunStore;
  private readonly s3: S3Client;
  private readonly bucket: string;
  private readonly retentionSeconds: number;
  constructor(runs: RunStore, s3: S3Client, bucket: string, retentionSeconds: number) {
    if (!bucket || !Number.isSafeInteger(retentionSeconds) || retentionSeconds < 1 || retentionSeconds > 3650 * 86400) throw new Error('Invalid evidence configuration');
    this.runs = runs; this.s3 = s3; this.bucket = bucket; this.retentionSeconds = retentionSeconds;
  }

  async complete(lease: Lease, report: Record<string, unknown>, bytes: Buffer, signal: AbortSignal, authorize: () => Promise<boolean>): Promise<boolean> {
    if (!bytes.length || bytes.length > MAX_SIZE) throw new Error('Invalid evidence size');
    const id = randomUUID();
    const key = `evidence/${lease.candidate.installationId}/${lease.candidate.repositoryId}/${lease.id}/${id}.tar`;
    const sha256 = createHash('sha256').update(bytes).digest('hex');
    const root = await mkdtemp(join(tmpdir(), 'proofci-evidence-'));
    try {
      const path = join(root, 'evidence.tar');
      await writeFile(path, bytes, { flag: 'wx', mode: 0o600 });
      const { stdout } = await run('python3', [checkBundle, path, sha256], { timeout: 60_000, maxBuffer: 10 * 1024 * 1024,
        env: { PATH: process.env.PATH ?? '/usr/bin:/bin', PYTHONDONTWRITEBYTECODE: '1' }, signal });
      const checked: unknown = JSON.parse(stdout);
      if (typeof checked !== 'object' || checked === null || !('report' in checked) || !('envelope' in checked) ||
          !isDeepStrictEqual(checked.report, report) || typeof checked.envelope !== 'object' || checked.envelope === null ||
          !('head' in checked.envelope) || checked.envelope.head !== (lease.candidate.kind === 'pull-request' ? lease.candidate.mergeHead : lease.candidate.head) ||
          !('base' in checked.envelope) || checked.envelope.base !== lease.candidate.base ||
          !('baseline_sha256' in checked.envelope) || checked.envelope.baseline_sha256 !== lease.candidate.baseline ||
          !('envelope' in report) || !isDeepStrictEqual(report.envelope, checked.envelope)) throw new Error('Evidence does not match run report');
    } finally { await rm(root, { recursive: true, force: true }); }
    if (signal.aborted || !await authorize() || signal.aborted) return false;
    if (!await this.runs.reserveEvidence(lease, id, key, sha256, bytes.length)) return false;
    await this.s3.send(new PutObjectCommand({ Bucket: this.bucket, Key: key, Body: bytes, ContentType: 'application/x-tar', IfNoneMatch: '*' }), { abortSignal: AbortSignal.any([signal, AbortSignal.timeout(120_000)]) });
    if (signal.aborted || !await authorize() || signal.aborted) return false;
    return this.runs.completeEvidence(lease, id, report, this.retentionSeconds);
  }

  async download(scope: RepositoryScope, runId: string): Promise<{ kind: 'missing' } | { kind: 'expired' } | { kind: 'available'; bytes: Uint8Array; sha256: string }> {
    const evidence = await this.runs.hostedEvidence(scope, runId);
    if (!evidence) return this.runs.legacyEvidence(scope, runId, this.retentionSeconds);
    if (evidence.expired) return { kind: 'expired' };
    let object;
    try { object = await this.s3.send(new GetObjectCommand({ Bucket: this.bucket, Key: evidence.key })); }
    catch (error) {
      const current = await this.runs.hostedEvidence(scope, runId);
      if (!current) return { kind: 'missing' };
      if (current.expired) return { kind: 'expired' };
      throw error;
    }
    if (object.ContentType !== 'application/x-tar' || object.ContentLength !== evidence.bytes || !object.Body || evidence.bytes > MAX_SIZE) throw new Error('Invalid stored evidence');
    const chunks: Uint8Array[] = [];
    let length = 0;
    const reader = object.Body.transformToWebStream().getReader();
    try {
      while (true) {
        const next = await reader.read();
        if (next.done) break;
        length += next.value.byteLength;
        if (length > evidence.bytes || length > MAX_SIZE) throw new Error('Stored evidence exceeds its recorded size');
        chunks.push(next.value);
      }
    } finally { await reader.cancel().catch(() => {}); reader.releaseLock(); }
    const bytes = Buffer.concat(chunks, length);
    if (bytes.length !== evidence.bytes || createHash('sha256').update(bytes).digest('hex') !== evidence.sha256) throw new Error('Stored evidence digest mismatch');
    const current = await this.runs.hostedEvidence(scope, runId);
    if (!current) return { kind: 'missing' };
    if (current.expired) return { kind: 'expired' };
    return { kind: 'available', bytes, sha256: evidence.sha256 };
  }

  async expire(): Promise<void> {
    await this.runs.expireLegacyEvidence(this.retentionSeconds);
    for (const item of await this.runs.expiredEvidence()) {
      try {
        await this.s3.send(new DeleteObjectCommand({ Bucket: this.bucket, Key: item.key }));
        await this.runs.evidenceDeleted(item.id);
      } catch { /* Retry on the next sweep. */ }
    }
  }
}
