import { test } from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { mkdtempSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { Pool } from 'pg';
import { EnrollmentStore } from '../src/enrollment-store.ts';
import { LocalAuthority } from '../src/local-authority.ts';

const databaseUrl = process.env.PROOFCI_TEST_DATABASE_URL;
test('enrollment commits before enabling authority and removal fences before commit', { skip: !databaseUrl }, async () => {
  const pool = new Pool({ connectionString: databaseUrl });
  const root = mkdtempSync(join(tmpdir(), 'proofci-authority-test-'));
  const storePath = join(root, 'baseline.db');
  const scope = { installationId: 910019, repositoryId: 910020 };
  const repository = 'https://github.com/example/authority-test.git';
  const script = `import sys\nsys.path.insert(0, 'portable')\nimport baselines, authority\nfrom test_baselines import manifest\ndb = baselines.open_store(sys.argv[1])\ndata = baselines.encoded(manifest())\ndb.execute('INSERT INTO baselines(digest,manifest,manifest_path,baseline_sha256,repository,initial_head,approval_identity,approval_source,report) VALUES(?,?,?,?,?,?,?,?,?)', (baselines.sha(data),data,'contracts.json','b'*64,sys.argv[2],'a'*40,'1','test',b'{}'))\ndb.execute('INSERT INTO active VALUES(1,?)',(baselines.sha(data),))\ndb.commit()\ndb.close()\nauthority.mutate(sys.argv[1], 'bootstrap', sys.argv[2], head='a'*40, actor=1, ref='refs/heads/main')`;
  try {
    execFileSync('python3', ['-c', script, storePath, repository], { env: { ...process.env, PYTHONDONTWRITEBYTECODE: '1' } });
    const authority = new LocalAuthority([{ ...scope, store: storePath, repository, ref: 'refs/heads/main' }]);
    const store = new EnrollmentStore(pool);
    await store.initialize();
    const events: string[] = [];
    store.setAuthority({
      disable: async (installationId, repositoryIds) => {
        await authority.disable(installationId, repositoryIds);
        events.push('disabled');
        assert.equal(await authority.current(scope), null);
      },
      enable: async item => {
        assert.equal(await store.isSelected(item), true);
        await authority.enable(item);
        events.push('enabled');
      },
    });
    await store.select(scope);
    const enrolledEpoch = await authority.current(scope);
    assert.ok(enrolledEpoch);
    await store.remove(scope);
    assert.equal(await authority.current(scope), null);
    await store.select(scope);
    assert.notEqual(await authority.current(scope), enrolledEpoch);
    assert.deepEqual(events, ['disabled', 'enabled', 'disabled', 'disabled', 'enabled']);
    store.setAuthority({
      disable: async (installationId, repositoryIds) => {
        await authority.disable(installationId, repositoryIds);
        throw new Error('interrupted after fence');
      },
      enable: async item => authority.enable(item),
    });
    await assert.rejects(store.remove(scope), /interrupted after fence/);
    assert.equal(await store.isSelected(scope), true);
    assert.equal(await authority.current(scope), null);
  } finally {
    await pool.query('DELETE FROM proofci_repository_selections WHERE installation_id=$1', [scope.installationId]).catch(() => {});
    await pool.query('DELETE FROM proofci_installation_revisions WHERE installation_id=$1', [scope.installationId]).catch(() => {});
    await pool.end();
    rmSync(root, { recursive: true, force: true });
  }
});

test('completed runs lose applicability when authority changes and can be scheduled again', { skip: !databaseUrl }, async () => {
  const pool = new Pool({ connectionString: databaseUrl });
  const scope = { installationId: 910021, repositoryId: 910022 };
  try {
    const { RunStore } = await import('../src/run-store.ts');
    const enrollment = new EnrollmentStore(pool);
    const { current } = { current: async () => revision };
    let revision = 1;
    const runs = new RunStore(pool, { current });
    await enrollment.initialize();
    await runs.initialize();
    await enrollment.select(scope);
    const candidate = { ...scope, kind: 'head-snapshot' as const, lane: 'refs/heads/main', head: 'a'.repeat(40), base: 'a'.repeat(40), baseline: 'b'.repeat(64) };
    const id = await runs.admit(candidate);
    const lease = await runs.claim(60_000);
    assert.ok(lease);
    assert.equal(lease.candidate.authorityEpoch, 1);
    assert.equal(await runs.complete(lease, { status: 'passed', authority_epoch: 1 }), true);
    assert.equal((await runs.inspect(scope, id))?.applicable, true);
    revision = 2;
    assert.equal((await runs.inspect(scope, id))?.applicable, false);
    const newId = await runs.admit(candidate);
    assert.notEqual(newId, id);
    assert.equal((await runs.inspect(scope, id))?.applicable, false);
    const nextLease = await runs.claim(60_000);
    assert.ok(nextLease);
    revision = 3;
    assert.equal(await runs.complete(nextLease, { status: 'passed', authority_epoch: 2 }), true);
    assert.equal((await runs.inspect(scope, newId))?.applicable, false);
    assert.equal((await new RunStore(pool).inspect(scope, newId))?.applicable, false);
  } finally {
    await pool.query('DELETE FROM proofci_runs WHERE installation_id=$1', [scope.installationId]).catch(() => {});
    await pool.query('DELETE FROM proofci_repository_selections WHERE installation_id=$1', [scope.installationId]).catch(() => {});
    await pool.query('DELETE FROM proofci_installation_revisions WHERE installation_id=$1', [scope.installationId]).catch(() => {});
    await pool.end();
  }
});

test('a selection racing removal cannot re-enable a stale enrollment', { skip: !databaseUrl }, async () => {
  const pool = new Pool({ connectionString: databaseUrl });
  const scope = { installationId: 910023, repositoryId: 910024 };
  let enabled = true;
  let beginDisable: () => void = () => {};
  let finishDisable: () => void = () => {};
  const disabled = new Promise<void>(resolve => { beginDisable = resolve; });
  const release = new Promise<void>(resolve => { finishDisable = resolve; });
  try {
    const store = new EnrollmentStore(pool);
    await store.initialize();
    await store.select(scope);
    const oldRevision = await store.beginSelection(scope);
    store.setAuthority({
      disable: async () => { enabled = false; beginDisable(); await release; },
      enable: async () => { enabled = true; },
    });
    const removal = store.remove(scope);
    await disabled;
    const selection = store.selectIfUnchanged(scope, oldRevision);
    finishDisable();
    await removal;
    assert.equal(await selection, false);
    assert.equal(enabled, false);
    assert.equal(await store.isSelected(scope), false);
  } finally {
    finishDisable();
    await pool.query('DELETE FROM proofci_repository_selections WHERE installation_id=$1', [scope.installationId]).catch(() => {});
    await pool.query('DELETE FROM proofci_installation_revisions WHERE installation_id=$1', [scope.installationId]).catch(() => {});
    await pool.end();
  }
});
