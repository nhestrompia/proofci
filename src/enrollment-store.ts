import { randomUUID } from 'node:crypto';
import type { Pool, PoolClient } from 'pg';

export type RepositoryScope = { installationId: number; repositoryId: number };
type Authority = { disable(installationId: number, repositoryIds: number[] | null): Promise<void>; enable(scope: RepositoryScope): Promise<void> };

/** Stores only locally selected repositories. Live GitHub access must also be checked. */
export class EnrollmentStore {
  private readonly pool: Pool;
  private authority?: Authority;
  setAuthority(authority: Authority): void { this.authority = authority; }
  constructor(pool: Pool) { this.pool = pool; }

  async initialize(): Promise<void> {
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_repository_selections (
      installation_id BIGINT NOT NULL CHECK (installation_id > 0),
      repository_id BIGINT NOT NULL CHECK (repository_id > 0),
      generation TEXT NOT NULL DEFAULT '',
      PRIMARY KEY (installation_id, repository_id)
    )`);
    await this.pool.query("ALTER TABLE proofci_repository_selections ADD COLUMN IF NOT EXISTS generation TEXT NOT NULL DEFAULT ''");
    await this.pool.query('CREATE TABLE IF NOT EXISTS proofci_installation_revisions (installation_id BIGINT PRIMARY KEY, revision BIGINT NOT NULL DEFAULT 0)');
    await this.pool.query('CREATE TABLE IF NOT EXISTS proofci_installation_deliveries (delivery_id TEXT PRIMARY KEY)');
  }

  private async transaction<T>(installationId: number, run: (client: PoolClient) => Promise<T>, afterCommit?: (result: T) => Promise<void>): Promise<T> {
    const client = await this.pool.connect();
    try {
      await client.query('SELECT pg_advisory_lock(hashtextextended($1, 0))', [`proofci-authority:${installationId}`]);
      await client.query('BEGIN');
      const result = await run(client);
      await client.query('COMMIT');
      await afterCommit?.(result);
      return result;
    } catch (error) { await client.query('ROLLBACK'); throw error; }
    finally {
      try { await client.query('SELECT pg_advisory_unlock(hashtextextended($1, 0))', [`proofci-authority:${installationId}`]); } finally { client.release(); }
    }
  }

  private async lockRevision(client: PoolClient, installationId: number): Promise<string> {
    await client.query('INSERT INTO proofci_installation_revisions (installation_id) VALUES ($1) ON CONFLICT DO NOTHING', [installationId]);
    const result = await client.query<{ revision: string }>('SELECT revision FROM proofci_installation_revisions WHERE installation_id = $1 FOR UPDATE', [installationId]);
    return result.rows[0]!.revision;
  }

  async beginSelection(scope: RepositoryScope): Promise<string> {
    const result = await this.pool.query<{ revision: string }>('SELECT revision FROM proofci_installation_revisions WHERE installation_id = $1', [scope.installationId]);
    return result.rows[0]?.revision ?? '0';
  }

  async selectIfUnchanged(scope: RepositoryScope, revision: string): Promise<boolean> {
    return this.transaction(scope.installationId, async client => {
      if (await this.lockRevision(client, scope.installationId) !== revision) return false;
      await this.authority?.disable(scope.installationId, [scope.repositoryId]);
      await client.query('INSERT INTO proofci_repository_selections (installation_id, repository_id, generation) VALUES ($1, $2, $3) ON CONFLICT (installation_id, repository_id) DO UPDATE SET generation = EXCLUDED.generation', [scope.installationId, scope.repositoryId, randomUUID()]);
      return true;
    }, async selected => { if (selected) await this.authority?.enable(scope); });
  }

  async select(scope: RepositoryScope): Promise<void> {
    if (!await this.selectIfUnchanged(scope, await this.beginSelection(scope))) throw new Error('Installation changed during selection');
  }

  private async invalidate(installationId: number, sql: string, params: unknown[], deliveryId?: string, onlyIfDeleted = false, repositoryIds: number[] | null = null): Promise<void> {
    await this.transaction(installationId, async client => {
      await this.lockRevision(client, installationId);
      if (deliveryId) {
        const delivery = await client.query('INSERT INTO proofci_installation_deliveries (delivery_id) VALUES ($1) ON CONFLICT DO NOTHING RETURNING delivery_id', [deliveryId]);
        if (!delivery.rowCount) return;
      }
      const deleted = await client.query(sql, params);
      // A webhook or explicit removal fences even an enrollment that has not yet been saved.
      if (!onlyIfDeleted || deleted.rowCount) {
        await this.authority?.disable(installationId, repositoryIds);
        await client.query('UPDATE proofci_installation_revisions SET revision = revision + 1 WHERE installation_id = $1', [installationId]);
      }
    });
  }

  async remove(scope: RepositoryScope): Promise<void> {
    await this.invalidate(scope.installationId, 'DELETE FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = $2', [scope.installationId, scope.repositoryId], undefined, false, [scope.repositoryId]);
  }
  async removeInstallation(installationId: number, deliveryId: string): Promise<void> {
    await this.invalidate(installationId, 'DELETE FROM proofci_repository_selections WHERE installation_id = $1', [installationId], deliveryId);
  }
  async removeRepositories(installationId: number, repositoryIds: number[], deliveryId: string): Promise<void> {
    await this.invalidate(installationId, 'DELETE FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = ANY($2::bigint[])', [installationId, repositoryIds], deliveryId, false, repositoryIds);
  }
  async readVersion(scope: RepositoryScope): Promise<string | null> {
    const result = await this.pool.query<{ generation: string }>('SELECT generation FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = $2', [scope.installationId, scope.repositoryId]);
    return result.rows[0]?.generation ?? null;
  }
  async removeIfVersion(scope: RepositoryScope, version: string): Promise<void> {
    await this.invalidate(scope.installationId, 'DELETE FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = $2 AND generation = $3', [scope.installationId, scope.repositoryId, version], undefined, true, [scope.repositoryId]);
  }
  async isSelected(scope: RepositoryScope): Promise<boolean> {
    return (await this.pool.query('SELECT 1 FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = $2', [scope.installationId, scope.repositoryId])).rowCount === 1;
  }
}
