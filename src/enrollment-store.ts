import { randomUUID } from 'node:crypto';
import type { Pool } from 'pg';

export type RepositoryScope = { installationId: number; repositoryId: number };

/** Stores only locally selected repositories. Live GitHub access must also be checked. */
export class EnrollmentStore {
  private readonly pool: Pool;

  constructor(pool: Pool) { this.pool = pool; }

  async initialize(): Promise<void> {
    await this.pool.query(`CREATE TABLE IF NOT EXISTS proofci_repository_selections (
      installation_id BIGINT NOT NULL CHECK (installation_id > 0),
      repository_id BIGINT NOT NULL CHECK (repository_id > 0),
      generation TEXT NOT NULL DEFAULT '',
      PRIMARY KEY (installation_id, repository_id)
    )`);
    await this.pool.query("ALTER TABLE proofci_repository_selections ADD COLUMN IF NOT EXISTS generation TEXT NOT NULL DEFAULT ''");
  }

  async select(scope: RepositoryScope): Promise<void> {
    await this.pool.query('INSERT INTO proofci_repository_selections (installation_id, repository_id, generation) VALUES ($1, $2, $3) ON CONFLICT (installation_id, repository_id) DO UPDATE SET generation = EXCLUDED.generation', [scope.installationId, scope.repositoryId, randomUUID()]);
  }

  async remove(scope: RepositoryScope): Promise<void> {
    await this.pool.query('DELETE FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = $2', [scope.installationId, scope.repositoryId]);
  }

  async readVersion(scope: RepositoryScope): Promise<string | null> {
    const result = await this.pool.query<{ generation: string }>('SELECT generation FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = $2', [scope.installationId, scope.repositoryId]);
    return result.rows[0]?.generation ?? null;
  }

  async removeIfVersion(scope: RepositoryScope, version: string): Promise<void> {
    await this.pool.query('DELETE FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = $2 AND generation = $3', [scope.installationId, scope.repositoryId, version]);
  }

  async isSelected(scope: RepositoryScope): Promise<boolean> {
    const result = await this.pool.query('SELECT 1 FROM proofci_repository_selections WHERE installation_id = $1 AND repository_id = $2', [scope.installationId, scope.repositoryId]);
    return result.rowCount === 1;
  }
}
