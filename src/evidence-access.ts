import type { RepositoryScope } from './enrollment-store.ts';
import type { EnrollmentStore } from './enrollment-store.ts';
import type { GitHubApp } from './github-app.ts';
import type { OAuthSessions } from './oauth.ts';
import type { EvidenceStore } from './evidence-store.ts';
import { authorizeNewWork } from './repository-authorization.ts';

export async function downloadEvidence(input: { scope: RepositoryScope; runId: string; session: string;
  selections: Pick<EnrollmentStore, 'readVersion' | 'removeIfVersion'>;
  github: Pick<GitHubApp, 'checkMaintainerAccess' | 'installationAccess'>;
  sessions: Pick<OAuthSessions, 'checkMaintainer'>; evidence: Pick<EvidenceStore, 'download'>
}): ReturnType<EvidenceStore['download']> {
  const authorized = async () => await input.sessions.checkMaintainer({ session: input.session, scope: input.scope, github: input.github }) !== null &&
    await authorizeNewWork({ scope: input.scope, selections: input.selections, github: input.github });
  try {
    if (!await authorized()) return { kind: 'missing' };
    const result = await input.evidence.download(input.scope, input.runId);
    if (!await authorized()) return { kind: 'missing' };
    return result;
  } catch { return { kind: 'missing' }; }
}
