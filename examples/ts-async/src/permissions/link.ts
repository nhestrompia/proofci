import type { Auth } from '@/lib/types';
import { getLink, getTeamUser } from '@/queries/prisma';

export async function canViewLink({ user, shareToken }: Auth, linkId: string): Promise<boolean> {
  if (user?.isAdmin) {
    return true;
  }

  if (
    shareToken?.linkId === linkId ||
    shareToken?.websiteId === linkId ||
    shareToken?.linkIds?.includes(linkId)
  ) {
    return true;
  }

  if (!user) {
    return false;
  }

  const link = await getLink(linkId);

  if (!link) {
    return false;
  }

  if (link.userId) {
    return user.id === link.userId;
  }

  if (link.teamId) {
    const teamUser = await getTeamUser(link.teamId, user.id);

    return !!teamUser;
  }

  return false;
}
