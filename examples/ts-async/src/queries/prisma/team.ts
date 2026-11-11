export interface TeamUser {
  id: string;
  role: string;
}

export async function getTeamUser(teamId: string, userId: string): Promise<TeamUser | null> {
  throw new Error(`the database is not part of this example: ${teamId} ${userId}`);
}
