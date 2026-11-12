// In umami these are Prisma queries. ProofCI never reads their bodies: the policy lists both
// functions under `effects`, so a proof holds for whatever the database answers.
export interface Link {
  id: string;
  userId: string | null;
  teamId: string | null;
}

export async function getLink(linkId: string): Promise<Link | null> {
  throw new Error(`the database is not part of this example: ${linkId}`);
}
