// Shapes of `async` code taken from real projects (umami, lobe-chat, trigger.dev), cut down to
// what ProofCI reads. The outside calls are listed in effects.json.
import { getLink, getTeamUser, getRow, loadSettings, sendMail, audit, fetchAccount, recordUsage } from "./world";
import type { Auth } from "./types";

// umami src/permissions/link.ts
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

// lobe-chat device/guards.ts, with the error class replaced by `Error`
export async function assertDeviceOperable(
  workspaceId: string | undefined,
  role: string,
  deviceId: string,
): Promise<void> {
  if (!workspaceId) return;
  const row = await getRow(deviceId);
  if (!row) throw new Error("Workspace device not found.");
  if (role !== "owner" && row.owner !== role) {
    throw new Error(row.isPublic ? "Workspace viewers cannot operate this device." : "Only the owner can operate this private device.");
  }
}

// An await in a loop, with an early exit
export async function firstNamed(ids: string[]): Promise<string | null> {
  for (const id of ids) {
    const row = await getRow(id);
    if (row !== null) {
      return row.owner;
    }
  }
  return null;
}

// A counter over awaits (a polling loop)
export async function pollCount(id: string, limit: number): Promise<number> {
  let attempts = 0;
  while (attempts < limit) {
    const row = await getRow(id);
    attempts += 1;
    if (row) {
      return attempts;
    }
  }
  return 0;
}

// An awaited call in a condition
export async function mayNotify(id: string): Promise<boolean> {
  if (!(await getRow(id))) {
    return false;
  }
  return true;
}

// trigger.dev-style: try around an await, reading the error message
export async function safeSettings(id: string): Promise<string> {
  try {
    const s = await loadSettings(id);
    return s.theme;
  } catch (e) {
    if (e instanceof Error) {
      return "failed: " + e.message;
    }
    throw e;
  }
}

// cleanup that always runs
export async function sendAndAudit(id: string): Promise<boolean> {
  try {
    await sendMail(id);
    return true;
  } finally {
    await audit(id);
  }
}

// an async function calling another
export async function canViewBoth(auth: Auth, a: string, b: string): Promise<boolean> {
  if (!(await canViewLink(auth, a))) {
    return false;
  }
  return await canViewLink(auth, b);
}

// a rejection that is handled, and one that is not
export async function lenient(id: string): Promise<boolean> {
  try {
    await sendMail(id);
    return true;
  } catch (e) {
    return false;
  }
}

// two outside calls in a row: the order is part of what the function does
export async function copyOwner(id: string): Promise<string> {
  const row = await getRow(id);
  if (!row) {
    return "";
  }
  await sendMail(row.owner);
  await audit(id);
  return row.owner;
}

// cal.com-style: turn a failure into text for the caller
export async function describeSend(id: string): Promise<string> {
  try {
    await sendMail(id);
    return "sent";
  } catch (e) {
    return e instanceof Error ? e.message : String(e);
  }
}

// wrap a failure with context, printing the caught value
export async function sendOrWrap(id: string): Promise<boolean> {
  try {
    await sendMail(id);
    return true;
  } catch (error) {
    throw new Error(`send to ${id} failed: ${error}`);
  }
}

// tell failures apart by their class, and give the rest back
export async function sendClassified(id: string): Promise<string> {
  try {
    await sendMail(id);
    return "sent";
  } catch (err) {
    if (err instanceof TypeError) {
      return "bad input: " + err.message;
    }
    if (err instanceof RangeError) {
      return "retry";
    }
    throw err;
  }
}

// `catch (e: any)` and an assertion
export async function sendNamed(id: string): Promise<string> {
  try {
    await sendMail(id);
    return "sent";
  } catch (e: any) {
    return `${(e as Error).name}: ${e.message}`;
  }
}

// an untyped client (`Promise<any>`), narrowed in the policy
export async function seatsLeft(userId: string, wanted: number): Promise<number> {
  const account = await fetchAccount(userId);
  if (!account || !account.active) {
    return 0;
  }
  await recordUsage(userId, account.plan);
  return account.seats >= wanted ? account.seats - wanted : 0;
}
