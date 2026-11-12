// The outside world: bodies are never read, only these signatures are.
export interface Link {
  id: string;
  userId: string | null;
  teamId: string | null;
}
export interface TeamUser {
  id: string;
  role: string;
}
export interface Row {
  owner: string;
  isPublic: boolean;
}
export interface Settings {
  theme: string;
}
export async function getLink(linkId: string): Promise<Link | null> {
  throw new Error("outside");
}
export async function getTeamUser(teamId: string, userId: string): Promise<TeamUser | null> {
  throw new Error("outside");
}
export async function getRow(id: string): Promise<Row | null> {
  throw new Error("outside");
}
export async function loadSettings(id: string): Promise<Settings> {
  throw new Error("outside");
}
export async function sendMail(id: string): Promise<void> {
  throw new Error("outside");
}
export async function audit(id: string): Promise<void> {
  throw new Error("outside");
}
export interface Account {
  active: boolean;
  plan: string;
  seats: number;
}
// An untyped client: the answer's type is written in the policy (`narrowed`).
export async function fetchAccount(userId: string): Promise<any> {
  throw new Error("outside");
}
export async function recordUsage(userId: string, event: any): Promise<void> {
  throw new Error("outside");
}
