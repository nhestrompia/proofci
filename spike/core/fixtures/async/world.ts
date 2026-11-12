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
// Objects the code is handed: it passes them around and calls their listed methods, nothing else.
export interface Db {
  find(id: string): Promise<Row | null>;
  remove(id: string): Promise<void>;
}
export interface Mailer {
  send(to: string, body: string): Promise<void>;
}
export interface Ctx {
  db: Db;
  mailer: Mailer | null;
  user: string;
}
export async function sendVia(mailer: Mailer, to: string): Promise<boolean> {
  throw new Error("outside");
}
