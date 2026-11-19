// The outside world: bodies are never read, only these signatures are.
export async function getName(id: string): Promise<string> {
  throw new Error("outside");
}
export async function getCount(id: string): Promise<number> {
  throw new Error("outside");
}
export async function logEvent(id: string): Promise<void> {
  throw new Error("outside");
}
