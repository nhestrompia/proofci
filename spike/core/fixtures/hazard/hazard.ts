// The lost update: read shared state, await, write it back. lobe-chat's appendAdvanceToPartial
// has this shape (a store read, a computation, a store write), and so does any counter or cache
// kept in the process. Two calls running together lose an update, which no history of outside
// calls explains, so a proof about the sequential reading would be false of the real program.
import { save } from "./world";

const stored = { advances: 0 };

export async function recordAdvance(id: string): Promise<number> {
  const before = stored.advances;
  await save(id, "advance");
  stored.advances = before + 1;
  return stored.advances;
}

let calls = 0;

export async function countCalls(id: string): Promise<number> {
  await save(id, "call");
  calls += 1;
  return calls;
}

// Reads nothing that other code can change after the await: fine, and the same under any schedule.
export async function recordOnce(id: string, advances: number): Promise<number> {
  const before = advances;
  await save(id, "advance");
  return before + 1;
}
