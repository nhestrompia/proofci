export type Account = { balance: number; log: number[] };

/** Reads, waits, writes: a second caller can slip in between. */
export async function withdrawStale(a: Account, amount: number): Promise<void> {
  const b = a.balance;
  a.log.push(amount);
  await null;
  a.balance = b - amount;
  a.log.push(-amount);
}

/** Reads and writes in one turn, so nothing can come between them. */
export async function withdrawSafe(a: Account, amount: number): Promise<void> {
  a.log.push(amount);
  await null;
  a.balance = a.balance - amount;
  a.log.push(-amount);
}

export async function twoWaits(a: Account, amount: number): Promise<void> {
  a.log.push(amount);
  await null;
  a.log.push(amount + 1);
  await null;
  a.log.push(amount + 2);
}
