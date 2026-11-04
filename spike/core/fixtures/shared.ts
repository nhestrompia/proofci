export type Account = { balance: number };

/** Safe when both accounts are the same object: each line reads the current balance. */
export function moveMoney(from: Account, to: Account, amount: number): void {
  from.balance = from.balance - amount;
  to.balance = to.balance + amount;
}

/** Looks equivalent, but reads both balances first, so sharing one account creates money. */
export function moveMoneyStale(from: Account, to: Account, amount: number): void {
  const a = from.balance;
  const b = to.balance;
  from.balance = a - amount;
  to.balance = b + amount;
}
