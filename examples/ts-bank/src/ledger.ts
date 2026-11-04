export interface Accounts {
  from: number;
  to: number;
}

const BASIS_POINTS = 10_000;
const MAX_FEE = 500;

/** A percentage fee, rounded down and capped. */
export function calculateFee(amount: number, rateBps: number): number {
  return Math.min(Math.floor(amount * rateBps / BASIS_POINTS), MAX_FEE);
}

/** Moves `amount` between accounts, or returns null if the balance is too low. */
export function transfer(accounts: Accounts, amount: number): Accounts | null {
  if (amount <= 0 || amount > accounts.from) return null;
  return { from: accounts.from - amount, to: accounts.to + amount };
}

/** The total of a list of amounts. */
export function sumAmounts(amounts: readonly number[]): number {
  let total = 0;
  for (const amount of amounts) {
    total += amount;
  }
  return total;
}
