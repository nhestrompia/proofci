// Forms the corpus picks don't reach, for the comparison with Node.

/** A closure that assigns the variables it captures, and a result that may be the argument itself. */
export function colorIndexes(items: { empty: boolean; color: string }[]): { empty: boolean; color: string }[] {
  let index = 0;
  let changed = false;
  const out = items.map((item) => {
    const color = item.empty ? "none" : `c${index}`;
    if (!item.empty) index += 1;
    if (item.color === color) return item;
    changed = true;
    return { ...item, color };
  });
  return changed ? out : items;
}

export class Counter {
  n = 0;
  bump(by: number): number {
    this.n += by;
    return this.n;
  }
}

/** Two counters that may be the same object. */
export function bumpBoth(a: Counter, b: Counter): number {
  a.bump(1);
  b.bump(1);
  return a.n;
}

/** Library calls the bridge relates: `padStart` and `findIndex`. */
export function padCode(s: string): string {
  return s.padStart(4, "0");
}

export function firstAbove(xs: number[], k: number): number {
  return xs.findIndex((x) => x > k);
}

/** `for (;;)` over indices, and `while` with a counter. */
export function sumIndexed(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    s += xs[i];
  }
  return s;
}

export function halvings(n: number): number {
  let k = 0;
  let m = n;
  while (m > 1) {
    m = Math.floor(m / 2);
    k++;
  }
  return k;
}

export function lastOf(xs: number[]): number {
  return xs.at(-1) ?? 0;
}

export function lastCh(s: string): string {
  return s.at(-1) ?? "";
}

export function ruler(n: number): string {
  return "-".repeat(n % 8);
}

export function padRight(s: string, n: number): string {
  return s.padEnd(n % 12, ".");
}

export function flatten(rows: number[][]): number[] {
  return rows.flat();
}
