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
