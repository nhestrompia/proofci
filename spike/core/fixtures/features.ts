// Small programs that exercise what the typed path can't: closures, shared captured
// state, array callbacks, classes with overriding, and recursion over shared data.

export function counterTwice(start: number): number[] {
  let n = start;
  const bump = () => { n = n + 1; return n; };
  const out: number[] = [];
  out.push(bump());
  out.push(bump());
  n = n + 10;
  out.push(bump());
  return out;
}

/** Each closure must keep its own `x`, even though they share a loop. */
export function loopCaptures(xs: number[]): number {
  const fs: (() => number)[] = [];
  for (const x of xs) {
    fs.push(() => x * 2);
  }
  let total = 0;
  for (const f of fs) {
    total = total + f();
  }
  return total;
}

export function scaled(xs: number[], k: number): number[] {
  return xs.map(x => x * k);
}

export function indexed(xs: number[]): number[] {
  return xs.map((x, i) => x + i);
}

export function positives(xs: number[]): number[] {
  return xs.filter(x => x > 0);
}

export function total(xs: number[]): number {
  return xs.reduce((acc: number, x) => acc + x, 0);
}

export function anyOver(xs: number[], limit: number): boolean {
  return xs.some(x => x > limit);
}

export function firstNegative(xs: number[]): number | null {
  for (const x of xs) {
    if (x < 0) return x;
  }
  return null;
}

export function positivesLoop(xs: number[]): number[] {
  const out: number[] = [];
  for (const x of xs) {
    if (x > 0) out.push(x);
  }
  return out;
}

export function sumPlusOne(xs: number[]): number {
  return sumAll(xs) + 1;
}

function sumAll(xs: number[]): number {
  let t = 0;
  for (const x of xs) {
    t = t + x;
  }
  return t;
}

class Shape {
  size: number;
  constructor(size: number) {
    this.size = size;
  }
  area(): number {
    return this.size * this.size;
  }
  describe(): number {
    return this.area() + 1;
  }
}

class Doubled extends Shape {
  constructor(size: number) {
    super(size * 2);
  }
  area(): number {
    return super.area() + 100;
  }
}

/** `describe` lives on Shape but must call Doubled's `area`. */
export function dispatch(n: number): number {
  const a = new Shape(n);
  const b = new Doubled(n);
  return a.describe() * 1000 + b.describe();
}

export function growBoth(n: number): number {
  const s = new Shape(n);
  const same = s;
  same.size = same.size + 1;
  return s.area();
}

export type Tree = { value: number; left: Tree | null; right: Tree | null };

export function treeSum(t: Tree | null): number {
  if (t === null) return 0;
  return t.value + treeSum(t.left) + treeSum(t.right);
}
