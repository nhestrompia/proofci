// Array methods written in TypeScript, then lowered like any other code. They follow
// the spec's order of steps: the length is read once, and each index is read when
// reached. Core has no holes, so a slot that disappeared stops the model (`__stuck`).
declare function __stuck(): never;

function mapFrom<T, U>(xs: T[], f: (x: T, i: number, a: T[]) => U, i: number, n: number, out: U[]): U[] {
  if (i === n) return out;
  if (i >= xs.length) __stuck();
  out.push(f(xs[i], i, xs));
  return mapFrom(xs, f, i + 1, n, out);
}

export function jsMap<T, U>(xs: T[], f: (x: T, i: number, a: T[]) => U): U[] {
  const out: U[] = [];
  return mapFrom(xs, f, 0, xs.length, out);
}

function filterFrom<T>(xs: T[], f: (x: T, i: number, a: T[]) => boolean, i: number, n: number, out: T[]): T[] {
  if (i === n) return out;
  if (i >= xs.length) __stuck();
  const x = xs[i];
  if (f(x, i, xs)) out.push(x);
  return filterFrom(xs, f, i + 1, n, out);
}

export function jsFilter<T>(xs: T[], f: (x: T, i: number, a: T[]) => boolean): T[] {
  const out: T[] = [];
  return filterFrom(xs, f, 0, xs.length, out);
}

function reduceFrom<T, U>(xs: T[], f: (acc: U, x: T, i: number, a: T[]) => U, i: number, n: number, acc: U): U {
  if (i === n) return acc;
  if (i >= xs.length) __stuck();
  return reduceFrom(xs, f, i + 1, n, f(acc, xs[i], i, xs));
}

export function jsReduce<T, U>(xs: T[], f: (acc: U, x: T, i: number, a: T[]) => U, init: U): U {
  return reduceFrom(xs, f, 0, xs.length, init);
}

function someFrom<T>(xs: T[], f: (x: T, i: number, a: T[]) => boolean, i: number, n: number): boolean {
  if (i === n) return false;
  if (i >= xs.length) __stuck();
  if (f(xs[i], i, xs)) return true;
  return someFrom(xs, f, i + 1, n);
}

export function jsSome<T>(xs: T[], f: (x: T, i: number, a: T[]) => boolean): boolean {
  return someFrom(xs, f, 0, xs.length);
}
