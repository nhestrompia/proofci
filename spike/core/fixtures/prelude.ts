// Array methods written in TypeScript, then lowered like any other code. The library
// model is Core, so it needs no separate semantics.
export function jsMap<T, U>(xs: T[], f: (x: T, i: number, a: T[]) => U): U[] {
  const out: U[] = [];
  let i = 0;
  for (const x of xs) {
    out.push(f(x, i, xs));
    i = i + 1;
  }
  return out;
}

export function jsFilter<T>(xs: T[], f: (x: T, i: number, a: T[]) => boolean): T[] {
  const out: T[] = [];
  let i = 0;
  for (const x of xs) {
    if (f(x, i, xs)) out.push(x);
    i = i + 1;
  }
  return out;
}

export function jsReduce<T, U>(xs: T[], f: (acc: U, x: T, i: number, a: T[]) => U, init: U): U {
  let acc = init;
  let i = 0;
  for (const x of xs) {
    acc = f(acc, x, i, xs);
    i = i + 1;
  }
  return acc;
}

export function jsSome<T>(xs: T[], f: (x: T, i: number, a: T[]) => boolean): boolean {
  let i = 0;
  for (const x of xs) {
    if (f(x, i, xs)) return true;
    i = i + 1;
  }
  return false;
}
