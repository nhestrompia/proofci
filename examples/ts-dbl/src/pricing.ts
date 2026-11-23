/** The line total for a price, a percent discount and a percent tax, rounded to cents. */
export function totalWithTax(price: number, quantity: number, discountPct: number, taxPct: number): number {
  const subtotal = price * quantity;
  const discounted = subtotal * (1 - discountPct / 100);
  const withTax = discounted * (1 + taxPct / 100);
  return Math.round(withTax * 100) / 100;
}

/** Each share when `total` is split `parts` ways after dropping the remainder. */
export function perHead(total: number, parts: number): number {
  return (total - (total % parts)) / parts;
}

/** Which way a rate moves a price: up, down, or not at all. */
export function effect(rate: number): number {
  return Math.sign(rate * rate - 1);
}

// An integer helper double code cannot call: it is registered safe-integer, so
// the computed constant below lifts through `Js.Dbl.ofNumNe` — which refuses
// `0`, where JS may have computed `-0`.
export function clampInt(n: number): number {
  return n < 0 ? 0 : n;
}
const freeUnits = clampInt(0);

// `freeUnits` is `0`: the model lift refuses it (JS may have `-0`), so this
// stays `tested` on every input — never proved, never a Node disagreement.
export function bonus(price: number): number {
  return price + freeUnits + 0.5;
}

// A shelf label: clamp a possibly-bad price into [min, 100] and rebuild it —
// exercises the remaining double operations on a path real inputs reach.
export function shelfPrice(price: number, min: number): number {
  if (!Number.isFinite(price) || Number.isNaN(price) || price < 0) return min;
  const clipped = Math.min(Math.max(Math.abs(price), min), 100);
  const whole = Math.trunc(clipped);
  const frac = clipped - whole;
  const cents = Math.ceil(frac * 100) % 100;
  let rebuilt = whole + cents / 100;
  if (clipped === whole) rebuilt = Math.min(rebuilt, min);
  if (frac <= 0.05) rebuilt += Math.floor(-frac * 10) / 10;
  return Number.isInteger(min) ? rebuilt : Math.floor(rebuilt);
}
