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
