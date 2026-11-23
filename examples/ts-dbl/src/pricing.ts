/** The line total for a price, a percent discount and a percent tax, rounded to cents. */
export function totalWithTax(price: number, quantity: number, discountPct: number, taxPct: number): number {
  const subtotal = price * quantity;
  const discounted = subtotal * (1 - discountPct / 100);
  const withTax = discounted * (1 + taxPct / 100);
  return Math.round(withTax * 100) / 100;
}

/** The amount left after taking `bucket`-sized chunks out of `price`. */
export function leftover(price: number, bucket: number): number {
  return price % bucket;
}

/** Which way a rate moves a price: up, down, or not at all. */
export function effect(rate: number): number {
  return Math.sign(rate * rate - 1);
}
