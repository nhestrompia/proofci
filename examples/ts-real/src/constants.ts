/**
 * Divisor for the CCA price-tick granularity. Distinct from the pool tick spacing and not derivable
 * from the fee tier. v1 default: 1% of the floor price (the canonical CCA configurator value).
 */
export const AUCTION_TICK_DIVISOR = 100n
