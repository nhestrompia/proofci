import { AUCTION_TICK_DIVISOR } from '../constants'

/** Derives the CCA price-tick granularity from the floor price (minimum 1). */
export function deriveAuctionTickSpacing(floorPriceX96: bigint): bigint {
  const tickSpacing = floorPriceX96 / AUCTION_TICK_DIVISOR
  return tickSpacing > 0n ? tickSpacing : 1n
}

/**
 * Derives the CCA tick spacing AND snaps the floor price DOWN to the nearest tick boundary. The CCA
 * constructor seeds the floor as the first tick and requires `floorPrice % tickSpacing == 0`
 * (otherwise it reverts `TickPriceNotAtBoundary`). The on-chain floor drifts at most one tick below
 * the requested price (< 1/AUCTION_TICK_DIVISOR).
 */
export function deriveAuctionPricing(rawFloorPriceX96: bigint): { floorPriceX96: bigint; tickSpacing: bigint } {
  const tickSpacing = deriveAuctionTickSpacing(rawFloorPriceX96)
  return { floorPriceX96: rawFloorPriceX96 - (rawFloorPriceX96 % tickSpacing), tickSpacing }
}
