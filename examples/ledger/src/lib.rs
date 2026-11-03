//! A tiny ledger whose guarantees are checked by ProofCI.

/// Basis points in 100%.
pub const BPS_DENOMINATOR: u64 = 10_000;

/// Fee charged on `amount` at `fee_bps` basis points, rounded down.
/// Rates above 100% are capped at 100%.
pub fn calculate_fee(amount: u64, fee_bps: u64) -> u64 {
    let bps = if fee_bps > BPS_DENOMINATOR { BPS_DENOMINATOR } else { fee_bps };
    amount / BPS_DENOMINATOR * bps + amount % BPS_DENOMINATOR * bps / BPS_DENOMINATOR
}

pub struct Accounts {
    pub from: u64,
    pub to: u64,
}

/// Moves `amount` from `from` to `to`. Returns `None` when the sender cannot
/// cover the amount or the receiver's balance would overflow.
pub fn transfer(accounts: Accounts, amount: u64) -> Option<Accounts> {
    if amount > accounts.from {
        return None;
    }
    if accounts.to > u64::MAX - amount {
        return None;
    }
    Some(Accounts { from: accounts.from - amount, to: accounts.to + amount })
}
