/// Withdraws `amount` from `balance`; `None` if the balance is too small.
pub fn withdraw(balance: u64, amount: u64) -> Option<u64> {
    if amount > balance {
        None
    } else {
        Some(balance - amount)
    }
}
