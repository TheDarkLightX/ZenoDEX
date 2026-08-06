#![no_std]

/// Maximum admitted balance and transfer amount in the RC3 balance domain.
pub const MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1: u128 = (1_u128 << 112) - 1;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum AssetTransferArithmeticRejectV1 {
    InsufficientBalance,
    BalanceOverflow,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AssetTransferPostBalancesV1 {
    source_atoms: u128,
    destination_atoms: u128,
}

impl AssetTransferPostBalancesV1 {
    pub const fn source_atoms(self) -> u128 {
        self.source_atoms
    }

    pub const fn destination_atoms(self) -> u128 {
        self.destination_atoms
    }
}

/// Total transfer arithmetic over all `u128` inputs.
///
/// Callers own identifier, amount-domain, and state-shape validation. The
/// insufficient-balance guard has stable precedence over recipient overflow.
pub fn settle_transfer_balances_v1(
    source_atoms: u128,
    destination_atoms: u128,
    amount_atoms: u128,
) -> Result<AssetTransferPostBalancesV1, AssetTransferArithmeticRejectV1> {
    if source_atoms < amount_atoms {
        return Err(AssetTransferArithmeticRejectV1::InsufficientBalance);
    }
    let destination_atoms = destination_atoms
        .checked_add(amount_atoms)
        .filter(|value| *value <= MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1)
        .ok_or(AssetTransferArithmeticRejectV1::BalanceOverflow)?;
    Ok(AssetTransferPostBalancesV1 {
        source_atoms: source_atoms - amount_atoms,
        destination_atoms,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn one_atom_moves_exactly_and_conserves() {
        let post = settle_transfer_balances_v1(2, 3, 1).unwrap();
        assert_eq!(post.source_atoms(), 1);
        assert_eq!(post.destination_atoms(), 4);
        assert_eq!(post.source_atoms() + post.destination_atoms(), 5);
    }

    #[test]
    fn insufficient_precedes_destination_overflow() {
        assert_eq!(
            settle_transfer_balances_v1(0, u128::MAX, 1),
            Err(AssetTransferArithmeticRejectV1::InsufficientBalance)
        );
    }

    #[test]
    fn admitted_maximum_bound_is_exact() {
        let post = settle_transfer_balances_v1(
            MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1,
            0,
            MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1,
        )
        .unwrap();
        assert_eq!(post.source_atoms(), 0);
        assert_eq!(
            post.destination_atoms(),
            MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1
        );
        assert_eq!(
            settle_transfer_balances_v1(1, MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1, 1),
            Err(AssetTransferArithmeticRejectV1::BalanceOverflow)
        );
    }
}

#[cfg(kani)]
mod kani_contracts {
    use super::*;

    fn admitted_balance() -> u128 {
        let value = kani::any();
        kani::assume(value <= MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1);
        value
    }

    fn admitted_amount() -> u128 {
        let value = kani::any();
        kani::assume(value >= 1 && value <= MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1);
        value
    }

    #[kani::proof]
    fn transition_is_total_for_every_u128_input() {
        let _ = settle_transfer_balances_v1(kani::any(), kani::any(), kani::any());
    }

    #[kani::proof]
    fn accepted_transition_moves_exactly_and_conserves() {
        let source = admitted_balance();
        let destination = admitted_balance();
        let amount = admitted_amount();
        if let Ok(post) = settle_transfer_balances_v1(source, destination, amount) {
            assert_eq!(post.source_atoms(), source - amount);
            assert_eq!(post.destination_atoms(), destination + amount);
            assert_eq!(
                post.source_atoms() + post.destination_atoms(),
                source + destination
            );
            assert!(post.destination_atoms() <= MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1);
        }
    }

    #[kani::proof]
    fn rejection_partition_and_precedence_are_exact() {
        let source = admitted_balance();
        let destination = admitted_balance();
        let amount = admitted_amount();
        match settle_transfer_balances_v1(source, destination, amount) {
            Ok(_) => {
                assert!(source >= amount);
                assert!(destination + amount <= MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1);
            }
            Err(AssetTransferArithmeticRejectV1::InsufficientBalance) => {
                assert!(source < amount);
            }
            Err(AssetTransferArithmeticRejectV1::BalanceOverflow) => {
                assert!(source >= amount);
                assert!(destination + amount > MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1);
            }
        }
    }
}
