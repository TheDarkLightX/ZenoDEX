#![no_std]

extern crate alloc;

use tau_state_proof_risc0_shared::{
    ZusdOperationV1, ZusdRecursiveLeafInputV1, ZusdTransitionInputV1,
};

/// The source-pinned Liquity V1 minimum collateral ratio.
pub const ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS: u32 = 11_000;

/// Fail-closed proof-boundary failures. These are not economic transition
/// rejections; they state that a broader reusable helper cannot acquire the
/// requested proof profile's authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZusdProofPolicyError {
    UnsupportedSnapshotVersion,
    VaultDebtOverflow,
    VaultDebtMismatch,
    BalanceSupplyOverflow,
    BalanceSupplyMismatch,
    RecursivePreAppHashMissing,
    RecursiveBaselineMcrMismatch,
}

impl ZusdProofPolicyError {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::UnsupportedSnapshotVersion => "unsupported zusd snapshot version",
            Self::VaultDebtOverflow => "debt overflow",
            Self::VaultDebtMismatch => "zusd total debt mismatch",
            Self::BalanceSupplyOverflow => "zusd balance supply overflow",
            Self::BalanceSupplyMismatch => "zusd balance supply mismatch",
            Self::RecursivePreAppHashMissing => "zUSD recursive leaf requires pre_app_hash",
            Self::RecursiveBaselineMcrMismatch => {
                "zUSD recursive leaf requires baseline MCR 11000"
            }
        }
    }
}

/// Verify the scoped conservation relation required by every zUSD proof,
/// independently of whether the reusable transition helper is invoked directly
/// by a host or through a guest.
pub fn validate_zusd_scoped_snapshot_conservation_v1(
    input: &ZusdTransitionInputV1,
) -> Result<(), ZusdProofPolicyError> {
    if input.pre_state.version != 1 {
        return Err(ZusdProofPolicyError::UnsupportedSnapshotVersion);
    }

    let vault_debt = input.pre_state.vaults.iter().try_fold(0u128, |total, vault| {
        total
            .checked_add(vault.debt_zusd_e8)
            .ok_or(ZusdProofPolicyError::VaultDebtOverflow)
    })?;
    if vault_debt != input.pre_state.total_debt_zusd_e8 {
        return Err(ZusdProofPolicyError::VaultDebtMismatch);
    }

    let balance_supply = input
        .pre_state
        .balances
        .iter()
        .try_fold(0u128, |total, balance| {
            total
                .checked_add(balance.amount_e8)
                .ok_or(ZusdProofPolicyError::BalanceSupplyOverflow)
        })?;
    if balance_supply != input.pre_state.total_debt_zusd_e8 {
        return Err(ZusdProofPolicyError::BalanceSupplyMismatch);
    }

    Ok(())
}

/// Narrow the generic DepositMint proof to the recursive Liquity V1 minimum
/// profile without changing the generic proof's intentionally broader scope.
pub fn validate_zusd_recursive_baseline_input_v1(
    input: &ZusdRecursiveLeafInputV1,
) -> Result<(), ZusdProofPolicyError> {
    validate_zusd_scoped_snapshot_conservation_v1(&input.zusd_input)?;

    if !input.zusd_input.pre_app_hash_present {
        return Err(ZusdProofPolicyError::RecursivePreAppHashMissing);
    }

    let mcr_bps = match &input.zusd_input.operation {
        ZusdOperationV1::DepositMint { mcr_bps, .. } => *mcr_bps,
    };
    if mcr_bps != ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS {
        return Err(ZusdProofPolicyError::RecursiveBaselineMcrMismatch);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    extern crate std;

    use alloc::string::{String, ToString};
    use alloc::vec;
    use tau_state_proof_risc0_shared::{
        OracleBindingV1, ZusdBalanceEntryV1, ZusdOperationV1, ZusdRecursiveLeafInputV1,
        ZusdSnapshotV1, ZusdTransitionInputV1, ZusdVaultEntryV1,
    };

    use super::*;

    const E8: u128 = 100_000_000;

    fn oracle() -> OracleBindingV1 {
        OracleBindingV1 {
            oracle_bridge_id: "verified-oracle".to_string(),
            oracle_bridge_hash: "11".repeat(32),
            price_e8: E8 as i128,
            price_timestamp: 10,
            max_staleness_seconds: 5,
            observed_at: 12,
            pre_price_batch_commitment: "22".repeat(32),
        }
    }

    fn base_input(pre_state: ZusdSnapshotV1, mcr_bps: u32) -> ZusdTransitionInputV1 {
        ZusdTransitionInputV1 {
            state_hash: [7u8; 32],
            chain_id: "devnet".to_string(),
            pre_app_hash_present: true,
            pre_app_hash: [8u8; 32],
            pre_state,
            operation: ZusdOperationV1::DepositMint {
                pubkey: "wallet-a".to_string(),
                collateral_asset: "tAGRS".to_string(),
                deposit_amount_e8: 2_000 * E8,
                mint_amount_e8: 1_000 * E8,
                oracle: oracle(),
                mcr_bps,
                nonce: 1,
            },
            expected_post_app_hash: [9u8; 32],
            risc0_image_id: [1, 2, 3, 4, 5, 6, 7, 8],
        }
    }

    fn recursive_input(pre_state: ZusdSnapshotV1, mcr_bps: u32) -> ZusdRecursiveLeafInputV1 {
        ZusdRecursiveLeafInputV1 {
            chain_id: "devnet".to_string(),
            epoch_id: 1,
            lane_id: "zusd".to_string(),
            risc0_image_id: [1, 2, 3, 4, 5, 6, 7, 8],
            public_policy_hash: [1u8; 32],
            feature_suite_hash: [2u8; 32],
            dependency_lock_hash: [3u8; 32],
            toolchain_lock_hash: [4u8; 32],
            zusd_input: base_input(pre_state, mcr_bps),
        }
    }

    #[test]
    fn scoped_snapshot_rejects_balance_supply_mismatch() {
        let snapshot = ZusdSnapshotV1 {
            version: 1,
            vaults: vec![ZusdVaultEntryV1 {
                pubkey: "wallet-a".to_string(),
                collateral_asset: "tAGRS".to_string(),
                collateral_amount_e8: 2_000 * E8,
                debt_zusd_e8: 1_000 * E8,
                nonce: 1,
            }],
            balances: vec![ZusdBalanceEntryV1 {
                pubkey: "wallet-a".to_string(),
                amount_e8: 999 * E8,
            }],
            total_debt_zusd_e8: 1_000 * E8,
        };

        assert_eq!(
            validate_zusd_scoped_snapshot_conservation_v1(&base_input(snapshot, 10_001)),
            Err(ZusdProofPolicyError::BalanceSupplyMismatch)
        );
    }

    #[test]
    fn generic_proof_policy_keeps_caller_parameterized_mcr_scope() {
        for mcr_bps in [10_001, 10_999, 11_000, 11_001, 15_000] {
            assert_eq!(
                validate_zusd_scoped_snapshot_conservation_v1(&base_input(
                    ZusdSnapshotV1::empty(),
                    mcr_bps,
                )),
                Ok(())
            );
        }
    }

    #[test]
    fn recursive_baseline_accepts_only_exact_mcr() {
        assert_eq!(
            validate_zusd_recursive_baseline_input_v1(&recursive_input(
                ZusdSnapshotV1::empty(),
                ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS,
            )),
            Ok(())
        );
        for mcr_bps in [10_001, 10_999, 11_001, 15_000] {
            assert_eq!(
                validate_zusd_recursive_baseline_input_v1(&recursive_input(
                    ZusdSnapshotV1::empty(),
                    mcr_bps,
                )),
                Err(ZusdProofPolicyError::RecursiveBaselineMcrMismatch)
            );
        }
    }

    #[test]
    fn recursive_baseline_requires_prestate_commitment() {
        let mut input = recursive_input(
            ZusdSnapshotV1::empty(),
            ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS,
        );
        input.zusd_input.pre_app_hash_present = false;
        input.zusd_input.pre_app_hash = [0u8; 32];

        assert_eq!(
            validate_zusd_recursive_baseline_input_v1(&input),
            Err(ZusdProofPolicyError::RecursivePreAppHashMissing)
        );
    }

    #[test]
    fn scoped_balance_sum_overflow_is_typed() {
        let snapshot = ZusdSnapshotV1 {
            version: 1,
            vaults: vec![],
            balances: vec![
                ZusdBalanceEntryV1 {
                    pubkey: "wallet-a".to_string(),
                    amount_e8: u128::MAX,
                },
                ZusdBalanceEntryV1 {
                    pubkey: "wallet-b".to_string(),
                    amount_e8: 1,
                },
            ],
            total_debt_zusd_e8: 0,
        };

        assert_eq!(
            validate_zusd_scoped_snapshot_conservation_v1(&base_input(snapshot, 11_000)),
            Err(ZusdProofPolicyError::BalanceSupplyOverflow)
        );
    }

    #[test]
    fn error_text_matches_stable_boundary_reason() {
        assert_eq!(
            ZusdProofPolicyError::BalanceSupplyMismatch.as_str(),
            "zusd balance supply mismatch"
        );
    }

    #[allow(dead_code)]
    fn _string_type_is_available_for_no_std_test_build() -> String {
        String::new()
    }
}
