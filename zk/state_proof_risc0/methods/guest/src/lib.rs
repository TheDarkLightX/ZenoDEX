#![no_std]

use tau_state_proof_risc0_shared::{ZusdOperationV1, ZusdTransitionInputV1};

/// The source-pinned Liquity V1 minimum collateral ratio.
pub const ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS: u32 = 11_000;

/// Fail-closed reasons produced before the zUSD transition can enter the guest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ZusdMinimumAdmissionError {
    UnsupportedSnapshotVersion,
    MissingPreAppHash,
    McrMismatch,
    VaultDebtOverflow,
    VaultDebtMismatch,
    BalanceSupplyOverflow,
    BalanceSupplyMismatch,
}

/// Validate the invariants that distinguish the authoritative minimum-profile
/// proof from the older, caller-parameterized arithmetic helper.
///
/// This function is pure and deterministic.  It deliberately repeats the
/// snapshot conservation checks at the proof-admission boundary so a future
/// relaxation in a lower-level helper cannot silently broaden guest authority.
pub fn validate_zusd_minimum_profile_input_v1(
    input: &ZusdTransitionInputV1,
) -> Result<(), ZusdMinimumAdmissionError> {
    if input.pre_state.version != 1 {
        return Err(ZusdMinimumAdmissionError::UnsupportedSnapshotVersion);
    }
    if !input.pre_app_hash_present {
        return Err(ZusdMinimumAdmissionError::MissingPreAppHash);
    }

    let mcr_bps = match &input.operation {
        ZusdOperationV1::DepositMint { mcr_bps, .. } => *mcr_bps,
    };
    if mcr_bps != ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS {
        return Err(ZusdMinimumAdmissionError::McrMismatch);
    }

    let vault_debt = input.pre_state.vaults.iter().try_fold(0u128, |total, vault| {
        total
            .checked_add(vault.debt_zusd_e8)
            .ok_or(ZusdMinimumAdmissionError::VaultDebtOverflow)
    })?;
    if vault_debt != input.pre_state.total_debt_zusd_e8 {
        return Err(ZusdMinimumAdmissionError::VaultDebtMismatch);
    }

    let balance_supply = input
        .pre_state
        .balances
        .iter()
        .try_fold(0u128, |total, balance| {
            total
                .checked_add(balance.amount_e8)
                .ok_or(ZusdMinimumAdmissionError::BalanceSupplyOverflow)
        })?;
    if balance_supply != input.pre_state.total_debt_zusd_e8 {
        return Err(ZusdMinimumAdmissionError::BalanceSupplyMismatch);
    }

    Ok(())
}
