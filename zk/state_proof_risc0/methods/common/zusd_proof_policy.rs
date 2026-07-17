use tau_state_proof_risc0_shared::{
    ZusdOperationV1, ZusdRecursiveLeafInputV1, ZusdTransitionInputV1,
};

/// The source-pinned Liquity V1 minimum collateral ratio.
pub const ZUSD_LIQUITY_V1_MINIMUM_MCR_BPS: u32 = 11_000;

/// Fail-closed proof-boundary failures. These state that a broader reusable
/// transition cannot acquire the requested proof profile's authority.
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

/// Verify the scoped conservation relation required by every zUSD proof.
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
