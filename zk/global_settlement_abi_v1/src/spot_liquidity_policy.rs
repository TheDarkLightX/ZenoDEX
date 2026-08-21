use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};

pub const G1_SPOT_LP_CANDIDATE_SCHEMA_V1: &str = "zenodex/g1-spot-lp-candidate/v1";
pub const G1_SPOT_LP_SWAP_FEE_BPS_V1: u16 = 30;
pub const G1_SPOT_LP_PROTOCOL_FEE_SHARE_BPS_V1: u16 = 0;
pub const G1_SPOT_LP_MAX_POOL_ATOMS_V1: u128 = (1u128 << 64) - 1;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum SpotFeeRoundingV1 {
    CEIL_GROSS_INPUT,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum SpotOutputRoundingV1 {
    FLOOR_POOL_OUTPUT,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum SpotFeeOwnerV1 {
    CURRENT_LP_CLAIMANTS_VIA_POOL_RESERVES,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum PoolReserveIngressV1 {
    POOL_KERNEL_ONLY,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum InitialLpMintV1 {
    FLOOR_SQRT_PRODUCT_NO_PERMANENT_LOCK,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AdditionalLpMintV1 {
    MAX_NON_DILUTING_SHARES_CEIL_ASSET_USE_REFUND_EXCESS,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum LpWithdrawalRuleV1 {
    PRO_RATA_FLOOR_FINAL_BURN_DRAINS_AND_CLOSES,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum PoolResidueOwnerV1 {
    REMAINING_LP_CLAIMANTS_THEN_FINAL_BURNER,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum G1SpotLpSelectionV1 {
    CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct G1SpotLpPolicyCandidateV1 {
    pub schema: String,
    pub asset_authority_profile_root: RootV1,
    pub swap_fee_bps: u16,
    pub protocol_fee_share_bps: u16,
    pub fee_rounding: SpotFeeRoundingV1,
    pub output_rounding: SpotOutputRoundingV1,
    pub fee_owner: SpotFeeOwnerV1,
    pub reserve_ingress: PoolReserveIngressV1,
    pub initial_lp_mint: InitialLpMintV1,
    pub additional_lp_mint: AdditionalLpMintV1,
    pub withdrawal: LpWithdrawalRuleV1,
    pub residue_owner: PoolResidueOwnerV1,
    pub max_pool_atoms: u128,
    pub selection: G1SpotLpSelectionV1,
}

impl G1SpotLpPolicyCandidateV1 {
    /// Validates the exact inactive G1 Spot/LP candidate.
    ///
    /// This check supplies no route, transition, proof, profile activation, or
    /// publication authority.
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != G1_SPOT_LP_CANDIDATE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.asset_authority_profile_root
            .validate("Spot/LP asset-authority profile root", false)?;
        let expected =
            g1_testnet_spot_lp_policy_candidate_v1(self.asset_authority_profile_root.clone());
        if self != &expected {
            return Err(AbiErrorV1::InvalidBinding(
                "G1 testnet Spot/LP policy candidate",
            ));
        }
        Ok(())
    }

    pub fn profile_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("g1-spot-lp-candidate-v1", self)
    }

    /// Validates this candidate against the predecessor selected by its caller.
    ///
    /// Structural validation alone does not select an asset-authority profile.
    /// A future route or release boundary must supply its expected predecessor.
    pub fn validate_for_asset_authority_root(
        &self,
        expected_asset_authority_profile_root: &RootV1,
    ) -> AbiResultV1<()> {
        self.validate()?;
        if &self.asset_authority_profile_root != expected_asset_authority_profile_root {
            return Err(AbiErrorV1::InvalidBinding(
                "G1 Spot/LP asset-authority predecessor",
            ));
        }
        Ok(())
    }
}

/// Constructs the only inactive G1 Spot/LP candidate accepted by V1.
pub fn g1_testnet_spot_lp_policy_candidate_v1(
    asset_authority_profile_root: RootV1,
) -> G1SpotLpPolicyCandidateV1 {
    G1SpotLpPolicyCandidateV1 {
        schema: G1_SPOT_LP_CANDIDATE_SCHEMA_V1.to_owned(),
        asset_authority_profile_root,
        swap_fee_bps: G1_SPOT_LP_SWAP_FEE_BPS_V1,
        protocol_fee_share_bps: G1_SPOT_LP_PROTOCOL_FEE_SHARE_BPS_V1,
        fee_rounding: SpotFeeRoundingV1::CEIL_GROSS_INPUT,
        output_rounding: SpotOutputRoundingV1::FLOOR_POOL_OUTPUT,
        fee_owner: SpotFeeOwnerV1::CURRENT_LP_CLAIMANTS_VIA_POOL_RESERVES,
        reserve_ingress: PoolReserveIngressV1::POOL_KERNEL_ONLY,
        initial_lp_mint: InitialLpMintV1::FLOOR_SQRT_PRODUCT_NO_PERMANENT_LOCK,
        additional_lp_mint:
            AdditionalLpMintV1::MAX_NON_DILUTING_SHARES_CEIL_ASSET_USE_REFUND_EXCESS,
        withdrawal: LpWithdrawalRuleV1::PRO_RATA_FLOOR_FINAL_BURN_DRAINS_AND_CLOSES,
        residue_owner: PoolResidueOwnerV1::REMAINING_LP_CLAIMANTS_THEN_FINAL_BURNER,
        max_pool_atoms: G1_SPOT_LP_MAX_POOL_ATOMS_V1,
        selection: G1SpotLpSelectionV1::CANDIDATE_UNSELECTED_USER_CONFIRMATION_REQUIRED,
    }
}
