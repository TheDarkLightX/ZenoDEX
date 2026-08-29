use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_schema_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1,
    GLOBAL_SETTLEMENT_ABI_V1,
};
use crate::effects::GlobalEconomicEffectPlanV1;

pub const BASIS_POINTS_DENOMINATOR_V1: u16 = 10_000;
pub const PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1: &str = "protocol_fee_allocation";
pub const ZDEX_FEE_ALLOCATION_POLICY_KIND_V1: &str = "zdex_fee_allocation";
pub const FEE_ALLOCATION_OUTPUT_ROLE_V1: &str = "FEE_ALLOCATION_OUTPUT";
pub const FEE_ALLOCATION_OUTPUT_PORT_V1: &str = "ZDEX_FEE_ALLOCATION_OUTPUT_V1";
pub const FEE_INGRESS_PRINCIPAL_V1: &str = "protocol:fee-ingress";
pub const FEE_BUYBACK_PRINCIPAL_V1: &str = "protocol-fee-buyback-reserve";
pub const FEE_INGRESS_CONTROL_DOMAIN_V1: &str = "zenoledger:protocol-fee-ingress";

pub fn zdex_fee_allocation_port_schema_root_v1() -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct PortSchema<'a> {
        schema: &'static str,
        port: &'a str,
    }
    hash_global_v1(
        "zdex-fee-allocation-port-schema-v1",
        &PortSchema {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            port: FEE_ALLOCATION_OUTPUT_PORT_V1,
        },
    )
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXFeeDestinationV1 {
    BUYBACK,
    QUALIFIED_HOST_POOL,
    TREASURY,
    PROOF_REWARDS,
    COVER_RESERVE,
    LP_REBATES,
}

pub const ZDEX_FEE_DESTINATIONS_V1: [ZDEXFeeDestinationV1; 6] = [
    ZDEXFeeDestinationV1::BUYBACK,
    ZDEXFeeDestinationV1::QUALIFIED_HOST_POOL,
    ZDEXFeeDestinationV1::TREASURY,
    ZDEXFeeDestinationV1::PROOF_REWARDS,
    ZDEXFeeDestinationV1::COVER_RESERVE,
    ZDEXFeeDestinationV1::LP_REBATES,
];

pub(crate) fn destination_principal_v1(destination: ZDEXFeeDestinationV1) -> &'static str {
    match destination {
        ZDEXFeeDestinationV1::BUYBACK => FEE_BUYBACK_PRINCIPAL_V1,
        ZDEXFeeDestinationV1::QUALIFIED_HOST_POOL => "protocol:fee-qualified-host-pool",
        ZDEXFeeDestinationV1::TREASURY => "protocol:fee-treasury",
        ZDEXFeeDestinationV1::PROOF_REWARDS => "protocol:fee-proof-rewards",
        ZDEXFeeDestinationV1::COVER_RESERVE => "protocol:fee-cover-reserve",
        ZDEXFeeDestinationV1::LP_REBATES => "protocol:fee-lp-rebates",
    }
}

pub(crate) fn destination_control_domain_v1(destination: ZDEXFeeDestinationV1) -> &'static str {
    match destination {
        ZDEXFeeDestinationV1::BUYBACK => "zenoledger:protocol-buyback",
        ZDEXFeeDestinationV1::QUALIFIED_HOST_POOL => "zenoledger:qualified-host-pool",
        ZDEXFeeDestinationV1::TREASURY => "zenoledger:protocol-treasury",
        ZDEXFeeDestinationV1::PROOF_REWARDS => "zenoledger:proof-rewards",
        ZDEXFeeDestinationV1::COVER_RESERVE => "zenoledger:cover-reserve",
        ZDEXFeeDestinationV1::LP_REBATES => "zenoledger:lp-rebates",
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeShareV1 {
    pub destination: ZDEXFeeDestinationV1,
    pub share_bps: u16,
}

impl ZDEXFeeShareV1 {
    fn validate(&self) -> AbiResultV1<()> {
        if self.share_bps > BASIS_POINTS_DENOMINATOR_V1 {
            return Err(AbiErrorV1::InvalidBounds("ZDEX fee share"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeAllocationPolicyV1 {
    pub shares: Vec<ZDEXFeeShareV1>,
}

impl ZDEXFeeAllocationPolicyV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.shares.len() != ZDEX_FEE_DESTINATIONS_V1.len() {
            return Err(AbiErrorV1::InvalidBounds("ZDEX fee destination count"));
        }
        let mut total = 0_u32;
        for (share, expected_destination) in self.shares.iter().zip(ZDEX_FEE_DESTINATIONS_V1.iter())
        {
            share.validate()?;
            if share.destination != *expected_destination {
                return Err(AbiErrorV1::InvalidOrder("ZDEX fee destinations"));
            }
            total += u32::from(share.share_bps);
        }
        if total > u32::from(BASIS_POINTS_DENOMINATOR_V1) {
            return Err(AbiErrorV1::InvalidBounds("ZDEX assigned fee shares"));
        }
        Ok(())
    }

    pub fn assigned_basis_points(&self) -> u32 {
        self.shares
            .iter()
            .map(|share| u32::from(share.share_bps))
            .sum()
    }

    pub fn unassigned_basis_points(&self) -> AbiResultV1<u16> {
        self.validate()?;
        let unassigned = u32::from(BASIS_POINTS_DENOMINATOR_V1)
            .checked_sub(self.assigned_basis_points())
            .ok_or(AbiErrorV1::InvalidBounds("ZDEX unassigned fee shares"))?;
        u16::try_from(unassigned)
            .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX unassigned fee shares"))
    }

    pub fn policy_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-fee-allocation-policy-v1", self)
    }
}

pub fn candidate_zdex_fee_allocation_policy_v1() -> ZDEXFeeAllocationPolicyV1 {
    ZDEXFeeAllocationPolicyV1 {
        shares: ZDEX_FEE_DESTINATIONS_V1
            .into_iter()
            .zip([2_000, 0, 3_000, 1_000, 1_000, 500])
            .map(|(destination, share_bps)| ZDEXFeeShareV1 {
                destination,
                share_bps,
            })
            .collect(),
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeDestinationAmountV1 {
    pub destination: ZDEXFeeDestinationV1,
    pub allocation_atoms: u128,
}

fn validate_destination_amounts_v1(values: &[ZDEXFeeDestinationAmountV1]) -> AbiResultV1<()> {
    if values.len() != ZDEX_FEE_DESTINATIONS_V1.len() {
        return Err(AbiErrorV1::InvalidBounds("ZDEX fee amount count"));
    }
    for (value, expected_destination) in values.iter().zip(ZDEX_FEE_DESTINATIONS_V1.iter()) {
        if value.destination != *expected_destination {
            return Err(AbiErrorV1::InvalidOrder("ZDEX fee amount destinations"));
        }
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeStateV1 {
    pub fee_asset_id: RootV1,
    pub policy_root: RootV1,
    pub fee_ingress_atoms: u128,
    pub unallocated_reserve_atoms: u128,
    pub destination_balances: Vec<ZDEXFeeDestinationAmountV1>,
    pub owned_and_custodied_atoms: u128,
    pub supply_atoms: u128,
}

impl ZDEXFeeStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.fee_asset_id.validate("ZDEX fee asset id", false)?;
        self.policy_root
            .validate("ZDEX fee state policy root", false)?;
        validate_destination_amounts_v1(&self.destination_balances)?;
        if self.selected_balance_atoms()? > self.owned_and_custodied_atoms {
            return Err(AbiErrorV1::Conservation(
                "ZDEX selected fee balances exceed owned amount",
            ));
        }
        Ok(())
    }

    pub fn selected_balance_atoms(&self) -> AbiResultV1<u128> {
        self.destination_balances.iter().try_fold(
            self.fee_ingress_atoms
                .checked_add(self.unallocated_reserve_atoms)
                .ok_or(AbiErrorV1::Conservation(
                    "ZDEX selected fee balance overflow",
                ))?,
            |total, value| {
                total
                    .checked_add(value.allocation_atoms)
                    .ok_or(AbiErrorV1::Conservation(
                        "ZDEX selected fee balance overflow",
                    ))
            },
        )
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-fee-allocation-state-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeAllocationContextV1 {
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub allocation_route_release_id: RootV1,
    pub authorized_buyback_route_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub policy_root: RootV1,
}

impl ZDEXFeeAllocationContextV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "ZDEX fee allocation chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.allocation_route_release_id,
            &self.authorized_buyback_route_release_id,
            &self.tokenomics_module_release_id,
            &self.command_occurrence_id,
            &self.policy_root,
        ] {
            root.validate("ZDEX fee allocation root", false)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeAllocationCommandV1 {
    pub fee_charged_atoms: u128,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeAllocationOccurrenceV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub allocation_route_release_id: RootV1,
    pub authorized_buyback_route_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub policy_root: RootV1,
    pub fee_asset_id: RootV1,
    pub fee_charged_atoms: u128,
    pub allocations: Vec<ZDEXFeeDestinationAmountV1>,
    pub carried_residue_atoms: u128,
    pub pre_lane_root: RootV1,
    pub post_lane_root: RootV1,
    pub effect_plan_root: RootV1,
}

impl ZDEXFeeAllocationOccurrenceV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        validate_schema_v1(&self.schema)?;
        validate_token_v1(&self.chain_id, "ZDEX fee occurrence chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.allocation_route_release_id,
            &self.authorized_buyback_route_release_id,
            &self.tokenomics_module_release_id,
            &self.command_occurrence_id,
            &self.policy_root,
            &self.fee_asset_id,
            &self.pre_lane_root,
            &self.post_lane_root,
            &self.effect_plan_root,
        ] {
            root.validate("ZDEX fee occurrence root", false)?;
        }
        validate_destination_amounts_v1(&self.allocations)?;
        if self.fee_charged_atoms == 0 || self.fee_charged_atoms > i128::MAX.unsigned_abs() {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX occurrence charged fee effect",
            ));
        }
        let allocated = self.allocations.iter().try_fold(0_u128, |total, value| {
            total
                .checked_add(value.allocation_atoms)
                .ok_or(AbiErrorV1::Conservation("ZDEX fee allocation overflow"))
        })?;
        if allocated.checked_add(self.carried_residue_atoms) != Some(self.fee_charged_atoms) {
            return Err(AbiErrorV1::Conservation("ZDEX fee occurrence"));
        }
        Ok(())
    }

    pub fn buyback_quote_atoms(&self) -> u128 {
        self.allocations
            .first()
            .map_or(0, |value| value.allocation_atoms)
    }

    pub fn occurrence_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-fee-allocation-occurrence-v1", self)
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXFeeAllocationRejectCodeV1 {
    ZERO_FEE,
    POLICY_MISMATCH,
    INSUFFICIENT_FEE_INGRESS,
    EFFECT_WIDTH_EXCEEDED,
    STATE_OVERFLOW,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeAllocationAcceptedV1 {
    pub pre_state: ZDEXFeeStateV1,
    pub post_state: ZDEXFeeStateV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub occurrence: ZDEXFeeAllocationOccurrenceV1,
}

impl ZDEXFeeAllocationAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.effects.validate()?;
        self.occurrence.validate()?;
        if self.effects.is_empty()
            || self.pre_state.state_root()? != self.occurrence.pre_lane_root
            || self.post_state.state_root()? != self.occurrence.post_lane_root
            || self.effects.effect_plan_root()? != self.occurrence.effect_plan_root
        {
            return Err(AbiErrorV1::InvalidBinding("ZDEX fee acceptance"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXFeeAllocationRejectedV1 {
    pub code: ZDEXFeeAllocationRejectCodeV1,
    pub pre_state: ZDEXFeeStateV1,
    pub post_state: ZDEXFeeStateV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXFeeAllocationRejectedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.effects.validate()?;
        if self.pre_state != self.post_state || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding("ZDEX fee reject is exact no-op"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(tag = "outcome", content = "value", deny_unknown_fields)]
pub enum ZDEXFeeAllocationResultV1 {
    Accepted(Box<ZDEXFeeAllocationAcceptedV1>),
    Rejected(Box<ZDEXFeeAllocationRejectedV1>),
}
