use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
};
use crate::fee_allocation_effects_v1;
use crate::proof::LaneModuleTransitionJournalV1;
use crate::release::LaneIdV1;
use crate::transition_zdex_fee_allocation_v1;
use crate::zdex_fee_allocation_types::{
    ZDEXFeeAllocationAcceptedV1, ZDEXFeeAllocationCommandV1, ZDEXFeeAllocationContextV1,
    ZDEXFeeAllocationPolicyV1, ZDEXFeeAllocationResultV1,
};
use crate::zdex_tokenomics_lane_types::zdex_tokenomics_complete_lane_obligation_root_v1;

pub const ZDEX_TOKENOMICS_FEE_ALLOCATION_PRIVATE_PORT_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-fee-allocation-private-port/v1";
pub const ZDEX_TOKENOMICS_FEE_ALLOCATION_COORDINATOR_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-fee-allocation-coordinator/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsFeeAllocationPrivatePortV1 {
    pub schema: String,
    pub module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub allocation_occurrence_root: RootV1,
    pub pre_fee_substate_root: RootV1,
    pub post_fee_substate_root: RootV1,
    pub module_effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
}

impl ZDEXTokenomicsFeeAllocationPrivatePortV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_TOKENOMICS_FEE_ALLOCATION_PRIVATE_PORT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        for root in [
            &self.module_release_id,
            &self.command_occurrence_id,
            &self.allocation_occurrence_root,
            &self.pre_fee_substate_root,
            &self.post_fee_substate_root,
            &self.module_effect_plan_root,
            &self.terminal_obligations_root,
        ] {
            root.validate("ZDEX tokenomics fee private-port root", false)?;
        }
        if self.terminal_obligations_root != zdex_tokenomics_complete_lane_obligation_root_v1()? {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX tokenomics fee complete-lane obligation",
            ));
        }
        Ok(())
    }

    pub fn port_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-tokenomics-fee-allocation-private-port-v1", self)
    }
}

fn require_exact_allocation_v1(
    allocation: &ZDEXFeeAllocationAcceptedV1,
    policy: &ZDEXFeeAllocationPolicyV1,
) -> AbiResultV1<()> {
    allocation.validate()?;
    policy.validate()?;
    if allocation.effects
        != fee_allocation_effects_v1(
            &allocation.occurrence,
            &allocation.pre_state,
            &allocation.post_state,
            policy,
        )?
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics fee allocation effects",
        ));
    }
    let occurrence = &allocation.occurrence;
    let context = ZDEXFeeAllocationContextV1 {
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: occurrence.writer_epoch,
        allocation_route_release_id: occurrence.allocation_route_release_id.clone(),
        authorized_buyback_route_release_id: occurrence.authorized_buyback_route_release_id.clone(),
        tokenomics_module_release_id: occurrence.tokenomics_module_release_id.clone(),
        command_occurrence_id: occurrence.command_occurrence_id.clone(),
        policy_root: occurrence.policy_root.clone(),
    };
    let recomputed = transition_zdex_fee_allocation_v1(
        &context,
        &allocation.pre_state,
        policy,
        &ZDEXFeeAllocationCommandV1 {
            fee_charged_atoms: occurrence.fee_charged_atoms,
        },
    )?;
    if recomputed != ZDEXFeeAllocationResultV1::Accepted(Box::new(allocation.clone())) {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics fee allocation policy refinement",
        ));
    }
    Ok(())
}

pub fn build_zdex_tokenomics_fee_allocation_private_port_v1(
    allocation: &ZDEXFeeAllocationAcceptedV1,
    policy: &ZDEXFeeAllocationPolicyV1,
) -> AbiResultV1<ZDEXTokenomicsFeeAllocationPrivatePortV1> {
    require_exact_allocation_v1(allocation, policy)?;
    let occurrence = &allocation.occurrence;
    let port = ZDEXTokenomicsFeeAllocationPrivatePortV1 {
        schema: ZDEX_TOKENOMICS_FEE_ALLOCATION_PRIVATE_PORT_SCHEMA_V1.to_owned(),
        module_release_id: occurrence.tokenomics_module_release_id.clone(),
        command_occurrence_id: occurrence.command_occurrence_id.clone(),
        allocation_occurrence_root: occurrence.occurrence_root()?,
        pre_fee_substate_root: occurrence.pre_lane_root.clone(),
        post_fee_substate_root: occurrence.post_lane_root.clone(),
        module_effect_plan_root: allocation.effects.effect_plan_root()?,
        terminal_obligations_root: zdex_tokenomics_complete_lane_obligation_root_v1()?,
    };
    port.validate()?;
    Ok(port)
}

#[derive(Serialize)]
struct FeeAllocationModuleReceiptV1<'a> {
    allocation_occurrence_root: &'a RootV1,
    pre_fee_substate_root: &'a RootV1,
    post_fee_substate_root: &'a RootV1,
    effect_plan_root: &'a RootV1,
    private_port_root: &'a RootV1,
    terminal_obligations_root: &'a RootV1,
}

fn module_receipt_root_v1(
    allocation: &ZDEXFeeAllocationAcceptedV1,
    private_port: &ZDEXTokenomicsFeeAllocationPrivatePortV1,
) -> AbiResultV1<RootV1> {
    let occurrence = &allocation.occurrence;
    let allocation_occurrence_root = occurrence.occurrence_root()?;
    let effect_plan_root = allocation.effects.effect_plan_root()?;
    let private_port_root = private_port.port_root()?;
    hash_global_v1(
        "zdex-tokenomics-fee-allocation-lane-module-receipt-v1",
        &FeeAllocationModuleReceiptV1 {
            allocation_occurrence_root: &allocation_occurrence_root,
            pre_fee_substate_root: &occurrence.pre_lane_root,
            post_fee_substate_root: &occurrence.post_lane_root,
            effect_plan_root: &effect_plan_root,
            private_port_root: &private_port_root,
            terminal_obligations_root: &private_port.terminal_obligations_root,
        },
    )
}

pub fn build_zdex_tokenomics_fee_allocation_module_journal_v1(
    allocation: &ZDEXFeeAllocationAcceptedV1,
    policy: &ZDEXFeeAllocationPolicyV1,
    private_port: &ZDEXTokenomicsFeeAllocationPrivatePortV1,
) -> AbiResultV1<LaneModuleTransitionJournalV1> {
    require_exact_allocation_v1(allocation, policy)?;
    private_port.validate()?;
    if private_port != &build_zdex_tokenomics_fee_allocation_private_port_v1(allocation, policy)? {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics fee module private port",
        ));
    }
    let occurrence = &allocation.occurrence;
    let module = LaneModuleTransitionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: occurrence.chain_id.clone(),
        deployment_root: occurrence.deployment_root.clone(),
        profile_root: occurrence.profile_root.clone(),
        writer_epoch: occurrence.writer_epoch,
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        module_release_id: occurrence.tokenomics_module_release_id.clone(),
        command_occurrence_id: occurrence.command_occurrence_id.clone(),
        pre_lane_root: RootV1::parse(ZERO_ROOT_V1, "ZDEX fee partial pre-root", true)?,
        post_lane_root: RootV1::parse(ZERO_ROOT_V1, "ZDEX fee partial post-root", true)?,
        effect_plan_root: allocation.effects.effect_plan_root()?,
        private_port_root: private_port.port_root()?,
        receipt_root: module_receipt_root_v1(allocation, private_port)?,
        terminal_obligations_root: private_port.terminal_obligations_root.clone(),
    };
    module.validate()?;
    Ok(module)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsFeeAllocationCoordinatorContextV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub coordinator_release_id: RootV1,
    pub allocation_route_release_id: RootV1,
    pub authorized_buyback_route_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub policy_root: RootV1,
}

impl ZDEXTokenomicsFeeAllocationCoordinatorContextV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_TOKENOMICS_FEE_ALLOCATION_COORDINATOR_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        validate_token_v1(&self.chain_id, "ZDEX tokenomics fee coordinator chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.coordinator_release_id,
            &self.allocation_route_release_id,
            &self.authorized_buyback_route_release_id,
            &self.tokenomics_module_release_id,
            &self.command_occurrence_id,
            &self.policy_root,
        ] {
            root.validate("ZDEX tokenomics fee coordinator root", false)?;
        }
        Ok(())
    }
}
