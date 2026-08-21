use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    ZERO_ROOT_V1,
};
use crate::effects::{GlobalEconomicEffectPlanV1, LaneWriteV1};
use crate::proof::{LaneCompositionJournalV1, LaneModuleTransitionJournalV1};
use crate::release::LaneIdV1;
use crate::zdex_fee_allocation_types::ZDEXFeeStateV1;
use crate::zdex_hyperdeflation_types::ZDEXSupplyStateV1;
use crate::zdex_purchase_burn_effects::burn_effects_v1;
use crate::zdex_purchase_burn_types::ZDEXBurnJournalV1;

pub const ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1: &str = "zenodex/zdex-tokenomics-lane-state/v1";
pub const ZDEX_TOKENOMICS_BURN_PRIVATE_PORT_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-burn-private-port/v1";
pub const ZDEX_TOKENOMICS_BURN_COORDINATOR_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-burn-coordinator/v1";
pub const MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1: usize = 64;

pub fn zdex_tokenomics_complete_lane_obligation_root_v1() -> AbiResultV1<RootV1> {
    #[derive(Serialize)]
    struct Obligation<'a> {
        schema: &'static str,
        lane_id: LaneIdV1,
        requirement: &'a str,
    }
    hash_global_v1(
        "zdex-tokenomics-coordinator-obligation-v1",
        &Obligation {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            requirement: "VERIFIED_COMPLETE_LANE_ROOT",
        },
    )
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsLaneStateV1 {
    pub schema: String,
    pub supply_state: ZDEXSupplyStateV1,
    pub fee_allocation_states: Vec<ZDEXFeeStateV1>,
    pub staking_state_root: RootV1,
    pub host_claims_state_root: RootV1,
    pub treasury_claims_state_root: RootV1,
    pub proof_rewards_state_root: RootV1,
    pub cover_reserve_state_root: RootV1,
    pub lp_rebates_state_root: RootV1,
}

impl ZDEXTokenomicsLaneStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_TOKENOMICS_LANE_STATE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.supply_state.validate()?;
        if self.fee_allocation_states.is_empty()
            || self.fee_allocation_states.len() > MAX_ZDEX_TOKENOMICS_FEE_ASSETS_V1
        {
            return Err(AbiErrorV1::InvalidBounds(
                "ZDEX tokenomics fee-state registry width",
            ));
        }
        for state in &self.fee_allocation_states {
            state.validate()?;
            if self.supply_state.asset_id == state.fee_asset_id {
                return Err(AbiErrorV1::InvalidBinding(
                    "ZDEX supply asset cannot also be a fee asset",
                ));
            }
        }
        if self
            .fee_allocation_states
            .windows(2)
            .any(|pair| pair[0].fee_asset_id >= pair[1].fee_asset_id)
        {
            return Err(AbiErrorV1::InvalidOrder("ZDEX tokenomics fee states"));
        }
        for root in [
            &self.staking_state_root,
            &self.host_claims_state_root,
            &self.treasury_claims_state_root,
            &self.proof_rewards_state_root,
            &self.cover_reserve_state_root,
            &self.lp_rebates_state_root,
        ] {
            root.validate("ZDEX tokenomics lane component root", false)?;
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-tokenomics-lane-state-v1", self)
    }

    pub fn unrelated_to_burn_matches(&self, other: &Self) -> bool {
        self.fee_allocation_states == other.fee_allocation_states
            && self.staking_state_root == other.staking_state_root
            && self.host_claims_state_root == other.host_claims_state_root
            && self.treasury_claims_state_root == other.treasury_claims_state_root
            && self.proof_rewards_state_root == other.proof_rewards_state_root
            && self.cover_reserve_state_root == other.cover_reserve_state_root
            && self.lp_rebates_state_root == other.lp_rebates_state_root
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsBurnPrivatePortV1 {
    pub schema: String,
    pub module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub burn_journal_root: RootV1,
    pub pre_burn_substate_root: RootV1,
    pub post_burn_substate_root: RootV1,
    pub module_effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
}

impl ZDEXTokenomicsBurnPrivatePortV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_TOKENOMICS_BURN_PRIVATE_PORT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        for root in [
            &self.module_release_id,
            &self.command_occurrence_id,
            &self.burn_journal_root,
            &self.pre_burn_substate_root,
            &self.post_burn_substate_root,
            &self.module_effect_plan_root,
            &self.terminal_obligations_root,
        ] {
            root.validate("ZDEX tokenomics burn private-port root", false)?;
        }
        if self.terminal_obligations_root != zdex_tokenomics_complete_lane_obligation_root_v1()? {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX tokenomics complete-lane obligation",
            ));
        }
        Ok(())
    }

    pub fn port_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("zdex-tokenomics-burn-private-port-v1", self)
    }
}

pub fn build_zdex_tokenomics_burn_private_port_v1(
    journal: &ZDEXBurnJournalV1,
    effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<ZDEXTokenomicsBurnPrivatePortV1> {
    journal.validate()?;
    effects.validate()?;
    if effects != &burn_effects_v1(journal)? {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics burn private-port effects",
        ));
    }
    let port = ZDEXTokenomicsBurnPrivatePortV1 {
        schema: ZDEX_TOKENOMICS_BURN_PRIVATE_PORT_SCHEMA_V1.to_owned(),
        module_release_id: journal.tokenomics_module_release_id.clone(),
        command_occurrence_id: journal.command_occurrence_id.clone(),
        burn_journal_root: journal.journal_root()?,
        pre_burn_substate_root: journal.pre_tokenomics_burn_substate_root.clone(),
        post_burn_substate_root: journal.post_tokenomics_burn_substate_root.clone(),
        module_effect_plan_root: effects.effect_plan_root()?,
        terminal_obligations_root: zdex_tokenomics_complete_lane_obligation_root_v1()?,
    };
    port.validate()?;
    Ok(port)
}

#[derive(Serialize)]
struct ZDEXTokenomicsBurnModuleReceiptV1<'a> {
    burn_journal_root: &'a RootV1,
    pre_burn_substate_root: &'a RootV1,
    post_burn_substate_root: &'a RootV1,
    effect_plan_root: &'a RootV1,
    private_port_root: &'a RootV1,
    terminal_obligations_root: &'a RootV1,
}

fn zdex_tokenomics_burn_module_receipt_root_v1(
    journal: &ZDEXBurnJournalV1,
    effects: &GlobalEconomicEffectPlanV1,
    private_port: &ZDEXTokenomicsBurnPrivatePortV1,
) -> AbiResultV1<RootV1> {
    let burn_journal_root = journal.journal_root()?;
    let effect_plan_root = effects.effect_plan_root()?;
    let private_port_root = private_port.port_root()?;
    hash_global_v1(
        "zdex-tokenomics-burn-lane-module-receipt-v1",
        &ZDEXTokenomicsBurnModuleReceiptV1 {
            burn_journal_root: &burn_journal_root,
            pre_burn_substate_root: &journal.pre_tokenomics_burn_substate_root,
            post_burn_substate_root: &journal.post_tokenomics_burn_substate_root,
            effect_plan_root: &effect_plan_root,
            private_port_root: &private_port_root,
            terminal_obligations_root: &private_port.terminal_obligations_root,
        },
    )
}

pub fn build_zdex_tokenomics_burn_module_journal_v1(
    journal: &ZDEXBurnJournalV1,
    effects: &GlobalEconomicEffectPlanV1,
    private_port: &ZDEXTokenomicsBurnPrivatePortV1,
) -> AbiResultV1<LaneModuleTransitionJournalV1> {
    journal.validate()?;
    effects.validate()?;
    private_port.validate()?;
    if effects != &burn_effects_v1(journal)?
        || private_port != &build_zdex_tokenomics_burn_private_port_v1(journal, effects)?
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics burn module journal inputs",
        ));
    }
    let module_journal = LaneModuleTransitionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: journal.chain_id.clone(),
        deployment_root: journal.deployment_root.clone(),
        profile_root: journal.profile_root.clone(),
        writer_epoch: journal.writer_epoch,
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        module_release_id: journal.tokenomics_module_release_id.clone(),
        command_occurrence_id: journal.command_occurrence_id.clone(),
        pre_lane_root: RootV1::parse(ZERO_ROOT_V1, "ZDEX burn partial pre-root", true)?,
        post_lane_root: RootV1::parse(ZERO_ROOT_V1, "ZDEX burn partial post-root", true)?,
        effect_plan_root: effects.effect_plan_root()?,
        private_port_root: private_port.port_root()?,
        receipt_root: zdex_tokenomics_burn_module_receipt_root_v1(journal, effects, private_port)?,
        terminal_obligations_root: private_port.terminal_obligations_root.clone(),
    };
    module_journal.validate()?;
    Ok(module_journal)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsBurnCoordinatorContextV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub coordinator_release_id: RootV1,
    pub route_release_id: RootV1,
    pub tokenomics_module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub issue_burn_policy_root: RootV1,
}

impl ZDEXTokenomicsBurnCoordinatorContextV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ZDEX_TOKENOMICS_BURN_COORDINATOR_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        validate_token_v1(&self.chain_id, "ZDEX tokenomics coordinator chain id")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.coordinator_release_id,
            &self.route_release_id,
            &self.tokenomics_module_release_id,
            &self.command_occurrence_id,
            &self.issue_burn_policy_root,
        ] {
            root.validate("ZDEX tokenomics coordinator root", false)?;
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ZDEXTokenomicsLaneCoordinatorRejectCodeV1 {
    CHAIN_MISMATCH,
    DEPLOYMENT_MISMATCH,
    PROFILE_MISMATCH,
    WRITER_EPOCH_MISMATCH,
    WRONG_LANE,
    MODULE_RELEASE_MISMATCH,
    ROUTE_RELEASE_MISMATCH,
    OCCURRENCE_MISMATCH,
    PARTIAL_LANE_ROOT_CLAIM,
    PRIVATE_PORT_MISMATCH,
    MODULE_RECEIPT_MISMATCH,
    TERMINAL_OBLIGATION_MISMATCH,
    BURN_JOURNAL_MISMATCH,
    FEE_ALLOCATION_OCCURRENCE_MISMATCH,
    EFFECT_PLAN_MISMATCH,
    PRE_SUBSTATE_MISMATCH,
    POST_SUBSTATE_MISMATCH,
    UNRELATED_STATE_MUTATION,
    STATE_EFFECT_MISMATCH,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsLaneCompositionAcceptedV1 {
    pub post_state: ZDEXTokenomicsLaneStateV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub lane_journal: LaneCompositionJournalV1,
}

impl ZDEXTokenomicsLaneCompositionAcceptedV1 {
    pub fn expected_lane_write(&self) -> AbiResultV1<&LaneWriteV1> {
        self.effects
            .lane_writes
            .first()
            .ok_or(AbiErrorV1::InvalidBinding(
                "ZDEX tokenomics accepted lane write",
            ))
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.lane_journal.validate()?;
        if self.lane_journal.pre_lane_root.is_zero()
            || self.lane_journal.post_lane_root.is_zero()
            || self.lane_journal.lane_id != LaneIdV1::ZDEX_TOKENOMICS
            || self.lane_journal.post_lane_root != self.post_state.state_root()?
            || self.lane_journal.effect_plan_root != self.effects.effect_plan_root()?
            || !self.lane_journal.terminal_obligations_root.is_zero()
            || self.effects.lane_writes.len() != 1
            || self.effects.lane_writes[0].lane_id != LaneIdV1::ZDEX_TOKENOMICS
            || self.effects.lane_writes[0].pre_root != self.lane_journal.pre_lane_root
            || self.effects.lane_writes[0].post_root != self.lane_journal.post_lane_root
        {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX tokenomics lane composition acceptance",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ZDEXTokenomicsLaneCompositionRejectedV1 {
    pub code: ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    pub pre_lane_root: RootV1,
    pub post_lane_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

impl ZDEXTokenomicsLaneCompositionRejectedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_lane_root
            .validate("ZDEX tokenomics rejected pre-lane root", false)?;
        self.post_lane_root
            .validate("ZDEX tokenomics rejected post-lane root", false)?;
        self.effects.validate()?;
        if self.pre_lane_root != self.post_lane_root || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "ZDEX tokenomics coordinator reject is no-op",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ZDEXTokenomicsLaneCompositionResultV1 {
    Accepted(Box<ZDEXTokenomicsLaneCompositionAcceptedV1>),
    Rejected(Box<ZDEXTokenomicsLaneCompositionRejectedV1>),
}
