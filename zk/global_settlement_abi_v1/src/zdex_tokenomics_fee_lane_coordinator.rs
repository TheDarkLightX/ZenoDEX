use crate::canonical::{AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1};
use crate::effects::{GlobalEconomicEffectPlanV1, LaneWriteV1};
use crate::fee_allocation_effects_v1;
use crate::proof::{LaneCompositionJournalV1, LaneModuleTransitionJournalV1};
use crate::release::LaneIdV1;
use crate::zdex_fee_allocation_types::{
    ZDEXFeeAllocationAcceptedV1, ZDEXFeeAllocationPolicyV1, ZDEXFeeStateV1,
};
use crate::zdex_tokenomics_fee_lane_types::{
    build_zdex_tokenomics_fee_allocation_module_journal_v1,
    ZDEXTokenomicsFeeAllocationCoordinatorContextV1, ZDEXTokenomicsFeeAllocationPrivatePortV1,
};
use crate::zdex_tokenomics_lane_types::{
    zdex_tokenomics_complete_lane_obligation_root_v1, ZDEXTokenomicsLaneCompositionAcceptedV1,
    ZDEXTokenomicsLaneCompositionRejectedV1, ZDEXTokenomicsLaneCompositionResultV1,
    ZDEXTokenomicsLaneCoordinatorRejectCodeV1, ZDEXTokenomicsLaneStateV1,
};

pub struct ZDEXTokenomicsFeeAllocationLaneCandidateV1<'a> {
    pub context: &'a ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    pub module_journal: &'a LaneModuleTransitionJournalV1,
    pub private_port: &'a ZDEXTokenomicsFeeAllocationPrivatePortV1,
    pub pre_state: &'a ZDEXTokenomicsLaneStateV1,
    pub post_state: &'a ZDEXTokenomicsLaneStateV1,
    pub allocation: &'a ZDEXFeeAllocationAcceptedV1,
    pub policy: &'a ZDEXFeeAllocationPolicyV1,
}

impl ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_> {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.context.validate()?;
        self.module_journal.validate()?;
        self.private_port.validate()?;
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.allocation.validate()?;
        self.policy.validate()
    }
}

fn empty_effects_v1() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: vec![],
        asset_conservation: vec![],
        fee_conservation: vec![],
        lane_writes: vec![],
        occurrence_consumptions: vec![],
        external_outbox_enqueue: vec![],
    }
}

fn reject_v1(
    code: ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    pre_state: &ZDEXTokenomicsLaneStateV1,
) -> AbiResultV1<ZDEXTokenomicsLaneCompositionResultV1> {
    let root = pre_state.state_root()?;
    let rejected = ZDEXTokenomicsLaneCompositionRejectedV1 {
        code,
        pre_lane_root: root.clone(),
        post_lane_root: root,
        effects: empty_effects_v1(),
    };
    rejected.validate()?;
    Ok(ZDEXTokenomicsLaneCompositionResultV1::Rejected(Box::new(
        rejected,
    )))
}

fn context_reject_v1(
    candidate: &ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_>,
) -> Option<ZDEXTokenomicsLaneCoordinatorRejectCodeV1> {
    let context = candidate.context;
    let module = candidate.module_journal;
    let occurrence = &candidate.allocation.occurrence;
    let checks = [
        (
            module.chain_id != context.chain_id,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::CHAIN_MISMATCH,
        ),
        (
            module.deployment_root != context.deployment_root,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::DEPLOYMENT_MISMATCH,
        ),
        (
            module.profile_root != context.profile_root,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PROFILE_MISMATCH,
        ),
        (
            module.writer_epoch != context.writer_epoch,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::WRITER_EPOCH_MISMATCH,
        ),
        (
            module.lane_id != LaneIdV1::ZDEX_TOKENOMICS,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::WRONG_LANE,
        ),
        (
            module.module_release_id != context.tokenomics_module_release_id,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::MODULE_RELEASE_MISMATCH,
        ),
        (
            module.command_occurrence_id != context.command_occurrence_id,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::OCCURRENCE_MISMATCH,
        ),
        (
            !module.pre_lane_root.is_zero() || !module.post_lane_root.is_zero(),
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PARTIAL_LANE_ROOT_CLAIM,
        ),
        (
            occurrence.allocation_route_release_id != context.allocation_route_release_id,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::ROUTE_RELEASE_MISMATCH,
        ),
        (
            occurrence.authorized_buyback_route_release_id
                != context.authorized_buyback_route_release_id,
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::ROUTE_RELEASE_MISMATCH,
        ),
    ];
    checks
        .into_iter()
        .find_map(|(failed, code)| failed.then_some(code))
}

fn port_reject_v1(
    candidate: &ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_>,
) -> AbiResultV1<Option<ZDEXTokenomicsLaneCoordinatorRejectCodeV1>> {
    let module = candidate.module_journal;
    let port = candidate.private_port;
    if module.private_port_root != port.port_root()?
        || port.module_release_id != module.module_release_id
        || port.command_occurrence_id != module.command_occurrence_id
    {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PRIVATE_PORT_MISMATCH,
        ));
    }
    let obligation = zdex_tokenomics_complete_lane_obligation_root_v1()?;
    if module.terminal_obligations_root != obligation
        || port.terminal_obligations_root != obligation
    {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::TERMINAL_OBLIGATION_MISMATCH,
        ));
    }
    if !occurrence_matches_context_v1(candidate)? {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::FEE_ALLOCATION_OCCURRENCE_MISMATCH,
        ));
    }
    effect_reject_v1(candidate)
}

fn occurrence_matches_context_v1(
    candidate: &ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_>,
) -> AbiResultV1<bool> {
    let context = candidate.context;
    let port = candidate.private_port;
    let occurrence = &candidate.allocation.occurrence;
    if occurrence.chain_id != context.chain_id
        || occurrence.deployment_root != context.deployment_root
        || occurrence.profile_root != context.profile_root
        || occurrence.writer_epoch != context.writer_epoch
        || occurrence.tokenomics_module_release_id != context.tokenomics_module_release_id
        || occurrence.command_occurrence_id != context.command_occurrence_id
        || occurrence.policy_root != context.policy_root
        || port.allocation_occurrence_root != occurrence.occurrence_root()?
        || port.pre_fee_substate_root != occurrence.pre_lane_root
        || port.post_fee_substate_root != occurrence.post_lane_root
    {
        return Ok(false);
    }
    Ok(true)
}

fn effect_reject_v1(
    candidate: &ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_>,
) -> AbiResultV1<Option<ZDEXTokenomicsLaneCoordinatorRejectCodeV1>> {
    let module = candidate.module_journal;
    let port = candidate.private_port;
    let allocation = candidate.allocation;
    let occurrence = &allocation.occurrence;
    let expected_effects = match fee_allocation_effects_v1(
        occurrence,
        &allocation.pre_state,
        &allocation.post_state,
        candidate.policy,
    ) {
        Ok(effects) => effects,
        Err(_) => {
            return Ok(Some(
                ZDEXTokenomicsLaneCoordinatorRejectCodeV1::EFFECT_PLAN_MISMATCH,
            ))
        }
    };
    let effect_root = expected_effects.effect_plan_root()?;
    if allocation.effects != expected_effects
        || module.effect_plan_root != effect_root
        || port.module_effect_plan_root != effect_root
    {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::EFFECT_PLAN_MISMATCH,
        ));
    }
    let expected_module =
        build_zdex_tokenomics_fee_allocation_module_journal_v1(allocation, candidate.policy, port)?;
    if module.receipt_root != expected_module.receipt_root {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::MODULE_RECEIPT_MISMATCH,
        ));
    }
    Ok(None)
}

fn state_for_asset_v1<'a>(
    states: &'a [ZDEXFeeStateV1],
    asset: &RootV1,
) -> Option<&'a ZDEXFeeStateV1> {
    states.iter().find(|state| &state.fee_asset_id == asset)
}

fn state_reject_v1(
    candidate: &ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_>,
) -> Option<ZDEXTokenomicsLaneCoordinatorRejectCodeV1> {
    let allocation = candidate.allocation;
    let asset = &allocation.occurrence.fee_asset_id;
    if state_for_asset_v1(&candidate.pre_state.fee_allocation_states, asset)
        != Some(&allocation.pre_state)
    {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PRE_SUBSTATE_MISMATCH);
    }
    if state_for_asset_v1(&candidate.post_state.fee_allocation_states, asset)
        != Some(&allocation.post_state)
    {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::POST_SUBSTATE_MISMATCH);
    }
    let pre_other: Vec<_> = candidate
        .pre_state
        .fee_allocation_states
        .iter()
        .filter(|state| &state.fee_asset_id != asset)
        .collect();
    let post_other: Vec<_> = candidate
        .post_state
        .fee_allocation_states
        .iter()
        .filter(|state| &state.fee_asset_id != asset)
        .collect();
    if pre_other != post_other
        || candidate.pre_state.supply_state != candidate.post_state.supply_state
        || candidate.pre_state.staking_state_root != candidate.post_state.staking_state_root
        || candidate.pre_state.host_claims_state_root != candidate.post_state.host_claims_state_root
        || candidate.pre_state.treasury_claims_state_root
            != candidate.post_state.treasury_claims_state_root
        || candidate.pre_state.proof_rewards_state_root
            != candidate.post_state.proof_rewards_state_root
        || candidate.pre_state.cover_reserve_state_root
            != candidate.post_state.cover_reserve_state_root
        || candidate.pre_state.lp_rebates_state_root != candidate.post_state.lp_rebates_state_root
    {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::UNRELATED_STATE_MUTATION);
    }
    None
}

fn normalize_effects_v1(
    candidate: &ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_>,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let effects = &candidate.allocation.effects;
    let normalized = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: effects.rows.clone(),
        asset_conservation: effects.asset_conservation.clone(),
        fee_conservation: effects.fee_conservation.clone(),
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            pre_root: candidate.pre_state.state_root()?,
            post_root: candidate.post_state.state_root()?,
        }],
        occurrence_consumptions: effects.occurrence_consumptions.clone(),
        external_outbox_enqueue: effects.external_outbox_enqueue.clone(),
    };
    normalized.validate()?;
    Ok(normalized)
}

pub fn compose_zdex_tokenomics_fee_allocation_lane_v1(
    candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1<'_>,
) -> AbiResultV1<ZDEXTokenomicsLaneCompositionResultV1> {
    candidate.validate()?;
    if let Some(code) = context_reject_v1(&candidate) {
        return reject_v1(code, candidate.pre_state);
    }
    if let Some(code) = port_reject_v1(&candidate)? {
        return reject_v1(code, candidate.pre_state);
    }
    if let Some(code) = state_reject_v1(&candidate) {
        return reject_v1(code, candidate.pre_state);
    }
    let normalized = normalize_effects_v1(&candidate)?;
    let lane_journal = LaneCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: candidate.context.chain_id.clone(),
        deployment_root: candidate.context.deployment_root.clone(),
        profile_root: candidate.context.profile_root.clone(),
        writer_epoch: candidate.context.writer_epoch,
        lane_id: LaneIdV1::ZDEX_TOKENOMICS,
        coordinator_release_id: candidate.context.coordinator_release_id.clone(),
        command_occurrence_id: candidate.context.command_occurrence_id.clone(),
        ordered_module_journal_roots: vec![candidate.module_journal.journal_root()?],
        pre_lane_root: candidate.pre_state.state_root()?,
        post_lane_root: candidate.post_state.state_root()?,
        effect_plan_root: normalized.effect_plan_root()?,
        terminal_obligations_root: RootV1::parse(
            ZERO_ROOT_V1,
            "ZDEX tokenomics discharged fee obligation",
            true,
        )?,
    };
    lane_journal.validate()?;
    let accepted = ZDEXTokenomicsLaneCompositionAcceptedV1 {
        post_state: candidate.post_state.clone(),
        effects: normalized,
        lane_journal,
    };
    accepted.validate()?;
    Ok(ZDEXTokenomicsLaneCompositionResultV1::Accepted(Box::new(
        accepted,
    )))
}
