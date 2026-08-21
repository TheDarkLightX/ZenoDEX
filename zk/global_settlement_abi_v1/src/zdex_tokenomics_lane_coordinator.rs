use crate::canonical::{AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1, ZERO_ROOT_V1};
use crate::effects::{GlobalEconomicEffectPlanV1, LaneWriteV1};
use crate::proof::{LaneCompositionJournalV1, LaneModuleTransitionJournalV1};
use crate::release::LaneIdV1;
use crate::zdex_purchase_burn_effects::burn_effects_v1;
use crate::zdex_purchase_burn_types::ZDEXBurnJournalV1;
use crate::zdex_tokenomics_lane_types::{
    build_zdex_tokenomics_burn_module_journal_v1, zdex_tokenomics_complete_lane_obligation_root_v1,
    ZDEXTokenomicsBurnCoordinatorContextV1, ZDEXTokenomicsBurnPrivatePortV1,
    ZDEXTokenomicsLaneCompositionAcceptedV1, ZDEXTokenomicsLaneCompositionRejectedV1,
    ZDEXTokenomicsLaneCompositionResultV1, ZDEXTokenomicsLaneCoordinatorRejectCodeV1,
    ZDEXTokenomicsLaneStateV1,
};

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

pub struct ZDEXTokenomicsBurnLaneCandidateV1<'a> {
    pub context: &'a ZDEXTokenomicsBurnCoordinatorContextV1,
    pub module_journal: &'a LaneModuleTransitionJournalV1,
    pub private_port: &'a ZDEXTokenomicsBurnPrivatePortV1,
    pub pre_state: &'a ZDEXTokenomicsLaneStateV1,
    pub post_state: &'a ZDEXTokenomicsLaneStateV1,
    pub burn_journal: &'a ZDEXBurnJournalV1,
    pub module_effects: &'a GlobalEconomicEffectPlanV1,
}

impl ZDEXTokenomicsBurnLaneCandidateV1<'_> {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.context.validate()?;
        self.module_journal.validate()?;
        self.private_port.validate()?;
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.burn_journal.validate()?;
        self.module_effects.validate()?;
        Ok(())
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
    candidate: &ZDEXTokenomicsBurnLaneCandidateV1<'_>,
) -> Option<ZDEXTokenomicsLaneCoordinatorRejectCodeV1> {
    let context = candidate.context;
    let module = candidate.module_journal;
    if module.chain_id != context.chain_id {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::CHAIN_MISMATCH);
    }
    if module.deployment_root != context.deployment_root {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::DEPLOYMENT_MISMATCH);
    }
    if module.profile_root != context.profile_root {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PROFILE_MISMATCH);
    }
    if module.writer_epoch != context.writer_epoch {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::WRITER_EPOCH_MISMATCH);
    }
    if module.lane_id != LaneIdV1::ZDEX_TOKENOMICS {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::WRONG_LANE);
    }
    if module.module_release_id != context.tokenomics_module_release_id {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::MODULE_RELEASE_MISMATCH);
    }
    if module.command_occurrence_id != context.command_occurrence_id {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::OCCURRENCE_MISMATCH);
    }
    if !module.pre_lane_root.is_zero() || !module.post_lane_root.is_zero() {
        return Some(ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PARTIAL_LANE_ROOT_CLAIM);
    }
    None
}

fn port_reject_v1(
    candidate: &ZDEXTokenomicsBurnLaneCandidateV1<'_>,
) -> AbiResultV1<Option<ZDEXTokenomicsLaneCoordinatorRejectCodeV1>> {
    let context = candidate.context;
    let module = candidate.module_journal;
    let port = candidate.private_port;
    let burn = candidate.burn_journal;
    let effects = candidate.module_effects;
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
    if burn.route_release_id != context.route_release_id {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::ROUTE_RELEASE_MISMATCH,
        ));
    }
    if burn.chain_id != context.chain_id
        || burn.deployment_root != context.deployment_root
        || burn.profile_root != context.profile_root
        || burn.writer_epoch != context.writer_epoch
        || burn.tokenomics_module_release_id != context.tokenomics_module_release_id
        || burn.command_occurrence_id != context.command_occurrence_id
        || burn.issue_burn_policy_root != context.issue_burn_policy_root
        || port.burn_journal_root != burn.journal_root()?
        || port.pre_burn_substate_root != burn.pre_tokenomics_burn_substate_root
        || port.post_burn_substate_root != burn.post_tokenomics_burn_substate_root
    {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::BURN_JOURNAL_MISMATCH,
        ));
    }
    let effect_root = effects.effect_plan_root()?;
    if effects != &burn_effects_v1(burn)?
        || module.effect_plan_root != effect_root
        || port.module_effect_plan_root != effect_root
        || burn.effect_plan_root != effect_root
    {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::EFFECT_PLAN_MISMATCH,
        ));
    }
    let expected_module = build_zdex_tokenomics_burn_module_journal_v1(burn, effects, port)?;
    if module.receipt_root != expected_module.receipt_root {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::MODULE_RECEIPT_MISMATCH,
        ));
    }
    Ok(None)
}

fn state_reject_v1(
    candidate: &ZDEXTokenomicsBurnLaneCandidateV1<'_>,
) -> AbiResultV1<Option<ZDEXTokenomicsLaneCoordinatorRejectCodeV1>> {
    let context = candidate.context;
    let pre_state = candidate.pre_state;
    let post_state = candidate.post_state;
    let burn = candidate.burn_journal;
    if pre_state.supply_state.state_root()? != burn.pre_tokenomics_burn_substate_root {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::PRE_SUBSTATE_MISMATCH,
        ));
    }
    if post_state.supply_state.state_root()? != burn.post_tokenomics_burn_substate_root {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::POST_SUBSTATE_MISMATCH,
        ));
    }
    if !pre_state.unrelated_to_burn_matches(post_state) {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::UNRELATED_STATE_MUTATION,
        ));
    }
    let pre_bucket = pre_state.supply_state.bucket_atoms(&burn.burn_bucket_id)?;
    let post_bucket = post_state.supply_state.bucket_atoms(&burn.burn_bucket_id)?;
    if pre_state.supply_state.policy_root != context.issue_burn_policy_root
        || post_state.supply_state.policy_root != context.issue_burn_policy_root
        || pre_state.supply_state.asset_id != burn.zdex_asset_id
        || post_state.supply_state.asset_id != burn.zdex_asset_id
        || pre_state.supply_state.live_supply_atoms != burn.zdex_supply_pre_atoms
        || post_state.supply_state.live_supply_atoms != burn.zdex_supply_post_atoms
        || burn.zdex_owned_pre_atoms != burn.zdex_supply_pre_atoms
        || burn.zdex_owned_post_atoms != burn.zdex_supply_post_atoms
        || pre_bucket != Some(burn.burn_bucket_pre_atoms)
        || post_bucket.is_some()
        || burn.burn_bucket_post_atoms != 0
    {
        return Ok(Some(
            ZDEXTokenomicsLaneCoordinatorRejectCodeV1::STATE_EFFECT_MISMATCH,
        ));
    }
    Ok(None)
}

fn normalize_effects_v1(
    candidate: &ZDEXTokenomicsBurnLaneCandidateV1<'_>,
) -> AbiResultV1<GlobalEconomicEffectPlanV1> {
    let pre_state = candidate.pre_state;
    let post_state = candidate.post_state;
    let effects = candidate.module_effects;
    let normalized = GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: effects.rows.clone(),
        asset_conservation: effects.asset_conservation.clone(),
        fee_conservation: effects.fee_conservation.clone(),
        lane_writes: vec![LaneWriteV1 {
            lane_id: LaneIdV1::ZDEX_TOKENOMICS,
            pre_root: pre_state.state_root()?,
            post_root: post_state.state_root()?,
        }],
        occurrence_consumptions: effects.occurrence_consumptions.clone(),
        external_outbox_enqueue: effects.external_outbox_enqueue.clone(),
    };
    normalized.validate()?;
    Ok(normalized)
}

pub fn compose_zdex_tokenomics_burn_lane_v1(
    candidate: ZDEXTokenomicsBurnLaneCandidateV1<'_>,
) -> AbiResultV1<ZDEXTokenomicsLaneCompositionResultV1> {
    candidate.validate()?;
    if let Some(code) = context_reject_v1(&candidate) {
        return reject_v1(code, candidate.pre_state);
    }
    if let Some(code) = port_reject_v1(&candidate)? {
        return reject_v1(code, candidate.pre_state);
    }
    if let Some(code) = state_reject_v1(&candidate)? {
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
            "ZDEX tokenomics discharged terminal obligations",
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
