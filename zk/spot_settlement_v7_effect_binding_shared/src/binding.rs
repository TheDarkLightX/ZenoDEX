use alloc::collections::BTreeSet;
use alloc::vec;
use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    AssetEffectKindV2, AuthorizedEconomicActionV1, CommitmentV3, EconomicActionBatchV1,
    EconomicActionIdV1, EconomicActionRecordInputV1, EconomicActionRecordV1,
    SettlementEffectPlanInputV2, SettlementEffectPlanV2,
};

use crate::journal::SpotSettlementV7EffectBindingJournalInputV1;
use crate::{
    SpotSettlementStateEffectOpeningV1, SpotSettlementV7EffectBindingErrorV1,
    SpotSettlementV7EffectBindingJournalV1,
};

/// Closed proof-neutral relation between one full state opening and one plan.
///
/// The fields are private and construction derives the V7 plan from the source
/// plan lineage. This value grants no receipt, finality, persistence, or
/// settlement authority.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v7_effect_binding_shared::BoundSpotSettlementStateV1;
/// let bound: BoundSpotSettlementStateV1 = unimplemented!();
/// let _ = bound.settlement_authority();
/// ```
#[derive(Debug, PartialEq, Eq)]
pub struct BoundSpotSettlementStateV1 {
    opening: SpotSettlementStateEffectOpeningV1,
    plan: SettlementEffectPlanV2,
    journal: SpotSettlementV7EffectBindingJournalV1,
}

impl BoundSpotSettlementStateV1 {
    pub const fn opening(&self) -> &SpotSettlementStateEffectOpeningV1 {
        &self.opening
    }

    pub const fn plan(&self) -> &SettlementEffectPlanV2 {
        &self.plan
    }

    pub const fn journal(&self) -> &SpotSettlementV7EffectBindingJournalV1 {
        &self.journal
    }
}

/// Derive and bind the V7 plan from source Plan A.
///
/// This function accepts no caller-proposed V7 plan. The future guest must
/// first prove that `source_plan_a` is the exact plan encoded by the
/// authenticated V6 source receipt. The plain Rust type supplies no authority.
pub fn bind_spot_settlement_effect_plan_v1(
    opening: SpotSettlementStateEffectOpeningV1,
    source_plan_a: &SettlementEffectPlanV2,
) -> Result<BoundSpotSettlementStateV1, SpotSettlementV7EffectBindingErrorV1> {
    let source_plan_commitment = source_plan_a.canonical_commitment()?;
    let plan = derive_expected_spot_v7_settlement_effect_plan_v1(&opening, source_plan_a)?;
    bind_derived_plan(opening, plan, source_plan_commitment)
}

/// Project authenticated V6 authorization lineage into the exact V7 plan.
///
/// This helper performs no receipt verification. It preserves the source
/// application, domain, action type, authorization, validity window, epoch,
/// grant, policy, and consumed-object lineage. It replaces only the state and
/// effect fields with values derived from the complete V7 pre/post opening.
pub fn derive_expected_spot_v7_settlement_effect_plan_v1(
    opening: &SpotSettlementStateEffectOpeningV1,
    source_plan_a: &SettlementEffectPlanV2,
) -> Result<SettlementEffectPlanV2, SpotSettlementV7EffectBindingErrorV1> {
    require_restricted_source_plan(source_plan_a)?;
    let [source_action] = source_plan_a.economic_action_batch().actions() else {
        return Err(SpotSettlementV7EffectBindingErrorV1::ExpectedSingletonAction);
    };
    let source_record = source_action.record();
    if source_record.authorization_nonce() != u64::from(opening.ingress_nonce()) {
        return Err(SpotSettlementV7EffectBindingErrorV1::ActionNonceMismatch);
    }

    let source_plan_commitment = source_plan_a.canonical_commitment()?;
    let consumed_object_ids = derived_consumed_object_lineage(
        source_record.consumed_object_ids(),
        opening.source_journal_commitment(),
        source_plan_commitment,
    );
    let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
        application_id: source_record.application_id(),
        chain_or_domain_id: source_record.chain_or_domain_id(),
        action_type_id: source_record.action_type_id(),
        authorization_subject_id: source_record.authorization_subject_id(),
        authorization_scope_id: source_record.authorization_scope_id(),
        authorization_nonce: source_record.authorization_nonce(),
        valid_from_epoch: source_record.valid_from_epoch(),
        valid_through_epoch: source_record.valid_through_epoch(),
        pre_state_root: opening.pre_state_root(),
        action_semantics_hash: opening.action_semantics_hash(),
        effect_commitment: opening.effect_commitment(),
        consumed_object_ids,
    })?;
    let action = AuthorizedEconomicActionV1::new(record, source_action.authorization_grant_id())?;
    let action_id = action.action_id()?;
    let batch = EconomicActionBatchV1::new(
        source_plan_a.economic_action_batch().epoch_id(),
        opening.pre_state_root(),
        vec![action],
    )?;
    Ok(SettlementEffectPlanV2::new(SettlementEffectPlanInputV2 {
        source_semantic_journal_hash: opening.source_journal_commitment(),
        public_policy_hash: source_plan_a.public_policy_hash(),
        post_state_root: opening.post_state_root(),
        economic_action_batch: batch,
        ledger_cell_writes: opening.expected_cell_writes(action_id)?,
        asset_effects: opening.expected_asset_effects(action_id)?,
        message_effects: vec![],
        carry_effects: vec![],
        reward_effects: vec![],
    })?)
}

fn require_restricted_source_plan(
    source_plan: &SettlementEffectPlanV2,
) -> Result<(), SpotSettlementV7EffectBindingErrorV1> {
    source_plan.validate_self_consistency()?;
    if source_plan.economic_action_batch().actions().len() != 1 {
        return Err(SpotSettlementV7EffectBindingErrorV1::ExpectedSingletonAction);
    }
    if source_plan.ledger_cell_writes().len() != 1 {
        return Err(SpotSettlementV7EffectBindingErrorV1::SourcePlanProfile(
            "one opaque cell write",
        ));
    }
    let [source_effect] = source_plan.asset_effects() else {
        return Err(SpotSettlementV7EffectBindingErrorV1::SourcePlanProfile(
            "one ordinary asset effect",
        ));
    };
    if source_effect.kind() != AssetEffectKindV2::OrdinaryTransfer {
        return Err(SpotSettlementV7EffectBindingErrorV1::SourcePlanProfile(
            "ordinary asset effect",
        ));
    }
    if !source_plan.message_effects().is_empty()
        || !source_plan.carry_effects().is_empty()
        || !source_plan.reward_effects().is_empty()
    {
        return Err(SpotSettlementV7EffectBindingErrorV1::UnsupportedOperationalEffects);
    }
    Ok(())
}

fn derived_consumed_object_lineage(
    source_objects: &[CommitmentV3],
    source_journal_commitment: CommitmentV3,
    source_plan_commitment: CommitmentV3,
) -> Vec<CommitmentV3> {
    source_objects
        .iter()
        .copied()
        .chain([source_journal_commitment, source_plan_commitment])
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn bind_derived_plan(
    opening: SpotSettlementStateEffectOpeningV1,
    plan: SettlementEffectPlanV2,
    source_plan_commitment: CommitmentV3,
) -> Result<BoundSpotSettlementStateV1, SpotSettlementV7EffectBindingErrorV1> {
    plan.validate_self_consistency()?;
    if plan.source_semantic_journal_hash() != opening.source_journal_commitment() {
        return Err(SpotSettlementV7EffectBindingErrorV1::SourceJournalMismatch);
    }
    if plan.economic_action_batch().pre_state_root() != opening.pre_state_root() {
        return Err(SpotSettlementV7EffectBindingErrorV1::PreStateRootMismatch);
    }
    if plan.post_state_root() != opening.post_state_root() {
        return Err(SpotSettlementV7EffectBindingErrorV1::PostStateRootMismatch);
    }
    let [action] = plan.economic_action_batch().actions() else {
        return Err(SpotSettlementV7EffectBindingErrorV1::ExpectedSingletonAction);
    };
    if action.record().authorization_nonce() != u64::from(opening.ingress_nonce()) {
        return Err(SpotSettlementV7EffectBindingErrorV1::ActionNonceMismatch);
    }
    if action.record().action_semantics_hash() != opening.action_semantics_hash() {
        return Err(SpotSettlementV7EffectBindingErrorV1::ActionSemanticsMismatch);
    }
    if action.record().effect_commitment() != opening.effect_commitment() {
        return Err(SpotSettlementV7EffectBindingErrorV1::EffectCommitmentMismatch);
    }
    let action_id = action.action_id()?;
    require_exact_cell_writes(&opening, &plan, action_id)?;
    require_exact_asset_effects(&opening, &plan, action_id)?;
    if !plan.message_effects().is_empty()
        || !plan.carry_effects().is_empty()
        || !plan.reward_effects().is_empty()
    {
        return Err(SpotSettlementV7EffectBindingErrorV1::UnsupportedOperationalEffects);
    }
    let journal =
        SpotSettlementV7EffectBindingJournalV1::new(SpotSettlementV7EffectBindingJournalInputV1 {
            compatibility_profile_id: opening.compatibility_profile_id(),
            state_root_scheme_id: opening.state_root_scheme_id(),
            source_journal_commitment: opening.source_journal_commitment(),
            source_settlement_plan_commitment: source_plan_commitment,
            settlement_effect_plan_commitment: plan.canonical_commitment()?,
            cell_transitions_root: opening.cell_transitions_root(),
            pre_state_root: opening.pre_state_root(),
            post_state_root: opening.post_state_root(),
            economic_action_id: action_id,
            action_semantics_hash: opening.action_semantics_hash(),
            effect_commitment: opening.effect_commitment(),
            public_policy_hash: plan.public_policy_hash(),
        })?;
    Ok(BoundSpotSettlementStateV1 {
        opening,
        plan,
        journal,
    })
}

fn require_exact_cell_writes(
    opening: &SpotSettlementStateEffectOpeningV1,
    plan: &SettlementEffectPlanV2,
    action_id: EconomicActionIdV1,
) -> Result<(), SpotSettlementV7EffectBindingErrorV1> {
    if plan.ledger_cell_writes() != opening.expected_cell_writes(action_id)?.as_slice() {
        return Err(SpotSettlementV7EffectBindingErrorV1::CellWritesMismatch);
    }
    Ok(())
}

fn require_exact_asset_effects(
    opening: &SpotSettlementStateEffectOpeningV1,
    plan: &SettlementEffectPlanV2,
    action_id: EconomicActionIdV1,
) -> Result<(), SpotSettlementV7EffectBindingErrorV1> {
    if plan.asset_effects() != opening.expected_asset_effects(action_id)?.as_slice() {
        return Err(SpotSettlementV7EffectBindingErrorV1::AssetEffectsMismatch);
    }
    Ok(())
}
