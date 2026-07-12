use zenodex_zrpf_protocol_v3::{
    CommitmentV3, ProfileIdV3, ProposedValueAggregateV5, SettlementEffectPlanV2,
    SettlementEpochCertificateInputV1, SettlementEpochCertificateV1, SettlementSemanticRootV1,
    SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
};

mod error;
mod hash;

pub use error::OrdinarySpotSettlementCertificateErrorV1;

use hash::{
    derive_empty_carry_continuity_root_v1, derive_proof_tree_root_v1, derive_schedule_root_v1,
};

use crate::{
    derive_spot_settlement_projection_v1, SpotSettlementAuthorizationInputV1,
    SpotSettlementProjectionV1,
};

/// Recomposes one proof-neutral ordinary Spot settlement certificate.
///
/// The caller proposes only the semantic claim binding and DA certificate root.
/// This function derives every other settlement field from the exact checked V5
/// proposal and authorization. It supplies no receipt or ledger authority.
pub fn compose_ordinary_spot_settlement_certificate_v1(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    semantic_claim_binding: CommitmentV3,
    data_availability_certificate_root: CommitmentV3,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    let projection = derive_spot_settlement_projection_v1(proposal, authorization)?;
    let plan = projection.settlement_plan();
    plan.validate_self_consistency()?;
    require_projection_plan_association(&projection)?;
    require_empty_ordinary_rows(
        plan.message_effects().len(),
        plan.carry_effects().len(),
        plan.reward_effects().len(),
    )?;

    let proof_tree_root = derive_proof_tree_root_v1(proposal)?;
    let schedule_certificate_root = derive_schedule_root_v1(plan.economic_action_batch(), plan)?;
    let carry_continuity_certificate_root = derive_empty_carry_continuity_root_v1(plan)?;
    let semantic_profile_id =
        ProfileIdV3::new(proposal.semantic_subtree().value_profile_id().into_bytes())?;
    let fields = CertificateCompositionFieldsV1 {
        semantic_profile_id,
        semantic_claim_binding,
        data_availability_certificate_root,
        proof_tree_root,
        schedule_certificate_root,
        carry_continuity_certificate_root,
    };

    compose_checked_certificate(proposal, plan, fields)
}

#[derive(Clone, Copy)]
struct CertificateCompositionFieldsV1 {
    semantic_profile_id: ProfileIdV3,
    semantic_claim_binding: CommitmentV3,
    data_availability_certificate_root: CommitmentV3,
    proof_tree_root: CommitmentV3,
    schedule_certificate_root: CommitmentV3,
    carry_continuity_certificate_root: CommitmentV3,
}

fn compose_checked_certificate(
    proposal: &ProposedValueAggregateV5,
    plan: &SettlementEffectPlanV2,
    fields: CertificateCompositionFieldsV1,
) -> Result<SettlementEpochCertificateV1, OrdinarySpotSettlementCertificateErrorV1> {
    let batch = plan.economic_action_batch();
    Ok(SettlementEpochCertificateV1::new(
        SettlementEpochCertificateInputV1 {
            certificate_version: SETTLEMENT_EPOCH_CERTIFICATE_VERSION_V1,
            application_id: batch.application_id(),
            chain_or_domain_id: batch.chain_or_domain_id(),
            epoch_id: batch.epoch_id(),
            semantic_profile_id: fields.semantic_profile_id,
            semantic_journal_hash: plan.source_semantic_journal_hash(),
            semantic_claim_binding: fields.semantic_claim_binding,
            proof_tree_root: fields.proof_tree_root,
            semantic_root: SettlementSemanticRootV1::ValueSubtree(
                proposal.semantic_subtree().value_subtree_root(),
            ),
            economic_action_batch_commitment: batch.canonical_commitment()?,
            economic_action_ids_root: batch.action_ids_root(),
            action_authorization_bindings_root: batch.action_authorization_bindings_root(),
            authorization_grant_spends_root: batch.authorization_grant_spends_root(),
            consumed_object_ids_root: batch.consumed_object_ids_root(),
            settlement_effect_plan_commitment: plan.canonical_commitment()?,
            pre_state_root: batch.pre_state_root(),
            post_state_root: plan.post_state_root(),
            cell_writes_root: plan.cell_writes_root(),
            asset_effects_root: plan.asset_effects_root(),
            messages_root: plan.message_effects_root(),
            carries_root: plan.carry_effects_root(),
            rewards_root: plan.reward_effects_root(),
            public_policy_hash: plan.public_policy_hash(),
            data_availability_certificate_root: fields.data_availability_certificate_root,
            schedule_certificate_root: fields.schedule_certificate_root,
            carry_continuity_certificate_root: fields.carry_continuity_certificate_root,
            dependency_manifest_root: proposal.dependency_manifest_root(),
        },
    )?)
}

fn require_projection_plan_association(
    projection: &SpotSettlementProjectionV1,
) -> Result<(), OrdinarySpotSettlementCertificateErrorV1> {
    let plan = projection.settlement_plan();
    if projection.action_batch() != plan.economic_action_batch() {
        return Err(OrdinarySpotSettlementCertificateErrorV1::ProjectionBatchMismatch);
    }
    if projection.source_semantic_journal_hash() != plan.source_semantic_journal_hash() {
        return Err(OrdinarySpotSettlementCertificateErrorV1::ProjectionSourceHashMismatch);
    }
    Ok(())
}

fn require_empty_ordinary_rows(
    message_count: usize,
    carry_count: usize,
    reward_count: usize,
) -> Result<(), OrdinarySpotSettlementCertificateErrorV1> {
    if message_count != 0 {
        return Err(
            OrdinarySpotSettlementCertificateErrorV1::NonEmptyMessageEffects {
                actual: message_count,
            },
        );
    }
    if carry_count != 0 {
        return Err(
            OrdinarySpotSettlementCertificateErrorV1::NonEmptyCarryEffects {
                actual: carry_count,
            },
        );
    }
    if reward_count != 0 {
        return Err(
            OrdinarySpotSettlementCertificateErrorV1::NonEmptyRewardEffects {
                actual: reward_count,
            },
        );
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{require_empty_ordinary_rows, OrdinarySpotSettlementCertificateErrorV1};

    #[test]
    fn nonempty_ordinary_rows_reject_in_message_carry_reward_order() {
        assert_eq!(
            require_empty_ordinary_rows(3, 2, 1).unwrap_err(),
            OrdinarySpotSettlementCertificateErrorV1::NonEmptyMessageEffects { actual: 3 }
        );
        assert_eq!(
            require_empty_ordinary_rows(0, 2, 1).unwrap_err(),
            OrdinarySpotSettlementCertificateErrorV1::NonEmptyCarryEffects { actual: 2 }
        );
        assert_eq!(
            require_empty_ordinary_rows(0, 0, 1).unwrap_err(),
            OrdinarySpotSettlementCertificateErrorV1::NonEmptyRewardEffects { actual: 1 }
        );
        assert_eq!(require_empty_ordinary_rows(0, 0, 0), Ok(()));
    }
}
