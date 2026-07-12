use alloc::vec::Vec;

use super::hash::{derive_settlement_certificate_id_v1, sha256};
use super::SettlementAdmissionJournalErrorV1;
use crate::{
    decode_exact_settlement_effect_plan_v2, decode_exact_settlement_epoch_certificate_v1,
    encode_settlement_effect_plan_v2, encode_settlement_epoch_certificate_v1, ApplicationIdV3,
    CommitmentV3, DomainIdV3, ProfileIdV3, SettlementEffectPlanV2, SettlementEpochCertificateV1,
    SettlementSemanticRootV1,
};

/// Proof-neutral, cross-language admission projection of one exact certificate
/// and its complete effect-plan opening.
///
/// Every field is derived from the two validated inner objects. This type does
/// not authenticate a RISC0 receipt, authorize ledger mutation, or attest data
/// availability. A sealed verifier and an atomic admission store remain
/// separate authority boundaries.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::SettlementAdmissionJournalV1;
/// let journal: SettlementAdmissionJournalV1 = unimplemented!();
/// let _ = journal.settlement_receipt_id();
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SettlementAdmissionJournalV1 {
    journal_version: u16,
    certificate_bytes: Vec<u8>,
    effect_plan_bytes: Vec<u8>,
    certificate_sha256: [u8; 32],
    effect_plan_sha256: [u8; 32],
    certificate_version: u16,
    effect_plan_version: u16,
    application_id: ApplicationIdV3,
    chain_or_domain_id: DomainIdV3,
    epoch_id: u64,
    semantic_profile_id: ProfileIdV3,
    semantic_journal_hash: CommitmentV3,
    semantic_claim_binding: CommitmentV3,
    proof_tree_root: CommitmentV3,
    semantic_root: SettlementSemanticRootV1,
    dependency_manifest_root: CommitmentV3,
    public_policy_hash: CommitmentV3,
    economic_action_batch_commitment: CommitmentV3,
    settlement_effect_plan_commitment: CommitmentV3,
    economic_action_ids_root: CommitmentV3,
    action_authorization_bindings_root: CommitmentV3,
    authorization_grant_spends_root: CommitmentV3,
    consumed_object_ids_root: CommitmentV3,
    action_count: u32,
    consumed_object_count: u32,
    pre_state_root: CommitmentV3,
    post_state_root: CommitmentV3,
    cell_writes_root: CommitmentV3,
    asset_effects_root: CommitmentV3,
    messages_root: CommitmentV3,
    carries_root: CommitmentV3,
    rewards_root: CommitmentV3,
    data_availability_certificate_root: CommitmentV3,
    schedule_certificate_root: CommitmentV3,
    carry_continuity_certificate_root: CommitmentV3,
    settlement_certificate_id: CommitmentV3,
    certificate_commitment: CommitmentV3,
}

impl SettlementAdmissionJournalV1 {
    pub fn derive(
        certificate: &SettlementEpochCertificateV1,
        effect_plan: &SettlementEffectPlanV2,
    ) -> Result<Self, SettlementAdmissionJournalErrorV1> {
        certificate.validate()?;
        effect_plan.validate_self_consistency()?;
        validate_certificate_plan_association(certificate, effect_plan)?;

        let certificate_bytes = encode_settlement_epoch_certificate_v1(certificate)?;
        let effect_plan_bytes = encode_settlement_effect_plan_v2(effect_plan)?;
        let batch = effect_plan.economic_action_batch();
        let action_count = u32::try_from(batch.actions().len())
            .map_err(|_| SettlementAdmissionJournalErrorV1::ArithmeticOverflow("action_count"))?;
        let consumed_object_count = count_consumed_objects(effect_plan)?;

        Ok(Self {
            journal_version: super::SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1,
            certificate_sha256: sha256(&certificate_bytes),
            effect_plan_sha256: sha256(&effect_plan_bytes),
            certificate_version: certificate.certificate_version(),
            effect_plan_version: effect_plan.plan_version(),
            application_id: certificate.application_id(),
            chain_or_domain_id: certificate.chain_or_domain_id(),
            epoch_id: certificate.epoch_id(),
            semantic_profile_id: certificate.semantic_profile_id(),
            semantic_journal_hash: certificate.semantic_journal_hash(),
            semantic_claim_binding: certificate.semantic_claim_binding(),
            proof_tree_root: certificate.proof_tree_root(),
            semantic_root: certificate.semantic_root(),
            dependency_manifest_root: certificate.dependency_manifest_root(),
            public_policy_hash: certificate.public_policy_hash(),
            economic_action_batch_commitment: certificate.economic_action_batch_commitment(),
            settlement_effect_plan_commitment: certificate.settlement_effect_plan_commitment(),
            economic_action_ids_root: certificate.economic_action_ids_root(),
            action_authorization_bindings_root: certificate.action_authorization_bindings_root(),
            authorization_grant_spends_root: certificate.authorization_grant_spends_root(),
            consumed_object_ids_root: certificate.consumed_object_ids_root(),
            action_count,
            consumed_object_count,
            pre_state_root: certificate.pre_state_root(),
            post_state_root: certificate.post_state_root(),
            cell_writes_root: certificate.cell_writes_root(),
            asset_effects_root: certificate.asset_effects_root(),
            messages_root: certificate.messages_root(),
            carries_root: certificate.carries_root(),
            rewards_root: certificate.rewards_root(),
            data_availability_certificate_root: certificate.data_availability_certificate_root(),
            schedule_certificate_root: certificate.schedule_certificate_root(),
            carry_continuity_certificate_root: certificate.carry_continuity_certificate_root(),
            settlement_certificate_id: derive_settlement_certificate_id_v1(&certificate_bytes)?,
            certificate_commitment: certificate.canonical_journal_hash()?,
            certificate_bytes,
            effect_plan_bytes,
        })
    }

    pub fn validate_self_consistency(&self) -> Result<(), SettlementAdmissionJournalErrorV1> {
        let certificate = decode_exact_settlement_epoch_certificate_v1(&self.certificate_bytes)?;
        let effect_plan = decode_exact_settlement_effect_plan_v2(&self.effect_plan_bytes)?;
        if Self::derive(&certificate, &effect_plan)? != *self {
            return Err(SettlementAdmissionJournalErrorV1::DuplicatedFieldMismatch);
        }
        Ok(())
    }

    pub const fn journal_version(&self) -> u16 {
        self.journal_version
    }

    pub fn certificate_bytes(&self) -> &[u8] {
        &self.certificate_bytes
    }

    pub fn effect_plan_bytes(&self) -> &[u8] {
        &self.effect_plan_bytes
    }

    pub const fn certificate_sha256(&self) -> [u8; 32] {
        self.certificate_sha256
    }

    pub const fn effect_plan_sha256(&self) -> [u8; 32] {
        self.effect_plan_sha256
    }

    pub const fn certificate_version(&self) -> u16 {
        self.certificate_version
    }

    pub const fn effect_plan_version(&self) -> u16 {
        self.effect_plan_version
    }

    pub const fn application_id(&self) -> ApplicationIdV3 {
        self.application_id
    }

    pub const fn chain_or_domain_id(&self) -> DomainIdV3 {
        self.chain_or_domain_id
    }

    pub const fn epoch_id(&self) -> u64 {
        self.epoch_id
    }

    pub const fn semantic_profile_id(&self) -> ProfileIdV3 {
        self.semantic_profile_id
    }

    pub const fn semantic_journal_hash(&self) -> CommitmentV3 {
        self.semantic_journal_hash
    }

    pub const fn semantic_claim_binding(&self) -> CommitmentV3 {
        self.semantic_claim_binding
    }

    pub const fn proof_tree_root(&self) -> CommitmentV3 {
        self.proof_tree_root
    }

    pub const fn semantic_root(&self) -> SettlementSemanticRootV1 {
        self.semantic_root
    }

    pub const fn dependency_manifest_root(&self) -> CommitmentV3 {
        self.dependency_manifest_root
    }

    pub const fn public_policy_hash(&self) -> CommitmentV3 {
        self.public_policy_hash
    }

    pub const fn economic_action_batch_commitment(&self) -> CommitmentV3 {
        self.economic_action_batch_commitment
    }

    pub const fn settlement_effect_plan_commitment(&self) -> CommitmentV3 {
        self.settlement_effect_plan_commitment
    }

    pub const fn economic_action_ids_root(&self) -> CommitmentV3 {
        self.economic_action_ids_root
    }

    pub const fn action_authorization_bindings_root(&self) -> CommitmentV3 {
        self.action_authorization_bindings_root
    }

    pub const fn authorization_grant_spends_root(&self) -> CommitmentV3 {
        self.authorization_grant_spends_root
    }

    pub const fn consumed_object_ids_root(&self) -> CommitmentV3 {
        self.consumed_object_ids_root
    }

    pub const fn action_count(&self) -> u32 {
        self.action_count
    }

    pub const fn consumed_object_count(&self) -> u32 {
        self.consumed_object_count
    }

    pub const fn pre_state_root(&self) -> CommitmentV3 {
        self.pre_state_root
    }

    pub const fn post_state_root(&self) -> CommitmentV3 {
        self.post_state_root
    }

    pub const fn cell_writes_root(&self) -> CommitmentV3 {
        self.cell_writes_root
    }

    pub const fn asset_effects_root(&self) -> CommitmentV3 {
        self.asset_effects_root
    }

    pub const fn messages_root(&self) -> CommitmentV3 {
        self.messages_root
    }

    pub const fn carries_root(&self) -> CommitmentV3 {
        self.carries_root
    }

    pub const fn rewards_root(&self) -> CommitmentV3 {
        self.rewards_root
    }

    pub const fn data_availability_certificate_root(&self) -> CommitmentV3 {
        self.data_availability_certificate_root
    }

    pub const fn schedule_certificate_root(&self) -> CommitmentV3 {
        self.schedule_certificate_root
    }

    pub const fn carry_continuity_certificate_root(&self) -> CommitmentV3 {
        self.carry_continuity_certificate_root
    }

    pub const fn settlement_certificate_id(&self) -> CommitmentV3 {
        self.settlement_certificate_id
    }

    pub const fn certificate_commitment(&self) -> CommitmentV3 {
        self.certificate_commitment
    }
}

fn validate_certificate_plan_association(
    certificate: &SettlementEpochCertificateV1,
    effect_plan: &SettlementEffectPlanV2,
) -> Result<(), SettlementAdmissionJournalErrorV1> {
    validate_certificate_plan_scope(certificate, effect_plan)?;
    validate_certificate_action_batch(certificate, effect_plan)?;
    validate_certificate_effect_roots(certificate, effect_plan)
}

fn validate_certificate_plan_scope(
    certificate: &SettlementEpochCertificateV1,
    effect_plan: &SettlementEffectPlanV2,
) -> Result<(), SettlementAdmissionJournalErrorV1> {
    let batch = effect_plan.economic_action_batch();
    require_equal(
        "application_id",
        certificate.application_id(),
        batch.application_id(),
    )?;
    require_equal(
        "chain_or_domain_id",
        certificate.chain_or_domain_id(),
        batch.chain_or_domain_id(),
    )?;
    require_equal("epoch_id", certificate.epoch_id(), batch.epoch_id())?;
    require_equal(
        "semantic_journal_hash",
        certificate.semantic_journal_hash(),
        effect_plan.source_semantic_journal_hash(),
    )
}

fn validate_certificate_action_batch(
    certificate: &SettlementEpochCertificateV1,
    effect_plan: &SettlementEffectPlanV2,
) -> Result<(), SettlementAdmissionJournalErrorV1> {
    let batch = effect_plan.economic_action_batch();
    require_equal(
        "economic_action_batch_commitment",
        certificate.economic_action_batch_commitment(),
        batch
            .canonical_commitment()
            .map_err(crate::SettlementEffectErrorV2::from)?,
    )?;
    require_equal(
        "economic_action_ids_root",
        certificate.economic_action_ids_root(),
        batch.action_ids_root(),
    )?;
    require_equal(
        "action_authorization_bindings_root",
        certificate.action_authorization_bindings_root(),
        batch.action_authorization_bindings_root(),
    )?;
    require_equal(
        "authorization_grant_spends_root",
        certificate.authorization_grant_spends_root(),
        batch.authorization_grant_spends_root(),
    )?;
    require_equal(
        "consumed_object_ids_root",
        certificate.consumed_object_ids_root(),
        batch.consumed_object_ids_root(),
    )?;
    require_equal(
        "settlement_effect_plan_commitment",
        certificate.settlement_effect_plan_commitment(),
        effect_plan.canonical_commitment()?,
    )
}

fn validate_certificate_effect_roots(
    certificate: &SettlementEpochCertificateV1,
    effect_plan: &SettlementEffectPlanV2,
) -> Result<(), SettlementAdmissionJournalErrorV1> {
    let batch = effect_plan.economic_action_batch();
    for (field, certificate_root, plan_root) in [
        (
            "pre_state_root",
            certificate.pre_state_root(),
            batch.pre_state_root(),
        ),
        (
            "post_state_root",
            certificate.post_state_root(),
            effect_plan.post_state_root(),
        ),
        (
            "cell_writes_root",
            certificate.cell_writes_root(),
            effect_plan.cell_writes_root(),
        ),
        (
            "asset_effects_root",
            certificate.asset_effects_root(),
            effect_plan.asset_effects_root(),
        ),
        (
            "messages_root",
            certificate.messages_root(),
            effect_plan.message_effects_root(),
        ),
        (
            "carries_root",
            certificate.carries_root(),
            effect_plan.carry_effects_root(),
        ),
        (
            "rewards_root",
            certificate.rewards_root(),
            effect_plan.reward_effects_root(),
        ),
        (
            "public_policy_hash",
            certificate.public_policy_hash(),
            effect_plan.public_policy_hash(),
        ),
    ] {
        require_equal(field, certificate_root, plan_root)?;
    }
    Ok(())
}

fn count_consumed_objects(
    effect_plan: &SettlementEffectPlanV2,
) -> Result<u32, SettlementAdmissionJournalErrorV1> {
    let count = effect_plan
        .economic_action_batch()
        .actions()
        .iter()
        .try_fold(0usize, |count, action| {
            count.checked_add(action.record().consumed_object_ids().len())
        })
        .ok_or(SettlementAdmissionJournalErrorV1::ArithmeticOverflow(
            "consumed_object_count",
        ))?;
    u32::try_from(count)
        .map_err(|_| SettlementAdmissionJournalErrorV1::ArithmeticOverflow("consumed_object_count"))
}

fn require_equal<T: PartialEq>(
    field: &'static str,
    actual: T,
    expected: T,
) -> Result<(), SettlementAdmissionJournalErrorV1> {
    if actual != expected {
        return Err(SettlementAdmissionJournalErrorV1::CertificatePlanMismatch(
            field,
        ));
    }
    Ok(())
}
