use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, FullBlobDataAvailabilityCertificateV1, ProposedValueAggregateV5,
    SettlementEffectPlanV2, SettlementEpochCertificateV1,
};

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

pub fn independent_schedule_root(
    proposal: &ProposedValueAggregateV5,
    plan: &SettlementEffectPlanV2,
) -> CommitmentV3 {
    let batch = plan.economic_action_batch();
    let mut hasher = domain_hasher(b"zenodex.zrpf.ordinary_spot_schedule_certificate.v1");
    hasher.update(1_u16.to_be_bytes());
    hasher.update(
        proposal
            .operational_commitments()
            .conflict_schedule_root()
            .as_bytes(),
    );
    hasher.update(u16::try_from(batch.actions().len()).unwrap().to_be_bytes());
    for action in batch.actions() {
        hasher.update(action.action_id().unwrap().as_bytes());
    }
    hasher.update(batch.canonical_commitment().unwrap().as_bytes());
    hasher.update(plan.canonical_commitment().unwrap().as_bytes());
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}

pub fn independent_da_certificate_root(
    certificate: &FullBlobDataAvailabilityCertificateV1,
) -> [u8; 32] {
    let mut hasher = domain_hasher(b"zenodex.zrpf.full_blob_da.certificate_root.v1");
    hasher.update(certificate.certificate_version().to_be_bytes());
    hasher.update(certificate.application_id().as_bytes());
    hasher.update(certificate.chain_or_domain_id().as_bytes());
    hasher.update(certificate.epoch_id().to_be_bytes());
    hasher.update(certificate.data_schema_id().as_bytes());
    hasher.update(certificate.data_root().as_bytes());
    hasher.update(certificate.blob_length().to_be_bytes());
    hasher.update(certificate.chunk_size().to_be_bytes());
    hasher.update(certificate.chunk_count().to_be_bytes());
    hasher.update(certificate.chunk_root().as_bytes());
    hasher.update(certificate.retention_through_epoch().to_be_bytes());
    hasher.update(certificate.storage_policy_hash().as_bytes());
    hasher.finalize().into()
}

pub fn independent_journal_hash(certificate: &SettlementEpochCertificateV1) -> CommitmentV3 {
    let mut hasher = domain_hasher(b"zenodex.zrpf.settlement_epoch_certificate_journal.v1");
    hasher.update(certificate.certificate_version().to_be_bytes());
    hasher.update(certificate.application_id().as_bytes());
    hasher.update(certificate.chain_or_domain_id().as_bytes());
    hasher.update(certificate.epoch_id().to_be_bytes());
    hasher.update(certificate.semantic_profile_id().as_bytes());
    for root in [
        certificate.semantic_journal_hash(),
        certificate.semantic_claim_binding(),
        certificate.proof_tree_root(),
    ] {
        hasher.update(root.as_bytes());
    }
    hasher.update([1]);
    hasher.update(certificate.semantic_root().root().as_bytes());
    for root in [
        certificate.economic_action_batch_commitment(),
        certificate.economic_action_ids_root(),
        certificate.action_authorization_bindings_root(),
        certificate.authorization_grant_spends_root(),
        certificate.consumed_object_ids_root(),
        certificate.settlement_effect_plan_commitment(),
        certificate.pre_state_root(),
        certificate.post_state_root(),
        certificate.cell_writes_root(),
        certificate.asset_effects_root(),
        certificate.messages_root(),
        certificate.carries_root(),
        certificate.rewards_root(),
        certificate.public_policy_hash(),
        certificate.data_availability_certificate_root(),
        certificate.schedule_certificate_root(),
        certificate.carry_continuity_certificate_root(),
        certificate.dependency_manifest_root(),
    ] {
        hasher.update(root.as_bytes());
    }
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}
