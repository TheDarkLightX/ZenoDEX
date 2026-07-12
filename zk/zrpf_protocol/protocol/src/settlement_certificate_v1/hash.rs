use sha2::{Digest, Sha256};

use super::{SettlementEpochCertificateErrorV1, SettlementEpochCertificateV1};
use crate::CommitmentV3;

const SETTLEMENT_CERTIFICATE_JOURNAL_HASH_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.settlement_epoch_certificate_journal.v1";

pub(super) fn derive_settlement_certificate_journal_hash_v1(
    certificate: &SettlementEpochCertificateV1,
) -> Result<CommitmentV3, SettlementEpochCertificateErrorV1> {
    let mut hasher = domain_hasher(SETTLEMENT_CERTIFICATE_JOURNAL_HASH_DOMAIN_V1)?;
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
        update_commitment(&mut hasher, root);
    }
    let semantic_root = certificate.semantic_root();
    hasher.update([semantic_root.hash_tag()]);
    update_commitment(&mut hasher, semantic_root.root());
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
        update_commitment(&mut hasher, root);
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| SettlementEpochCertificateErrorV1::InvalidDerivedCommitment("journal_hash"))
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, SettlementEpochCertificateErrorV1> {
    let length = u16::try_from(domain.len()).map_err(|_| {
        SettlementEpochCertificateErrorV1::ArithmeticOverflow("journal_hash_domain")
    })?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn update_commitment(hasher: &mut Sha256, value: CommitmentV3) {
    hasher.update(value.as_bytes());
}
