use sha2::{Digest, Sha256};

use super::{CheckpointFinalityCertificateErrorV2, CheckpointFinalityCertificateInputV2};
use crate::CommitmentV3;

const CERTIFICATE_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.checkpoint_finality.certificate_root.v2";

pub(super) fn derive_checkpoint_finality_certificate_root_v2(
    input: &CheckpointFinalityCertificateInputV2,
) -> Result<CommitmentV3, CheckpointFinalityCertificateErrorV2> {
    let mut hasher = domain_hasher(CERTIFICATE_ROOT_DOMAIN_V2)?;
    hasher.update(super::CHECKPOINT_FINALITY_CERTIFICATE_VERSION_V2.to_be_bytes());
    hasher.update(input.application_id.as_bytes());
    hasher.update(input.chain_or_domain_id.as_bytes());
    hasher.update(input.epoch_id.to_be_bytes());
    hasher.update(input.proof_journal_hash.as_bytes());
    hasher.update(input.post_state_root.as_bytes());
    hasher.update(input.application_checkpoint_sequence.to_be_bytes());
    hasher.update(input.application_checkpoint_hash.as_bytes());
    hasher.update(input.parent_application_checkpoint_hash.as_bytes());
    hasher.update(input.finality_network_id.as_bytes());
    hasher.update(input.finality_protocol_id.as_bytes());
    hasher.update(input.external_finality_policy_hash.as_bytes());
    hasher.update(input.finality_verifier_set_root.as_bytes());
    hasher.update(input.finality_evidence_root.as_bytes());
    hasher.update(input.finality_policy_root.as_bytes());
    CommitmentV3::new(hasher.finalize().into()).map_err(|_| {
        CheckpointFinalityCertificateErrorV2::InvalidDerivedCommitment("certificate_root")
    })
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, CheckpointFinalityCertificateErrorV2> {
    let length = u16::try_from(domain.len())
        .map_err(|_| CheckpointFinalityCertificateErrorV2::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}
