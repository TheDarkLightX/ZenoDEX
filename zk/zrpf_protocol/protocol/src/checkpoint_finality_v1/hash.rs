use sha2::{Digest, Sha256};

use super::{CheckpointFinalityCertificateErrorV1, CheckpointFinalityCertificateV1};
use crate::CommitmentV3;

const CERTIFICATE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.checkpoint_finality.certificate_root.v1";

pub(super) fn derive_checkpoint_finality_certificate_root_v1(
    certificate: &CheckpointFinalityCertificateV1,
) -> Result<CommitmentV3, CheckpointFinalityCertificateErrorV1> {
    let mut hasher = domain_hasher(CERTIFICATE_ROOT_DOMAIN_V1)?;
    hasher.update(certificate.certificate_version().to_be_bytes());
    hasher.update(certificate.application_id().as_bytes());
    hasher.update(certificate.chain_or_domain_id().as_bytes());
    hasher.update(certificate.epoch_id().to_be_bytes());
    hasher.update(certificate.proof_journal_hash().as_bytes());
    hasher.update(certificate.post_state_root().as_bytes());
    hasher.update(certificate.checkpoint_height().to_be_bytes());
    hasher.update(certificate.checkpoint_hash().as_bytes());
    hasher.update(certificate.finality_network_id().as_bytes());
    hasher.update(certificate.finality_protocol_id().as_bytes());
    hasher.update(certificate.external_finality_policy_hash().as_bytes());
    hasher.update(certificate.finality_verifier_set_root().as_bytes());
    hasher.update(certificate.finality_evidence_root().as_bytes());
    hasher.update(certificate.finality_policy_root().as_bytes());
    commitment(hasher, "certificate_root")
}

fn domain_hasher(domain: &[u8]) -> Result<Sha256, CheckpointFinalityCertificateErrorV1> {
    let length = u16::try_from(domain.len())
        .map_err(|_| CheckpointFinalityCertificateErrorV1::ArithmeticOverflow("hash_domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(domain);
    Ok(hasher)
}

fn commitment(
    hasher: Sha256,
    field: &'static str,
) -> Result<CommitmentV3, CheckpointFinalityCertificateErrorV1> {
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| CheckpointFinalityCertificateErrorV1::InvalidDerivedCommitment(field))
}
