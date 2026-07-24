use sha2::{Digest, Sha256};

use super::SettlementAdmissionJournalErrorV1;
use crate::CommitmentV3;

const SETTLEMENT_CERTIFICATE_ID_DOMAIN_V1: &[u8] = b"zenodex.zrpf.settlement_certificate_id.v1";

pub(super) fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

pub(super) fn derive_settlement_certificate_id_v1(
    certificate_bytes: &[u8],
) -> Result<CommitmentV3, SettlementAdmissionJournalErrorV1> {
    let domain_len = u16::try_from(SETTLEMENT_CERTIFICATE_ID_DOMAIN_V1.len()).map_err(|_| {
        SettlementAdmissionJournalErrorV1::ArithmeticOverflow("certificate_id_domain")
    })?;
    let certificate_len = u32::try_from(certificate_bytes.len())
        .map_err(|_| SettlementAdmissionJournalErrorV1::ArithmeticOverflow("certificate_bytes"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_len.to_be_bytes());
    hasher.update(SETTLEMENT_CERTIFICATE_ID_DOMAIN_V1);
    hasher.update(certificate_len.to_be_bytes());
    hasher.update(certificate_bytes);
    CommitmentV3::new(hasher.finalize().into()).map_err(|_| {
        SettlementAdmissionJournalErrorV1::InvalidDerivedCommitment("settlement_certificate_id")
    })
}
