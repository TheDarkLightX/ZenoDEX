use alloc::vec::Vec;

use super::{
    SettlementEpochCertificateErrorV1, SettlementEpochCertificateV1,
    MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1,
};

pub fn encode_settlement_epoch_certificate_v1(
    certificate: &SettlementEpochCertificateV1,
) -> Result<Vec<u8>, SettlementEpochCertificateErrorV1> {
    certificate.validate()?;
    let bytes = postcard::to_allocvec(certificate)
        .map_err(|_| SettlementEpochCertificateErrorV1::PostcardDecode)?;
    require_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_settlement_epoch_certificate_v1(
    bytes: &[u8],
) -> Result<SettlementEpochCertificateV1, SettlementEpochCertificateErrorV1> {
    require_size(bytes.len())?;
    let (certificate, remainder) = postcard::take_from_bytes::<SettlementEpochCertificateV1>(bytes)
        .map_err(|_| SettlementEpochCertificateErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(SettlementEpochCertificateErrorV1::TrailingBytes);
    }
    if encode_settlement_epoch_certificate_v1(&certificate)?.as_slice() != bytes {
        return Err(SettlementEpochCertificateErrorV1::NonCanonicalEncoding);
    }
    Ok(certificate)
}

fn require_size(size: usize) -> Result<(), SettlementEpochCertificateErrorV1> {
    if size == 0 {
        return Err(SettlementEpochCertificateErrorV1::EmptyInput);
    }
    if size > MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1 {
        return Err(SettlementEpochCertificateErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1,
        });
    }
    Ok(())
}
