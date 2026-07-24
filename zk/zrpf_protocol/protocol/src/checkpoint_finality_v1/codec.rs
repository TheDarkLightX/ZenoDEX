use alloc::vec::Vec;

use super::{
    CheckpointFinalityCertificateErrorV1, CheckpointFinalityCertificateV1,
    MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V1,
};

pub fn encode_checkpoint_finality_certificate_v1(
    certificate: &CheckpointFinalityCertificateV1,
) -> Result<Vec<u8>, CheckpointFinalityCertificateErrorV1> {
    certificate.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(certificate)
        .map_err(|_| CheckpointFinalityCertificateErrorV1::PostcardDecode)?;
    require_input_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_checkpoint_finality_certificate_v1(
    bytes: &[u8],
) -> Result<CheckpointFinalityCertificateV1, CheckpointFinalityCertificateErrorV1> {
    require_input_size(bytes.len())?;
    let (certificate, remainder) =
        postcard::take_from_bytes::<CheckpointFinalityCertificateV1>(bytes)
            .map_err(|_| CheckpointFinalityCertificateErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(CheckpointFinalityCertificateErrorV1::TrailingBytes);
    }
    if encode_checkpoint_finality_certificate_v1(&certificate)?.as_slice() != bytes {
        return Err(CheckpointFinalityCertificateErrorV1::NonCanonicalEncoding);
    }
    Ok(certificate)
}

fn require_input_size(size: usize) -> Result<(), CheckpointFinalityCertificateErrorV1> {
    if size == 0 {
        return Err(CheckpointFinalityCertificateErrorV1::EmptyInput);
    }
    if size > MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V1 {
        return Err(CheckpointFinalityCertificateErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V1,
        });
    }
    Ok(())
}
