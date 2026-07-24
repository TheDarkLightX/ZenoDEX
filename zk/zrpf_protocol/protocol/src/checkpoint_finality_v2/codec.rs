use alloc::vec::Vec;

use super::{
    CheckpointFinalityCertificateErrorV2, CheckpointFinalityCertificateV2,
    MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2,
};

pub fn encode_checkpoint_finality_certificate_v2(
    certificate: &CheckpointFinalityCertificateV2,
) -> Result<Vec<u8>, CheckpointFinalityCertificateErrorV2> {
    certificate.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(certificate)
        .map_err(|_| CheckpointFinalityCertificateErrorV2::PostcardDecode)?;
    require_input_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_checkpoint_finality_certificate_v2(
    bytes: &[u8],
) -> Result<CheckpointFinalityCertificateV2, CheckpointFinalityCertificateErrorV2> {
    require_input_size(bytes.len())?;
    let (certificate, remainder) =
        postcard::take_from_bytes::<CheckpointFinalityCertificateV2>(bytes)
            .map_err(|_| CheckpointFinalityCertificateErrorV2::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(CheckpointFinalityCertificateErrorV2::TrailingBytes);
    }
    if encode_checkpoint_finality_certificate_v2(&certificate)?.as_slice() != bytes {
        return Err(CheckpointFinalityCertificateErrorV2::NonCanonicalEncoding);
    }
    Ok(certificate)
}

fn require_input_size(size: usize) -> Result<(), CheckpointFinalityCertificateErrorV2> {
    if size == 0 {
        return Err(CheckpointFinalityCertificateErrorV2::EmptyInput);
    }
    if size > MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2 {
        return Err(CheckpointFinalityCertificateErrorV2::InputTooLarge {
            actual: size,
            maximum: MAX_CHECKPOINT_FINALITY_CERTIFICATE_BYTES_V2,
        });
    }
    Ok(())
}
