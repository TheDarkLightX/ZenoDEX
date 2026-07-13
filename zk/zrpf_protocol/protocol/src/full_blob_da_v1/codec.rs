use alloc::vec::Vec;

use super::{
    FullBlobDataAvailabilityCertificateV1, FullBlobDataAvailabilityErrorV1,
    MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
};

pub fn encode_full_blob_da_certificate_v1(
    certificate: &FullBlobDataAvailabilityCertificateV1,
) -> Result<Vec<u8>, FullBlobDataAvailabilityErrorV1> {
    certificate.validate_self_consistency()?;
    let bytes = postcard::to_allocvec(certificate)
        .map_err(|_| FullBlobDataAvailabilityErrorV1::PostcardDecode)?;
    require_input_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_full_blob_da_certificate_v1(
    bytes: &[u8],
) -> Result<FullBlobDataAvailabilityCertificateV1, FullBlobDataAvailabilityErrorV1> {
    require_input_size(bytes.len())?;
    let (certificate, remainder) =
        postcard::take_from_bytes::<FullBlobDataAvailabilityCertificateV1>(bytes)
            .map_err(|_| FullBlobDataAvailabilityErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(FullBlobDataAvailabilityErrorV1::TrailingBytes);
    }
    if encode_full_blob_da_certificate_v1(&certificate)?.as_slice() != bytes {
        return Err(FullBlobDataAvailabilityErrorV1::NonCanonicalEncoding);
    }
    Ok(certificate)
}

fn require_input_size(size: usize) -> Result<(), FullBlobDataAvailabilityErrorV1> {
    if size == 0 {
        return Err(FullBlobDataAvailabilityErrorV1::EmptyInput);
    }
    if size > MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1 {
        return Err(FullBlobDataAvailabilityErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_FULL_BLOB_DA_CERTIFICATE_BYTES_V1,
        });
    }
    Ok(())
}
