use alloc::vec::Vec;

use serde::{Deserialize, Serialize};

use super::{
    AssumptionManifestV1, ProofShapeErrorV1, ProofShapeRegistryV1, ProofShapeV1,
    MAX_ASSUMPTION_MANIFEST_BYTES_V1, MAX_PROOF_SHAPE_BYTES_V1, MAX_PROOF_SHAPE_REGISTRY_BYTES_V1,
};

pub fn encode_proof_shape_v1(value: &ProofShapeV1) -> Result<Vec<u8>, ProofShapeErrorV1> {
    value.validate()?;
    encode_bounded(value, MAX_PROOF_SHAPE_BYTES_V1)
}

pub fn decode_exact_proof_shape_v1(bytes: &[u8]) -> Result<ProofShapeV1, ProofShapeErrorV1> {
    decode_exact_bounded(bytes, MAX_PROOF_SHAPE_BYTES_V1, encode_proof_shape_v1)
}

pub fn encode_assumption_manifest_v1(
    value: &AssumptionManifestV1,
) -> Result<Vec<u8>, ProofShapeErrorV1> {
    value.validate()?;
    encode_bounded(value, MAX_ASSUMPTION_MANIFEST_BYTES_V1)
}

pub fn decode_exact_assumption_manifest_v1(
    bytes: &[u8],
) -> Result<AssumptionManifestV1, ProofShapeErrorV1> {
    decode_exact_bounded(
        bytes,
        MAX_ASSUMPTION_MANIFEST_BYTES_V1,
        encode_assumption_manifest_v1,
    )
}

pub fn encode_proof_shape_registry_v1(
    value: &ProofShapeRegistryV1,
) -> Result<Vec<u8>, ProofShapeErrorV1> {
    value.validate()?;
    encode_bounded(value, MAX_PROOF_SHAPE_REGISTRY_BYTES_V1)
}

pub fn decode_exact_proof_shape_registry_v1(
    bytes: &[u8],
) -> Result<ProofShapeRegistryV1, ProofShapeErrorV1> {
    decode_exact_bounded(
        bytes,
        MAX_PROOF_SHAPE_REGISTRY_BYTES_V1,
        encode_proof_shape_registry_v1,
    )
}

fn encode_bounded<T: Serialize>(value: &T, maximum: usize) -> Result<Vec<u8>, ProofShapeErrorV1> {
    let bytes = postcard::to_allocvec(value).map_err(|_| ProofShapeErrorV1::PostcardDecode)?;
    if bytes.len() > maximum {
        return Err(ProofShapeErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum,
        });
    }
    Ok(bytes)
}

fn decode_exact_bounded<T>(
    bytes: &[u8],
    maximum: usize,
    encode: fn(&T) -> Result<Vec<u8>, ProofShapeErrorV1>,
) -> Result<T, ProofShapeErrorV1>
where
    T: for<'de> Deserialize<'de>,
{
    if bytes.is_empty() {
        return Err(ProofShapeErrorV1::EmptyInput);
    }
    if bytes.len() > maximum {
        return Err(ProofShapeErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum,
        });
    }
    let (value, remainder) =
        postcard::take_from_bytes(bytes).map_err(|_| ProofShapeErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ProofShapeErrorV1::TrailingBytes);
    }
    if encode(&value)?.as_slice() != bytes {
        return Err(ProofShapeErrorV1::NonCanonicalEncoding);
    }
    Ok(value)
}
