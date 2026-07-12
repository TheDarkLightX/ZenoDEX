use alloc::vec::Vec;

use serde::{Deserialize, Serialize};

use super::base::{TaskManifestErrorV1, MAX_PROGRAM_MANIFEST_BYTES_V1, MAX_PROOF_TASK_BYTES_V1};
use super::manifest::ProgramManifestV1;
use super::task::ProofTaskV1;

pub fn encode_program_manifest_v1(
    value: &ProgramManifestV1,
) -> Result<Vec<u8>, TaskManifestErrorV1> {
    value.validate()?;
    encode_bounded(value, MAX_PROGRAM_MANIFEST_BYTES_V1)
}

pub fn decode_exact_program_manifest_v1(
    bytes: &[u8],
) -> Result<ProgramManifestV1, TaskManifestErrorV1> {
    decode_exact_bounded(
        bytes,
        MAX_PROGRAM_MANIFEST_BYTES_V1,
        encode_program_manifest_v1,
    )
}

pub fn encode_proof_task_v1(value: &ProofTaskV1) -> Result<Vec<u8>, TaskManifestErrorV1> {
    value.validate()?;
    encode_bounded(value, MAX_PROOF_TASK_BYTES_V1)
}

pub fn decode_exact_proof_task_v1(bytes: &[u8]) -> Result<ProofTaskV1, TaskManifestErrorV1> {
    decode_exact_bounded(bytes, MAX_PROOF_TASK_BYTES_V1, encode_proof_task_v1)
}

fn encode_bounded<T: Serialize>(value: &T, maximum: usize) -> Result<Vec<u8>, TaskManifestErrorV1> {
    let bytes = postcard::to_allocvec(value).map_err(|_| TaskManifestErrorV1::PostcardDecode)?;
    if bytes.len() > maximum {
        return Err(TaskManifestErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum,
        });
    }
    Ok(bytes)
}

fn decode_exact_bounded<T>(
    bytes: &[u8],
    maximum: usize,
    encode: fn(&T) -> Result<Vec<u8>, TaskManifestErrorV1>,
) -> Result<T, TaskManifestErrorV1>
where
    T: for<'de> Deserialize<'de>,
{
    if bytes.is_empty() {
        return Err(TaskManifestErrorV1::EmptyInput);
    }
    if bytes.len() > maximum {
        return Err(TaskManifestErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum,
        });
    }
    let (value, remainder) =
        postcard::take_from_bytes(bytes).map_err(|_| TaskManifestErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(TaskManifestErrorV1::TrailingBytes);
    }
    if encode(&value)?.as_slice() != bytes {
        return Err(TaskManifestErrorV1::NonCanonicalEncoding);
    }
    Ok(value)
}
