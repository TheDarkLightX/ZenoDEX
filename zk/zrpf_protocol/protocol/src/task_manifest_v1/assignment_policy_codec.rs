use alloc::vec::Vec;

use super::assignment_policy::{
    ProofAssignmentPolicyErrorV1, ProofAssignmentPolicyV1, MAX_PROOF_ASSIGNMENT_POLICY_BYTES_V1,
};

pub fn encode_proof_assignment_policy_v1(
    value: &ProofAssignmentPolicyV1,
) -> Result<Vec<u8>, ProofAssignmentPolicyErrorV1> {
    value.validate()?;
    let bytes =
        postcard::to_allocvec(value).map_err(|_| ProofAssignmentPolicyErrorV1::PostcardDecode)?;
    if bytes.len() > MAX_PROOF_ASSIGNMENT_POLICY_BYTES_V1 {
        return Err(ProofAssignmentPolicyErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_PROOF_ASSIGNMENT_POLICY_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_proof_assignment_policy_v1(
    bytes: &[u8],
) -> Result<ProofAssignmentPolicyV1, ProofAssignmentPolicyErrorV1> {
    if bytes.is_empty() {
        return Err(ProofAssignmentPolicyErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_PROOF_ASSIGNMENT_POLICY_BYTES_V1 {
        return Err(ProofAssignmentPolicyErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_PROOF_ASSIGNMENT_POLICY_BYTES_V1,
        });
    }
    let (value, remainder): (ProofAssignmentPolicyV1, &[u8]) = postcard::take_from_bytes(bytes)
        .map_err(|_| ProofAssignmentPolicyErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(ProofAssignmentPolicyErrorV1::TrailingBytes);
    }
    if encode_proof_assignment_policy_v1(&value)?.as_slice() != bytes {
        return Err(ProofAssignmentPolicyErrorV1::NonCanonicalEncoding);
    }
    Ok(value)
}
