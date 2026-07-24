//! Governed receipt verification used only by the separate authority PID-1.

use core::fmt;

use zenodex_zrpf_risc0_spot_settlement_v7_child_policy::FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1;
use zenodex_zrpf_risc0_spot_settlement_v7_methods::ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID;
use zenodex_zrpf_risc0_spot_settlement_v7_verifier::{
    encode_spot_settlement_v7_verifier_output_v1,
    verify_spot_settlement_v7_canonical_succinct_bytes,
};

use crate::{
    decode_structural_spot_v7_payload_v1, SpotV7FirecrackerAuthorityInputErrorV1,
    SpotV7FirecrackerAuthorityInputManifestV1, SpotV7FirecrackerRequestV1,
    StructurallyDecodedSpotV7PayloadV1,
};

pub const SPOT_V7_FIRECRACKER_AUTHORITY_PID1_LIVE_RUNNER_AUTHORITY_V1: bool = false;
pub const SPOT_V7_FIRECRACKER_AUTHORITY_PID1_RELEASE_AUTHORITY_V1: bool = false;
pub const SPOT_V7_FIRECRACKER_AUTHORITY_PID1_SETTLEMENT_AUTHORITY_V1: bool = false;
pub const SPOT_V7_FIRECRACKER_AUTHORITY_PID1_PRODUCTION_READY_V1: bool = false;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotV7FirecrackerAuthorityVerificationErrorV1 {
    AuthorityInput(SpotV7FirecrackerAuthorityInputErrorV1),
    RequestManifestBinding,
    GovernedVerifier,
    VerifierOutput,
    OutputProtocol,
}

impl SpotV7FirecrackerAuthorityVerificationErrorV1 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::AuthorityInput(error) => error.code(),
            Self::RequestManifestBinding => "authority_request_manifest_binding",
            Self::GovernedVerifier => "authority_governed_verifier",
            Self::VerifierOutput => "authority_verifier_output",
            Self::OutputProtocol => "authority_output_protocol",
        }
    }
}

impl fmt::Display for SpotV7FirecrackerAuthorityVerificationErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.code())
    }
}

impl std::error::Error for SpotV7FirecrackerAuthorityVerificationErrorV1 {}

impl From<SpotV7FirecrackerAuthorityInputErrorV1>
    for SpotV7FirecrackerAuthorityVerificationErrorV1
{
    fn from(error: SpotV7FirecrackerAuthorityInputErrorV1) -> Self {
        Self::AuthorityInput(error)
    }
}

/// Authenticate the exact three manifest-bound inputs and derive the payload.
///
/// The closure passed to the internal helper is `FnOnce`, so the governed V7
/// verifier path cannot be invoked twice by this orchestration layer. The V7
/// verifier itself authenticates the V6 child and V7 receipt, recomposes the
/// complete journal, and returns the private verified value used to derive the
/// output. The output remains data until a governed live runner and atomic
/// store consume it.
pub fn derive_governed_spot_v7_authority_payload_v1(
    request: &SpotV7FirecrackerRequestV1,
    manifest_bytes: &[u8],
    v7_receipt_bytes: &[u8],
    guest_input_bytes: &[u8],
    v6_receipt_bytes: &[u8],
) -> Result<StructurallyDecodedSpotV7PayloadV1, SpotV7FirecrackerAuthorityVerificationErrorV1> {
    derive_authority_payload_with_verifier_v1(
        AuthorityVerificationInputsV1 {
            request_settlement_intent_sha256: request.settlement_intent_sha256(),
            manifest_bytes,
            v7_receipt_bytes,
            guest_input_bytes,
            v6_receipt_bytes,
            governed_v7_image_id: ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID,
            governed_v6_image_id: FINAL_SOURCE_OPENED_SPOT_SETTLEMENT_V6_IMAGE_ID_V1,
        },
        |v7_receipt, guest_input, v6_receipt| {
            let verified = verify_spot_settlement_v7_canonical_succinct_bytes(
                v7_receipt,
                guest_input,
                v6_receipt,
            )
            .map_err(|_| VerifyAndEncodeErrorV1::Verifier)?;
            let output = verified
                .firecracker_output()
                .map_err(|_| VerifyAndEncodeErrorV1::Output)?;
            encode_spot_settlement_v7_verifier_output_v1(&output)
                .map_err(|_| VerifyAndEncodeErrorV1::Output)
        },
    )
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum VerifyAndEncodeErrorV1 {
    Verifier,
    Output,
}

struct AuthorityVerificationInputsV1<'a> {
    request_settlement_intent_sha256: &'a [u8; 32],
    manifest_bytes: &'a [u8],
    v7_receipt_bytes: &'a [u8],
    guest_input_bytes: &'a [u8],
    v6_receipt_bytes: &'a [u8],
    governed_v7_image_id: [u32; 8],
    governed_v6_image_id: [u32; 8],
}

fn derive_authority_payload_with_verifier_v1<F>(
    inputs: AuthorityVerificationInputsV1<'_>,
    verify_and_encode: F,
) -> Result<StructurallyDecodedSpotV7PayloadV1, SpotV7FirecrackerAuthorityVerificationErrorV1>
where
    F: FnOnce(&[u8], &[u8], &[u8]) -> Result<Vec<u8>, VerifyAndEncodeErrorV1>,
{
    let manifest = SpotV7FirecrackerAuthorityInputManifestV1::decode(inputs.manifest_bytes)?;
    // In this versioned candidate profile, the outer request's settlement
    // intent is exactly the authority-input manifest identity. The manifest
    // then binds every receipt/input artifact. This does not claim a separate
    // semantic intent hash beyond the verified V7 journal.
    if manifest.sha256() != *inputs.request_settlement_intent_sha256 {
        return Err(SpotV7FirecrackerAuthorityVerificationErrorV1::RequestManifestBinding);
    }
    manifest
        .require_governed_image_ids(inputs.governed_v7_image_id, inputs.governed_v6_image_id)?;
    manifest.validate_artifacts(
        inputs.v7_receipt_bytes,
        inputs.guest_input_bytes,
        inputs.v6_receipt_bytes,
    )?;
    let payload_bytes = verify_and_encode(
        inputs.v7_receipt_bytes,
        inputs.guest_input_bytes,
        inputs.v6_receipt_bytes,
    )
    .map_err(|error| match error {
        VerifyAndEncodeErrorV1::Verifier => {
            SpotV7FirecrackerAuthorityVerificationErrorV1::GovernedVerifier
        }
        VerifyAndEncodeErrorV1::Output => {
            SpotV7FirecrackerAuthorityVerificationErrorV1::VerifierOutput
        }
    })?;
    decode_structural_spot_v7_payload_v1(&payload_bytes)
        .map_err(|_| SpotV7FirecrackerAuthorityVerificationErrorV1::OutputProtocol)
}

#[cfg(test)]
mod tests {
    use core::sync::atomic::{AtomicUsize, Ordering};

    use super::*;

    const V7_IMAGE_ID: [u32; 8] = [7; 8];
    const V6_IMAGE_ID: [u32; 8] = [6; 8];
    const GOLDEN_PAYLOAD_HEX: &str =
        include_str!("../../verifier/tests/vectors/spot_settlement_v7_firecracker_output_v1.hex");

    #[test]
    fn valid_inputs_invoke_verifier_once_and_use_its_exact_payload() {
        let (v7_receipt, guest_input, v6_receipt, manifest) = inputs();
        let calls = AtomicUsize::new(0);
        let payload = derive_authority_payload_with_verifier_v1(
            AuthorityVerificationInputsV1 {
                request_settlement_intent_sha256: &manifest.sha256(),
                manifest_bytes: &manifest.encode(),
                v7_receipt_bytes: &v7_receipt,
                guest_input_bytes: &guest_input,
                v6_receipt_bytes: &v6_receipt,
                governed_v7_image_id: V7_IMAGE_ID,
                governed_v6_image_id: V6_IMAGE_ID,
            },
            |_v7, _input, _v6| {
                calls.fetch_add(1, Ordering::Relaxed);
                Ok(golden_payload())
            },
        )
        .expect("manifest-bound verifier payload");
        assert_eq!(calls.load(Ordering::Relaxed), 1);
        assert_eq!(payload.raw_bytes(), golden_payload());
    }

    #[test]
    fn malformed_or_mismatched_inputs_never_invoke_verifier() {
        let (v7_receipt, guest_input, v6_receipt, manifest) = inputs();
        let mut malformed = manifest.encode();
        malformed[0] ^= 1;
        let mut wrong_input = guest_input.clone();
        wrong_input[0] ^= 1;

        for (manifest_bytes, supplied_input, expected) in [
            (
                malformed.to_vec(),
                guest_input.as_slice(),
                SpotV7FirecrackerAuthorityVerificationErrorV1::AuthorityInput(
                    SpotV7FirecrackerAuthorityInputErrorV1::ManifestMagic,
                ),
            ),
            (
                manifest.encode().to_vec(),
                wrong_input.as_slice(),
                SpotV7FirecrackerAuthorityVerificationErrorV1::AuthorityInput(
                    SpotV7FirecrackerAuthorityInputErrorV1::GuestInputBinding,
                ),
            ),
        ] {
            let calls = AtomicUsize::new(0);
            let result = derive_authority_payload_with_verifier_v1(
                AuthorityVerificationInputsV1 {
                    request_settlement_intent_sha256: &manifest.sha256(),
                    manifest_bytes: &manifest_bytes,
                    v7_receipt_bytes: &v7_receipt,
                    guest_input_bytes: supplied_input,
                    v6_receipt_bytes: &v6_receipt,
                    governed_v7_image_id: V7_IMAGE_ID,
                    governed_v6_image_id: V6_IMAGE_ID,
                },
                |_v7, _input, _v6| {
                    calls.fetch_add(1, Ordering::Relaxed);
                    Ok(golden_payload())
                },
            );
            assert_eq!(result, Err(expected));
            assert_eq!(calls.load(Ordering::Relaxed), 0);
        }

        let wrong_settlement_intent = [0x55; 32];
        let calls = AtomicUsize::new(0);
        let result = derive_authority_payload_with_verifier_v1(
            AuthorityVerificationInputsV1 {
                request_settlement_intent_sha256: &wrong_settlement_intent,
                manifest_bytes: &manifest.encode(),
                v7_receipt_bytes: &v7_receipt,
                guest_input_bytes: &guest_input,
                v6_receipt_bytes: &v6_receipt,
                governed_v7_image_id: V7_IMAGE_ID,
                governed_v6_image_id: V6_IMAGE_ID,
            },
            |_v7, _input, _v6| {
                calls.fetch_add(1, Ordering::Relaxed);
                Ok(golden_payload())
            },
        );
        assert_eq!(
            result,
            Err(SpotV7FirecrackerAuthorityVerificationErrorV1::RequestManifestBinding)
        );
        assert_eq!(calls.load(Ordering::Relaxed), 0);
    }

    #[test]
    fn coherently_rehashed_receipt_mutation_still_requires_crypto_rejection() {
        let (v7_receipt, guest_input, v6_receipt, _) = inputs();
        let mut mutated = v7_receipt;
        mutated[0] ^= 1;
        let manifest = SpotV7FirecrackerAuthorityInputManifestV1::new(
            V7_IMAGE_ID,
            V6_IMAGE_ID,
            &mutated,
            &guest_input,
            &v6_receipt,
        )
        .expect("coherent mutation manifest");
        let calls = AtomicUsize::new(0);
        let result = derive_authority_payload_with_verifier_v1(
            AuthorityVerificationInputsV1 {
                request_settlement_intent_sha256: &manifest.sha256(),
                manifest_bytes: &manifest.encode(),
                v7_receipt_bytes: &mutated,
                guest_input_bytes: &guest_input,
                v6_receipt_bytes: &v6_receipt,
                governed_v7_image_id: V7_IMAGE_ID,
                governed_v6_image_id: V6_IMAGE_ID,
            },
            |_v7, _input, _v6| {
                calls.fetch_add(1, Ordering::Relaxed);
                Err(VerifyAndEncodeErrorV1::Verifier)
            },
        );
        assert_eq!(
            result,
            Err(SpotV7FirecrackerAuthorityVerificationErrorV1::GovernedVerifier)
        );
        assert_eq!(calls.load(Ordering::Relaxed), 1);
    }

    #[test]
    fn placeholder_compiled_image_rejects_before_verifier() {
        let (v7_receipt, guest_input, v6_receipt, manifest) = inputs();
        let calls = AtomicUsize::new(0);
        let result = derive_authority_payload_with_verifier_v1(
            AuthorityVerificationInputsV1 {
                request_settlement_intent_sha256: &manifest.sha256(),
                manifest_bytes: &manifest.encode(),
                v7_receipt_bytes: &v7_receipt,
                guest_input_bytes: &guest_input,
                v6_receipt_bytes: &v6_receipt,
                governed_v7_image_id: [0; 8],
                governed_v6_image_id: V6_IMAGE_ID,
            },
            |_v7, _input, _v6| {
                calls.fetch_add(1, Ordering::Relaxed);
                Ok(golden_payload())
            },
        );
        assert_eq!(
            result,
            Err(
                SpotV7FirecrackerAuthorityVerificationErrorV1::AuthorityInput(
                    SpotV7FirecrackerAuthorityInputErrorV1::V7ImageIdUnmaterialized,
                )
            )
        );
        assert_eq!(calls.load(Ordering::Relaxed), 0);
    }

    fn inputs() -> (
        Vec<u8>,
        Vec<u8>,
        Vec<u8>,
        SpotV7FirecrackerAuthorityInputManifestV1,
    ) {
        let v7_receipt = b"v7 receipt".to_vec();
        let guest_input = b"guest input".to_vec();
        let v6_receipt = b"v6 receipt".to_vec();
        let manifest = SpotV7FirecrackerAuthorityInputManifestV1::new(
            V7_IMAGE_ID,
            V6_IMAGE_ID,
            &v7_receipt,
            &guest_input,
            &v6_receipt,
        )
        .expect("valid manifest");
        (v7_receipt, guest_input, v6_receipt, manifest)
    }

    fn golden_payload() -> Vec<u8> {
        let compact = GOLDEN_PAYLOAD_HEX
            .lines()
            .map(|line| line.split("//").next().unwrap_or("").trim())
            .collect::<String>();
        hex::decode(compact).expect("valid payload")
    }
}
