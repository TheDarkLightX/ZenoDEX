//! Historical V1 retained-receipt verifier.
//!
//! V1 accepted a host-declared semantic self-image inside the guest statement.
//! Its exact outer binding remains useful for immutable historical replay, but
//! this module grants no current admission, release, settlement, or production
//! authority. New consumers must use `VerifiedSemanticEpochReceiptV2`.

use core::fmt;

use risc0_zkvm::Receipt;
use zenodex_zrpf_protocol_v3::{
    decode_exact_semantic_epoch_proposal_v1, encode_semantic_epoch_proposal_v1,
    semantic_epoch_manifest_root_v1, CommitmentV3, ProgramIdV3, ProposedSemanticEpochV1,
    SemanticEpochDependencyProgramsV1,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, risc0_image_words_to_bytes,
};

use super::{
    verify_canonical_succinct_receipt_artifact, VerifiedNodeReceiptErrorV3,
    VerifiedReceiptProfileV3,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedSemanticEpochReceiptErrorV1 {
    ReceiptArtifact(VerifiedNodeReceiptErrorV3),
    ProposalDecodeFailed,
    ProgramIdMismatch,
    ManifestDerivationFailed,
    ManifestMismatch,
    ClaimBindingFailed,
    ExpectedProposalEncodingFailed,
    ProposalBytesMismatch,
}

impl VerifiedSemanticEpochReceiptErrorV1 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::ReceiptArtifact(_) => "semantic_receipt_artifact_rejected",
            Self::ProposalDecodeFailed => "semantic_proposal_decode_failed",
            Self::ProgramIdMismatch => "semantic_program_id_mismatch",
            Self::ManifestDerivationFailed => "semantic_manifest_derivation_failed",
            Self::ManifestMismatch => "semantic_manifest_mismatch",
            Self::ClaimBindingFailed => "semantic_claim_binding_failed",
            Self::ExpectedProposalEncodingFailed => "expected_semantic_proposal_encoding_failed",
            Self::ProposalBytesMismatch => "semantic_proposal_bytes_mismatch",
        }
    }
}

impl From<VerifiedNodeReceiptErrorV3> for VerifiedSemanticEpochReceiptErrorV1 {
    fn from(error: VerifiedNodeReceiptErrorV3) -> Self {
        Self::ReceiptArtifact(error)
    }
}

impl fmt::Display for VerifiedSemanticEpochReceiptErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReceiptArtifact(error) => {
                write!(formatter, "semantic receipt artifact rejected: {error}")
            }
            Self::ProposalDecodeFailed => {
                formatter.write_str("verified semantic proposal strict decoding failed")
            }
            Self::ProgramIdMismatch => formatter.write_str(
                "semantic proposal program ID differs from the image used to verify the receipt",
            ),
            Self::ManifestDerivationFailed => {
                formatter.write_str("governed semantic manifest derivation failed")
            }
            Self::ManifestMismatch => formatter.write_str(
                "semantic proposal manifest does not bind the governed dependency programs",
            ),
            Self::ClaimBindingFailed => {
                formatter.write_str("verified semantic RISC0 claim binding derivation failed")
            }
            Self::ExpectedProposalEncodingFailed => {
                formatter.write_str("expected semantic proposal encoding failed")
            }
            Self::ProposalBytesMismatch => {
                formatter.write_str("verified semantic proposal differs from the expected proposal")
            }
        }
    }
}

/// A Succinct receipt and semantic proposal that crossed the complete host
/// verification boundary.
///
/// Fields are private, and every construction path begins with bounded canonical
/// receipt bytes. A proof-system-neutral proposal cannot become a verified
/// receipt through conversion:
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ProposedSemanticEpochV1;
/// use zenodex_zrpf_risc0_verifier::historical_semantic_epoch_v1::VerifiedSemanticEpochReceiptV1;
/// let proposal: ProposedSemanticEpochV1 = unimplemented!();
/// let _: VerifiedSemanticEpochReceiptV1 = proposal.into();
/// ```
pub struct VerifiedSemanticEpochReceiptV1 {
    receipt: Receipt,
    receipt_profile: VerifiedReceiptProfileV3,
    proposal: ProposedSemanticEpochV1,
    claim_binding: CommitmentV3,
}

impl VerifiedSemanticEpochReceiptV1 {
    pub fn verify_canonical_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
        expected_dependencies: &SemanticEpochDependencyProgramsV1,
    ) -> Result<Self, VerifiedSemanticEpochReceiptErrorV1> {
        let (receipt, receipt_profile) =
            verify_canonical_succinct_receipt_artifact(receipt_bytes, expected_image_id)?;
        let proposal = decode_exact_semantic_epoch_proposal_v1(&receipt.journal.bytes)
            .map_err(|_| VerifiedSemanticEpochReceiptErrorV1::ProposalDecodeFailed)?;
        let verified_program_id =
            ProgramIdV3::new(risc0_image_words_to_bytes(expected_image_id))
                .map_err(|_| VerifiedSemanticEpochReceiptErrorV1::ProgramIdMismatch)?;
        if proposal.actual_program_id() != verified_program_id {
            return Err(VerifiedSemanticEpochReceiptErrorV1::ProgramIdMismatch);
        }
        let expected_manifest =
            semantic_epoch_manifest_root_v1(verified_program_id, expected_dependencies)
                .map_err(|_| VerifiedSemanticEpochReceiptErrorV1::ManifestDerivationFailed)?;
        if proposal.program_manifest_root() != expected_manifest {
            return Err(VerifiedSemanticEpochReceiptErrorV1::ManifestMismatch);
        }
        let claim_binding =
            derive_risc0_verified_claim_binding_v1(expected_image_id, &receipt.journal.bytes)
                .map_err(|_| VerifiedSemanticEpochReceiptErrorV1::ClaimBindingFailed)?;
        Ok(Self {
            receipt,
            receipt_profile,
            proposal,
            claim_binding,
        })
    }

    pub fn verify_exact_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
        expected_dependencies: &SemanticEpochDependencyProgramsV1,
        expected_proposal: &ProposedSemanticEpochV1,
    ) -> Result<Self, VerifiedSemanticEpochReceiptErrorV1> {
        let verified = Self::verify_canonical_succinct_bytes(
            receipt_bytes,
            expected_image_id,
            expected_dependencies,
        )?;
        let expected_bytes = encode_semantic_epoch_proposal_v1(expected_proposal)
            .map_err(|_| VerifiedSemanticEpochReceiptErrorV1::ExpectedProposalEncodingFailed)?;
        if verified.receipt.journal.bytes != expected_bytes {
            return Err(VerifiedSemanticEpochReceiptErrorV1::ProposalBytesMismatch);
        }
        Ok(verified)
    }

    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn receipt_profile(&self) -> &VerifiedReceiptProfileV3 {
        &self.receipt_profile
    }

    pub const fn proposal(&self) -> &ProposedSemanticEpochV1 {
        &self.proposal
    }

    pub const fn claim_binding(&self) -> CommitmentV3 {
        self.claim_binding
    }

    pub fn into_receipt(self) -> Receipt {
        self.receipt
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
    use zenodex_zrpf_protocol_v3::{
        ProgramIdV3, SemanticEpochDependencyProgramsInputV1, SemanticEpochDependencyProgramsV1,
    };

    use super::{VerifiedSemanticEpochReceiptErrorV1, VerifiedSemanticEpochReceiptV1};
    use crate::{VerifiedNodeReceiptErrorV3, MAX_CANONICAL_RECEIPT_BYTES_V3};

    const IMAGE_ID: [u32; 8] = [1, 2, 3, 4, 5, 6, 7, 8];

    fn dependencies() -> SemanticEpochDependencyProgramsV1 {
        SemanticEpochDependencyProgramsV1::new(SemanticEpochDependencyProgramsInputV1 {
            adapter_program_id: ProgramIdV3::new([1; 32]).expect("nonzero adapter program ID"),
            level_one_program_id: ProgramIdV3::new([2; 32]).expect("nonzero level-one program ID"),
            level_two_program_id: ProgramIdV3::new([3; 32]).expect("nonzero level-two program ID"),
        })
    }

    #[test]
    fn semantic_verifier_reject_codes_are_stable_and_unique() {
        let errors = [
            VerifiedSemanticEpochReceiptErrorV1::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::EmptyReceiptBytes,
            ),
            VerifiedSemanticEpochReceiptErrorV1::ProposalDecodeFailed,
            VerifiedSemanticEpochReceiptErrorV1::ProgramIdMismatch,
            VerifiedSemanticEpochReceiptErrorV1::ManifestDerivationFailed,
            VerifiedSemanticEpochReceiptErrorV1::ManifestMismatch,
            VerifiedSemanticEpochReceiptErrorV1::ClaimBindingFailed,
            VerifiedSemanticEpochReceiptErrorV1::ExpectedProposalEncodingFailed,
            VerifiedSemanticEpochReceiptErrorV1::ProposalBytesMismatch,
        ];
        let codes: BTreeSet<&str> = errors.iter().map(|error| error.code()).collect();
        assert_eq!(codes.len(), errors.len());
    }

    #[test]
    fn semantic_verifier_preserves_bounded_canonical_receipt_rejections() {
        assert_eq!(
            VerifiedSemanticEpochReceiptV1::verify_canonical_succinct_bytes(
                &[],
                IMAGE_ID,
                &dependencies(),
            )
            .err(),
            Some(VerifiedSemanticEpochReceiptErrorV1::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::EmptyReceiptBytes,
            ))
        );
        let oversized = vec![0_u8; MAX_CANONICAL_RECEIPT_BYTES_V3 + 1];
        assert_eq!(
            VerifiedSemanticEpochReceiptV1::verify_canonical_succinct_bytes(
                &oversized,
                IMAGE_ID,
                &dependencies(),
            )
            .err(),
            Some(VerifiedSemanticEpochReceiptErrorV1::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::ReceiptBytesTooLarge {
                    actual: MAX_CANONICAL_RECEIPT_BYTES_V3 + 1,
                    maximum: MAX_CANONICAL_RECEIPT_BYTES_V3,
                },
            ))
        );
        assert_eq!(
            VerifiedSemanticEpochReceiptV1::verify_canonical_succinct_bytes(
                b"{}",
                [0; 8],
                &dependencies(),
            )
            .err(),
            Some(VerifiedSemanticEpochReceiptErrorV1::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::ZeroExpectedImageId,
            ))
        );
    }

    #[test]
    fn fake_receipt_cannot_enter_the_semantic_verified_type() {
        let receipt = Receipt::try_from(FakeReceipt::new(ReceiptClaim::ok(
            IMAGE_ID,
            b"proposal".to_vec(),
        )))
        .expect("fake receipt conversion");
        let receipt_bytes = serde_json::to_vec(&receipt).expect("canonical fake receipt JSON");

        assert_eq!(
            VerifiedSemanticEpochReceiptV1::verify_canonical_succinct_bytes(
                &receipt_bytes,
                IMAGE_ID,
                &dependencies(),
            )
            .err(),
            Some(VerifiedSemanticEpochReceiptErrorV1::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::NonSuccinctReceipt,
            ))
        );
    }
}
