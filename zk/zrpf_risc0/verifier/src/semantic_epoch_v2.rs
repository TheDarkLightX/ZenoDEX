use core::fmt;

use risc0_zkvm::Receipt;
use zenodex_zrpf_protocol_v3::{
    decode_exact_semantic_epoch_proposal_v2, encode_semantic_epoch_proposal_v2,
    semantic_epoch_dependency_manifest_root_v2, semantic_epoch_manifest_root_v1, CommitmentV3,
    ProgramIdV3, ProposedSemanticEpochV2, SemanticEpochDependencyProgramsV1,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, risc0_image_words_to_bytes,
};

use super::{
    verify_canonical_succinct_receipt_artifact, VerifiedNodeReceiptErrorV3,
    VerifiedReceiptProfileV3,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedSemanticEpochReceiptErrorV2 {
    ReceiptArtifact(VerifiedNodeReceiptErrorV3),
    ProposalDecodeFailed,
    DependencyManifestDerivationFailed,
    DependencyManifestMismatch,
    RuntimeManifestDerivationFailed,
    ClaimBindingFailed,
    ExpectedProposalEncodingFailed,
    ProposalBytesMismatch,
}

impl VerifiedSemanticEpochReceiptErrorV2 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::ReceiptArtifact(_) => "semantic_v2_receipt_artifact_rejected",
            Self::ProposalDecodeFailed => "semantic_v2_proposal_decode_failed",
            Self::DependencyManifestDerivationFailed => {
                "semantic_v2_dependency_manifest_derivation_failed"
            }
            Self::DependencyManifestMismatch => "semantic_v2_dependency_manifest_mismatch",
            Self::RuntimeManifestDerivationFailed => {
                "semantic_v2_runtime_manifest_derivation_failed"
            }
            Self::ClaimBindingFailed => "semantic_v2_claim_binding_failed",
            Self::ExpectedProposalEncodingFailed => "expected_semantic_v2_proposal_encoding_failed",
            Self::ProposalBytesMismatch => "semantic_v2_proposal_bytes_mismatch",
        }
    }
}

impl From<VerifiedNodeReceiptErrorV3> for VerifiedSemanticEpochReceiptErrorV2 {
    fn from(error: VerifiedNodeReceiptErrorV3) -> Self {
        Self::ReceiptArtifact(error)
    }
}

impl fmt::Display for VerifiedSemanticEpochReceiptErrorV2 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReceiptArtifact(error) => {
                write!(formatter, "semantic V2 receipt artifact rejected: {error}")
            }
            Self::ProposalDecodeFailed => {
                formatter.write_str("verified semantic V2 proposal strict decoding failed")
            }
            Self::DependencyManifestDerivationFailed => {
                formatter.write_str("governed semantic V2 dependency manifest derivation failed")
            }
            Self::DependencyManifestMismatch => formatter
                .write_str("semantic V2 proposal does not bind the governed dependency programs"),
            Self::RuntimeManifestDerivationFailed => {
                formatter.write_str("verified semantic V2 runtime manifest derivation failed")
            }
            Self::ClaimBindingFailed => {
                formatter.write_str("verified semantic V2 RISC0 claim binding derivation failed")
            }
            Self::ExpectedProposalEncodingFailed => {
                formatter.write_str("expected semantic V2 proposal encoding failed")
            }
            Self::ProposalBytesMismatch => formatter
                .write_str("verified semantic V2 proposal differs from the expected proposal"),
        }
    }
}

/// A semantic V2 receipt whose runtime identity was attached only after
/// cryptographic verification under the governed image.
///
/// The proof-neutral proposal cannot become this authority-bearing type:
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ProposedSemanticEpochV2;
/// use zenodex_zrpf_risc0_verifier::VerifiedSemanticEpochReceiptV2;
/// let proposal: ProposedSemanticEpochV2 = unimplemented!();
/// let _: VerifiedSemanticEpochReceiptV2 = proposal.into();
/// ```
pub struct VerifiedSemanticEpochReceiptV2 {
    receipt: Receipt,
    receipt_profile: VerifiedReceiptProfileV3,
    proposal: ProposedSemanticEpochV2,
    verified_program_id: ProgramIdV3,
    verified_program_manifest_root: CommitmentV3,
    claim_binding: CommitmentV3,
}

impl VerifiedSemanticEpochReceiptV2 {
    pub fn verify_canonical_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
        expected_dependencies: &SemanticEpochDependencyProgramsV1,
    ) -> Result<Self, VerifiedSemanticEpochReceiptErrorV2> {
        // Receipt authentication precedes journal decoding and all semantic
        // interpretation. D enters authority only through this call.
        let (receipt, receipt_profile) =
            verify_canonical_succinct_receipt_artifact(receipt_bytes, expected_image_id)?;
        let proposal = decode_exact_semantic_epoch_proposal_v2(&receipt.journal.bytes)
            .map_err(|_| VerifiedSemanticEpochReceiptErrorV2::ProposalDecodeFailed)?;
        let (verified_program_id, verified_program_manifest_root) =
            attach_verified_runtime_identity_v2(
                proposal.dependency_manifest_root(),
                expected_image_id,
                expected_dependencies,
            )?;
        let claim_binding =
            derive_risc0_verified_claim_binding_v1(expected_image_id, &receipt.journal.bytes)
                .map_err(|_| VerifiedSemanticEpochReceiptErrorV2::ClaimBindingFailed)?;
        Ok(Self {
            receipt,
            receipt_profile,
            proposal,
            verified_program_id,
            verified_program_manifest_root,
            claim_binding,
        })
    }

    pub fn verify_exact_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
        expected_dependencies: &SemanticEpochDependencyProgramsV1,
        expected_proposal: &ProposedSemanticEpochV2,
    ) -> Result<Self, VerifiedSemanticEpochReceiptErrorV2> {
        let verified = Self::verify_canonical_succinct_bytes(
            receipt_bytes,
            expected_image_id,
            expected_dependencies,
        )?;
        let expected_bytes = encode_semantic_epoch_proposal_v2(expected_proposal)
            .map_err(|_| VerifiedSemanticEpochReceiptErrorV2::ExpectedProposalEncodingFailed)?;
        if verified.receipt.journal.bytes != expected_bytes {
            return Err(VerifiedSemanticEpochReceiptErrorV2::ProposalBytesMismatch);
        }
        Ok(verified)
    }

    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn receipt_profile(&self) -> &VerifiedReceiptProfileV3 {
        &self.receipt_profile
    }

    pub const fn proposal(&self) -> &ProposedSemanticEpochV2 {
        &self.proposal
    }

    pub const fn verified_program_id(&self) -> ProgramIdV3 {
        self.verified_program_id
    }

    pub const fn verified_program_manifest_root(&self) -> CommitmentV3 {
        self.verified_program_manifest_root
    }

    pub const fn claim_binding(&self) -> CommitmentV3 {
        self.claim_binding
    }

    pub fn into_receipt(self) -> Receipt {
        self.receipt
    }
}

fn attach_verified_runtime_identity_v2(
    proposed_dependency_manifest_root: CommitmentV3,
    expected_image_id: [u32; 8],
    expected_dependencies: &SemanticEpochDependencyProgramsV1,
) -> Result<(ProgramIdV3, CommitmentV3), VerifiedSemanticEpochReceiptErrorV2> {
    let verified_program_id = ProgramIdV3::new(risc0_image_words_to_bytes(expected_image_id))
        .map_err(|_| VerifiedSemanticEpochReceiptErrorV2::RuntimeManifestDerivationFailed)?;
    let expected_dependency_manifest =
        semantic_epoch_dependency_manifest_root_v2(expected_dependencies)
            .map_err(|_| VerifiedSemanticEpochReceiptErrorV2::DependencyManifestDerivationFailed)?;
    if proposed_dependency_manifest_root != expected_dependency_manifest {
        return Err(VerifiedSemanticEpochReceiptErrorV2::DependencyManifestMismatch);
    }
    let verified_program_manifest_root =
        semantic_epoch_manifest_root_v1(verified_program_id, expected_dependencies)
            .map_err(|_| VerifiedSemanticEpochReceiptErrorV2::RuntimeManifestDerivationFailed)?;
    Ok((verified_program_id, verified_program_manifest_root))
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use risc0_zkvm::{FakeReceipt, Receipt, ReceiptClaim};
    use zenodex_zrpf_protocol_v3::{
        semantic_epoch_dependency_manifest_root_v2, CommitmentV3, ProgramIdV3,
        SemanticEpochDependencyProgramsInputV1, SemanticEpochDependencyProgramsV1,
    };

    use super::{
        attach_verified_runtime_identity_v2, VerifiedSemanticEpochReceiptErrorV2,
        VerifiedSemanticEpochReceiptV2,
    };
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
    fn semantic_v2_verifier_reject_codes_are_stable_and_unique() {
        let errors = [
            VerifiedSemanticEpochReceiptErrorV2::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::EmptyReceiptBytes,
            ),
            VerifiedSemanticEpochReceiptErrorV2::ProposalDecodeFailed,
            VerifiedSemanticEpochReceiptErrorV2::DependencyManifestDerivationFailed,
            VerifiedSemanticEpochReceiptErrorV2::DependencyManifestMismatch,
            VerifiedSemanticEpochReceiptErrorV2::RuntimeManifestDerivationFailed,
            VerifiedSemanticEpochReceiptErrorV2::ClaimBindingFailed,
            VerifiedSemanticEpochReceiptErrorV2::ExpectedProposalEncodingFailed,
            VerifiedSemanticEpochReceiptErrorV2::ProposalBytesMismatch,
        ];
        let codes: BTreeSet<&str> = errors.iter().map(|error| error.code()).collect();
        assert_eq!(codes.len(), errors.len());
    }

    #[test]
    fn semantic_v2_preserves_bounded_receipt_rejections_before_journal_decode() {
        assert_eq!(
            VerifiedSemanticEpochReceiptV2::verify_canonical_succinct_bytes(
                &[],
                IMAGE_ID,
                &dependencies(),
            )
            .err(),
            Some(VerifiedSemanticEpochReceiptErrorV2::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::EmptyReceiptBytes,
            ))
        );
        let oversized = vec![0_u8; MAX_CANONICAL_RECEIPT_BYTES_V3 + 1];
        assert_eq!(
            VerifiedSemanticEpochReceiptV2::verify_canonical_succinct_bytes(
                &oversized,
                IMAGE_ID,
                &dependencies(),
            )
            .err(),
            Some(VerifiedSemanticEpochReceiptErrorV2::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::ReceiptBytesTooLarge {
                    actual: MAX_CANONICAL_RECEIPT_BYTES_V3 + 1,
                    maximum: MAX_CANONICAL_RECEIPT_BYTES_V3,
                },
            ))
        );
    }

    #[test]
    fn fake_receipt_cannot_enter_the_semantic_v2_verified_type() {
        let receipt = Receipt::try_from(FakeReceipt::new(ReceiptClaim::ok(
            IMAGE_ID,
            b"proposal-v2".to_vec(),
        )))
        .expect("fake receipt conversion");
        let receipt_bytes = serde_json::to_vec(&receipt).expect("canonical fake receipt JSON");

        assert_eq!(
            VerifiedSemanticEpochReceiptV2::verify_canonical_succinct_bytes(
                &receipt_bytes,
                IMAGE_ID,
                &dependencies(),
            )
            .err(),
            Some(VerifiedSemanticEpochReceiptErrorV2::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::NonSuccinctReceipt,
            ))
        );
    }

    #[test]
    fn dependency_substitution_rejects_before_runtime_identity_attachment() {
        let dependencies = dependencies();
        let correct = semantic_epoch_dependency_manifest_root_v2(&dependencies).unwrap();
        let wrong = CommitmentV3::new([7; 32]).unwrap();

        assert_eq!(
            attach_verified_runtime_identity_v2(wrong, IMAGE_ID, &dependencies),
            Err(VerifiedSemanticEpochReceiptErrorV2::DependencyManifestMismatch)
        );
        let (verified_program, runtime_manifest) =
            attach_verified_runtime_identity_v2(correct, IMAGE_ID, &dependencies).unwrap();
        let (other_program, other_runtime_manifest) =
            attach_verified_runtime_identity_v2(correct, [8, 7, 6, 5, 4, 3, 2, 1], &dependencies)
                .unwrap();
        assert_ne!(verified_program, other_program);
        assert_ne!(runtime_manifest, other_runtime_manifest);
    }
}
