use core::fmt;

use risc0_zkvm::Receipt;
use zenodex_zrpf_protocol_v3::{CommitmentV3, ProgramIdV3};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, program_id_from_risc0_words_v3,
};
use zenodex_zrpf_risc0_spot_value_aggregate_l1_policy_v6::PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6;
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    decode_exact_source_opened_spot_value_leaf_statement_v6,
    encode_source_opened_spot_value_leaf_statement_v6,
    source_opened_spot_value_leaf_program_manifest_root_v6, SourceOpenedSpotValueLeafStatementV6,
};

use super::{
    verify_canonical_succinct_receipt_artifact, VerifiedNodeReceiptErrorV3,
    VerifiedReceiptProfileV3,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedSourceOpenedSpotValueLeafReceiptErrorV6 {
    ReceiptArtifact(VerifiedNodeReceiptErrorV3),
    StatementDecodeFailed,
    RuntimeIdentityDerivationFailed,
    ClaimBindingFailed,
    ExpectedStatementEncodingFailed,
    StatementBytesMismatch,
}

impl VerifiedSourceOpenedSpotValueLeafReceiptErrorV6 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::ReceiptArtifact(_) => "source_opened_spot_v6_receipt_artifact_rejected",
            Self::StatementDecodeFailed => "source_opened_spot_v6_statement_decode_failed",
            Self::RuntimeIdentityDerivationFailed => {
                "source_opened_spot_v6_runtime_identity_derivation_failed"
            }
            Self::ClaimBindingFailed => "source_opened_spot_v6_claim_binding_failed",
            Self::ExpectedStatementEncodingFailed => {
                "source_opened_spot_v6_expected_statement_encoding_failed"
            }
            Self::StatementBytesMismatch => "source_opened_spot_v6_statement_bytes_mismatch",
        }
    }
}

impl From<VerifiedNodeReceiptErrorV3> for VerifiedSourceOpenedSpotValueLeafReceiptErrorV6 {
    fn from(error: VerifiedNodeReceiptErrorV3) -> Self {
        Self::ReceiptArtifact(error)
    }
}

impl fmt::Display for VerifiedSourceOpenedSpotValueLeafReceiptErrorV6 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::ReceiptArtifact(_) => "source-opened Spot V6 receipt artifact rejected",
            Self::StatementDecodeFailed => {
                "verified source-opened Spot V6 statement strict decoding failed"
            }
            Self::RuntimeIdentityDerivationFailed => {
                "source-opened Spot V6 runtime identity derivation failed"
            }
            Self::ClaimBindingFailed => {
                "source-opened Spot V6 verified claim binding derivation failed"
            }
            Self::ExpectedStatementEncodingFailed => {
                "expected source-opened Spot V6 statement encoding failed"
            }
            Self::StatementBytesMismatch => {
                "verified source-opened Spot V6 statement differs from the expected statement"
            }
        })
    }
}

/// Receipt-authenticated source-opened ordinary Spot V6 statement.
///
/// Runtime identity is attached only after exact Succinct verification. The
/// inner statement contains no claimed self-image field. This capability
/// grants no ledger, settlement, release, governance, or production authority.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::SourceOpenedSpotValueLeafStatementV6;
/// use zenodex_zrpf_risc0_verifier::VerifiedSourceOpenedSpotValueLeafReceiptV6;
/// let statement: SourceOpenedSpotValueLeafStatementV6 = unimplemented!();
/// let _: VerifiedSourceOpenedSpotValueLeafReceiptV6 = statement.into();
/// ```
pub struct VerifiedSourceOpenedSpotValueLeafReceiptV6 {
    receipt: Receipt,
    receipt_profile: VerifiedReceiptProfileV3,
    statement: SourceOpenedSpotValueLeafStatementV6,
    verified_program_id: ProgramIdV3,
    verified_program_manifest_root: CommitmentV3,
    claim_binding: CommitmentV3,
}

impl VerifiedSourceOpenedSpotValueLeafReceiptV6 {
    /// Verify one receipt under the governed source-opened Spot V6 leaf image.
    pub fn verify_governed_canonical_succinct_bytes(
        receipt_bytes: &[u8],
    ) -> Result<Self, VerifiedSourceOpenedSpotValueLeafReceiptErrorV6> {
        Self::verify_canonical_succinct_bytes(
            receipt_bytes,
            PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6,
        )
    }

    fn verify_canonical_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
    ) -> Result<Self, VerifiedSourceOpenedSpotValueLeafReceiptErrorV6> {
        let (receipt, receipt_profile) =
            verify_canonical_succinct_receipt_artifact(receipt_bytes, expected_image_id)?;
        let statement =
            decode_exact_source_opened_spot_value_leaf_statement_v6(&receipt.journal.bytes)
                .map_err(|_| {
                    VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::StatementDecodeFailed
                })?;
        let verified_program_id =
            program_id_from_risc0_words_v3(expected_image_id).map_err(|_| {
                VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::RuntimeIdentityDerivationFailed
            })?;
        let verified_program_manifest_root =
            source_opened_spot_value_leaf_program_manifest_root_v6(verified_program_id).map_err(
                |_| {
                    VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::RuntimeIdentityDerivationFailed
                },
            )?;
        let claim_binding =
            derive_risc0_verified_claim_binding_v1(expected_image_id, &receipt.journal.bytes)
                .map_err(|_| VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::ClaimBindingFailed)?;
        Ok(Self {
            receipt,
            receipt_profile,
            statement,
            verified_program_id,
            verified_program_manifest_root,
            claim_binding,
        })
    }

    /// Verify one receipt and bind the exact expected governed V6 statement.
    pub fn verify_governed_exact_succinct_bytes(
        receipt_bytes: &[u8],
        expected_statement: &SourceOpenedSpotValueLeafStatementV6,
    ) -> Result<Self, VerifiedSourceOpenedSpotValueLeafReceiptErrorV6> {
        Self::verify_exact_succinct_bytes(
            receipt_bytes,
            PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6,
            expected_statement,
        )
    }

    fn verify_exact_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
        expected_statement: &SourceOpenedSpotValueLeafStatementV6,
    ) -> Result<Self, VerifiedSourceOpenedSpotValueLeafReceiptErrorV6> {
        let verified = Self::verify_canonical_succinct_bytes(receipt_bytes, expected_image_id)?;
        let expected_bytes = encode_source_opened_spot_value_leaf_statement_v6(expected_statement)
            .map_err(|_| {
                VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::ExpectedStatementEncodingFailed
            })?;
        if verified.receipt.journal.bytes != expected_bytes {
            return Err(VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::StatementBytesMismatch);
        }
        Ok(verified)
    }

    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn receipt_profile(&self) -> &VerifiedReceiptProfileV3 {
        &self.receipt_profile
    }

    pub const fn statement(&self) -> &SourceOpenedSpotValueLeafStatementV6 {
        &self.statement
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

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::VerifiedSourceOpenedSpotValueLeafReceiptErrorV6;
    use crate::VerifiedNodeReceiptErrorV3;

    #[test]
    fn reject_codes_are_stable_and_unique() {
        let errors = [
            VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::EmptyReceiptBytes,
            ),
            VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::StatementDecodeFailed,
            VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::RuntimeIdentityDerivationFailed,
            VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::ClaimBindingFailed,
            VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::ExpectedStatementEncodingFailed,
            VerifiedSourceOpenedSpotValueLeafReceiptErrorV6::StatementBytesMismatch,
        ];
        let codes: BTreeSet<&str> = errors.iter().map(|error| error.code()).collect();
        assert_eq!(codes.len(), errors.len());
    }
}
