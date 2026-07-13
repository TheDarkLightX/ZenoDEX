use core::fmt;
use std::vec::Vec;

use risc0_zkvm::Receipt;
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_admission_journal_v1, encode_settlement_admission_journal_v1,
    CommitmentV3, ProgramIdV3, SettlementAdmissionJournalV1,
};
use zenodex_zrpf_risc0_shared::derive_risc0_verified_claim_binding_v1;
use zenodex_zrpf_risc0_spot_settlement_root_policy_v6::{
    pinned_source_opened_spot_settlement_identity_v6,
    PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6,
};
use zenodex_zrpf_risc0_spot_settlement_v6_shared::{
    bind_source_opened_spot_settlement_guest_input_after_l2_receipt_verification_v3,
    compose_source_opened_spot_settlement_output_after_l2_verification_v3,
    decode_exact_source_opened_spot_settlement_guest_envelope_v3,
};
use zenodex_zrpf_risc0_spot_value_aggregate_root_policy_v6::PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6;

use super::{
    verify_canonical_succinct_receipt_artifact, VerifiedNodeReceiptErrorV3,
    VerifiedReceiptProfileV3,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedSourceOpenedSpotSettlementReceiptErrorV6 {
    ReceiptArtifact(VerifiedNodeReceiptErrorV3),
    JournalDecodeFailed,
    RuntimeIdentityDerivationFailed,
    ClaimBindingFailed,
    ExpectedJournalEncodingFailed,
    JournalBytesMismatch,
    GuestInputDecodeFailed,
    GuestInputBindingFailed,
    GuestInputRecompositionFailed,
}

impl VerifiedSourceOpenedSpotSettlementReceiptErrorV6 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::ReceiptArtifact(_) => "source_opened_spot_settlement_v6_receipt_rejected",
            Self::JournalDecodeFailed => "source_opened_spot_settlement_v6_journal_decode_failed",
            Self::RuntimeIdentityDerivationFailed => {
                "source_opened_spot_settlement_v6_runtime_identity_failed"
            }
            Self::ClaimBindingFailed => "source_opened_spot_settlement_v6_claim_binding_failed",
            Self::ExpectedJournalEncodingFailed => {
                "source_opened_spot_settlement_v6_expected_journal_encoding_failed"
            }
            Self::JournalBytesMismatch => "source_opened_spot_settlement_v6_journal_bytes_mismatch",
            Self::GuestInputDecodeFailed => {
                "source_opened_spot_settlement_v6_guest_input_decode_failed"
            }
            Self::GuestInputBindingFailed => {
                "source_opened_spot_settlement_v6_guest_input_binding_failed"
            }
            Self::GuestInputRecompositionFailed => {
                "source_opened_spot_settlement_v6_guest_input_recomposition_failed"
            }
        }
    }
}

impl From<VerifiedNodeReceiptErrorV3> for VerifiedSourceOpenedSpotSettlementReceiptErrorV6 {
    fn from(error: VerifiedNodeReceiptErrorV3) -> Self {
        Self::ReceiptArtifact(error)
    }
}

impl fmt::Display for VerifiedSourceOpenedSpotSettlementReceiptErrorV6 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::ReceiptArtifact(_) => "source-opened Spot V6 settlement receipt rejected",
            Self::JournalDecodeFailed => "settlement admission journal strict decoding failed",
            Self::RuntimeIdentityDerivationFailed => {
                "settlement governed runtime identity derivation failed"
            }
            Self::ClaimBindingFailed => "settlement verified claim binding derivation failed",
            Self::ExpectedJournalEncodingFailed => "expected settlement journal encoding failed",
            Self::JournalBytesMismatch => {
                "verified settlement journal differs from exact expected journal"
            }
            Self::GuestInputDecodeFailed => "settlement guest input strict decoding failed",
            Self::GuestInputBindingFailed => "settlement guest input binding failed",
            Self::GuestInputRecompositionFailed => {
                "settlement journal recomposition from exact guest input failed"
            }
        })
    }
}

/// Receipt and exact-guest-input authenticated V6 settlement admission.
///
/// The receipt is verified once. Its journal is then recomposed byte-for-byte
/// from the exact guest input before this capability can be constructed.
pub struct VerifiedSourceOpenedSpotSettlementAdmissionV6 {
    verified_receipt: VerifiedSourceOpenedSpotSettlementReceiptV6,
    exact_guest_input_bytes: Vec<u8>,
}

impl VerifiedSourceOpenedSpotSettlementAdmissionV6 {
    pub fn verify(
        canonical_receipt_bytes: &[u8],
        exact_guest_input_bytes: &[u8],
    ) -> Result<Self, VerifiedSourceOpenedSpotSettlementReceiptErrorV6> {
        let verified_receipt =
            VerifiedSourceOpenedSpotSettlementReceiptV6::verify_canonical_succinct_bytes(
                canonical_receipt_bytes,
            )?;
        let envelope =
            decode_exact_source_opened_spot_settlement_guest_envelope_v3(exact_guest_input_bytes)
                .map_err(|_| {
                VerifiedSourceOpenedSpotSettlementReceiptErrorV6::GuestInputDecodeFailed
            })?;
        let l2_claim = derive_risc0_verified_claim_binding_v1(
            PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6,
            envelope.proposal_bytes(),
        )
        .map_err(|_| VerifiedSourceOpenedSpotSettlementReceiptErrorV6::ClaimBindingFailed)?;
        let input =
            bind_source_opened_spot_settlement_guest_input_after_l2_receipt_verification_v3(
                envelope,
            )
            .map_err(|_| {
                VerifiedSourceOpenedSpotSettlementReceiptErrorV6::GuestInputBindingFailed
            })?;
        let expected =
            compose_source_opened_spot_settlement_output_after_l2_verification_v3(&input, l2_claim)
                .map_err(|_| {
                    VerifiedSourceOpenedSpotSettlementReceiptErrorV6::GuestInputRecompositionFailed
                })?;
        if verified_receipt.receipt.journal.bytes != expected {
            return Err(VerifiedSourceOpenedSpotSettlementReceiptErrorV6::JournalBytesMismatch);
        }
        Ok(Self {
            verified_receipt,
            exact_guest_input_bytes: exact_guest_input_bytes.to_vec(),
        })
    }

    pub const fn verified_receipt(&self) -> &VerifiedSourceOpenedSpotSettlementReceiptV6 {
        &self.verified_receipt
    }

    pub fn exact_guest_input_bytes(&self) -> &[u8] {
        &self.exact_guest_input_bytes
    }
}

/// Receipt-authenticated V6 settlement admission journal.
///
/// The private fields keep the receipt-verification capability separate from
/// the proof-neutral journal. This object grants no ledger or release authority.
pub struct VerifiedSourceOpenedSpotSettlementReceiptV6 {
    receipt: Receipt,
    receipt_profile: VerifiedReceiptProfileV3,
    journal: SettlementAdmissionJournalV1,
    verified_program_id: ProgramIdV3,
    verified_program_manifest_root: CommitmentV3,
    settlement_claim_binding: CommitmentV3,
}

impl VerifiedSourceOpenedSpotSettlementReceiptV6 {
    pub fn verify_canonical_succinct_bytes(
        receipt_bytes: &[u8],
    ) -> Result<Self, VerifiedSourceOpenedSpotSettlementReceiptErrorV6> {
        let (receipt, receipt_profile) = verify_canonical_succinct_receipt_artifact(
            receipt_bytes,
            PINNED_SOURCE_OPENED_SPOT_SETTLEMENT_IMAGE_ID_V6,
        )?;
        let journal = decode_exact_settlement_admission_journal_v1(&receipt.journal.bytes)
            .map_err(|_| VerifiedSourceOpenedSpotSettlementReceiptErrorV6::JournalDecodeFailed)?;
        let identity = pinned_source_opened_spot_settlement_identity_v6().map_err(|_| {
            VerifiedSourceOpenedSpotSettlementReceiptErrorV6::RuntimeIdentityDerivationFailed
        })?;
        let settlement_claim_binding = derive_risc0_verified_claim_binding_v1(
            identity.expected_image_id(),
            &receipt.journal.bytes,
        )
        .map_err(|_| VerifiedSourceOpenedSpotSettlementReceiptErrorV6::ClaimBindingFailed)?;
        Ok(Self {
            receipt,
            receipt_profile,
            journal,
            verified_program_id: identity.expected_program_id(),
            verified_program_manifest_root: identity.expected_manifest_root(),
            settlement_claim_binding,
        })
    }

    pub fn verify_exact_succinct_bytes(
        receipt_bytes: &[u8],
        expected_journal: &SettlementAdmissionJournalV1,
    ) -> Result<Self, VerifiedSourceOpenedSpotSettlementReceiptErrorV6> {
        let verified = Self::verify_canonical_succinct_bytes(receipt_bytes)?;
        let expected = encode_settlement_admission_journal_v1(expected_journal).map_err(|_| {
            VerifiedSourceOpenedSpotSettlementReceiptErrorV6::ExpectedJournalEncodingFailed
        })?;
        if verified.receipt.journal.bytes != expected {
            return Err(VerifiedSourceOpenedSpotSettlementReceiptErrorV6::JournalBytesMismatch);
        }
        Ok(verified)
    }

    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn receipt_profile(&self) -> &VerifiedReceiptProfileV3 {
        &self.receipt_profile
    }

    pub const fn journal(&self) -> &SettlementAdmissionJournalV1 {
        &self.journal
    }

    pub const fn verified_program_id(&self) -> ProgramIdV3 {
        self.verified_program_id
    }

    pub const fn verified_program_manifest_root(&self) -> CommitmentV3 {
        self.verified_program_manifest_root
    }

    pub const fn settlement_claim_binding(&self) -> CommitmentV3 {
        self.settlement_claim_binding
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::VerifiedSourceOpenedSpotSettlementReceiptErrorV6 as Error;
    use crate::VerifiedNodeReceiptErrorV3;

    #[test]
    fn reject_codes_are_stable_and_unique() {
        let errors = [
            Error::ReceiptArtifact(VerifiedNodeReceiptErrorV3::EmptyReceiptBytes),
            Error::JournalDecodeFailed,
            Error::RuntimeIdentityDerivationFailed,
            Error::ClaimBindingFailed,
            Error::ExpectedJournalEncodingFailed,
            Error::JournalBytesMismatch,
            Error::GuestInputDecodeFailed,
            Error::GuestInputBindingFailed,
            Error::GuestInputRecompositionFailed,
        ];
        let codes: BTreeSet<&str> = errors.iter().map(|error| error.code()).collect();
        assert_eq!(codes.len(), errors.len());
    }
}
