use core::fmt;

use risc0_zkvm::{InnerReceipt, Receipt};
use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v3, encode_node_journal_v3, CommitmentV3, NodeJournalV3, ProgramIdV3,
    ProjectedChildDescriptorV3,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, risc0_image_words_to_bytes,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedNodeReceiptErrorV3 {
    NonSuccinctReceipt,
    ReceiptVerificationFailed,
    ExpectedJournalEncodingFailed,
    JournalBytesMismatch,
    JournalDecodeFailed,
    ProgramIdMismatch,
    ClaimBindingFailed,
    ChildProjectionFailed,
}

impl fmt::Display for VerifiedNodeReceiptErrorV3 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::NonSuccinctReceipt => "node receipt is not Succinct",
            Self::ReceiptVerificationFailed => "node receipt verification failed",
            Self::ExpectedJournalEncodingFailed => "expected node journal encoding failed",
            Self::JournalBytesMismatch => "node journal differs from the expected journal",
            Self::JournalDecodeFailed => "verified node journal strict decoding failed",
            Self::ProgramIdMismatch => {
                "node journal program ID differs from the image used to verify the receipt"
            }
            Self::ClaimBindingFailed => "verified RISC0 claim binding derivation failed",
            Self::ChildProjectionFailed => "verified child descriptor projection failed",
        })
    }
}

/// A receipt and V3 journal that have crossed the complete host verification
/// boundary. Fields are private so callers cannot construct this type from an
/// unverified receipt or from journal bytes alone.
pub struct VerifiedNodeReceiptV3 {
    receipt: Receipt,
    journal: NodeJournalV3,
    claim_binding: CommitmentV3,
    child_descriptor: ProjectedChildDescriptorV3,
}

impl VerifiedNodeReceiptV3 {
    pub fn verify_canonical_succinct(
        receipt: Receipt,
        expected_image_id: [u32; 8],
    ) -> Result<Self, VerifiedNodeReceiptErrorV3> {
        if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
            return Err(VerifiedNodeReceiptErrorV3::NonSuccinctReceipt);
        }
        receipt
            .verify(expected_image_id)
            .map_err(|_| VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed)?;
        let journal = decode_exact_node_journal_v3(&receipt.journal.bytes)
            .map_err(|_| VerifiedNodeReceiptErrorV3::JournalDecodeFailed)?;
        let verified_program_id = ProgramIdV3::new(risc0_image_words_to_bytes(expected_image_id))
            .map_err(|_| VerifiedNodeReceiptErrorV3::ProgramIdMismatch)?;
        if journal.actual_program_id() != verified_program_id {
            return Err(VerifiedNodeReceiptErrorV3::ProgramIdMismatch);
        }
        let claim_binding =
            derive_risc0_verified_claim_binding_v1(expected_image_id, &receipt.journal.bytes)
                .map_err(|_| VerifiedNodeReceiptErrorV3::ClaimBindingFailed)?;
        let child_descriptor = ProjectedChildDescriptorV3::project_canonical_journal(
            claim_binding,
            &receipt.journal.bytes,
        )
        .map_err(|_| VerifiedNodeReceiptErrorV3::ChildProjectionFailed)?;
        Ok(Self {
            receipt,
            journal,
            claim_binding,
            child_descriptor,
        })
    }

    pub fn verify_exact_succinct(
        receipt: Receipt,
        expected_image_id: [u32; 8],
        expected_journal: &NodeJournalV3,
    ) -> Result<Self, VerifiedNodeReceiptErrorV3> {
        let verified = Self::verify_canonical_succinct(receipt, expected_image_id)?;
        let expected_bytes = encode_node_journal_v3(expected_journal)
            .map_err(|_| VerifiedNodeReceiptErrorV3::ExpectedJournalEncodingFailed)?;
        if verified.receipt.journal.bytes != expected_bytes {
            return Err(VerifiedNodeReceiptErrorV3::JournalBytesMismatch);
        }
        Ok(verified)
    }

    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn journal(&self) -> &NodeJournalV3 {
        &self.journal
    }

    pub const fn claim_binding(&self) -> CommitmentV3 {
        self.claim_binding
    }

    pub const fn child_descriptor(&self) -> &ProjectedChildDescriptorV3 {
        &self.child_descriptor
    }

    pub fn into_receipt(self) -> Receipt {
        self.receipt
    }
}

#[cfg(test)]
mod tests {
    use zenodex_zrpf_risc0_shared::{
        derive_risc0_verified_claim_binding_v1, risc0_image_words_to_bytes,
    };

    #[test]
    fn image_words_use_risc0_digest_byte_order() {
        assert_eq!(
            risc0_image_words_to_bytes([
                0x0302_0100,
                0x0706_0504,
                0x0b0a_0908,
                0x0f0e_0d0c,
                0x1312_1110,
                0x1716_1514,
                0x1b1a_1918,
                0x1f1e_1d1c,
            ]),
            core::array::from_fn(|index| index as u8),
        );
    }

    #[test]
    fn verified_claim_binding_binds_program_and_exact_journal() {
        let image = [1u32; 8];
        let baseline = derive_risc0_verified_claim_binding_v1(image, b"journal").expect("binding");
        assert_ne!(
            baseline,
            derive_risc0_verified_claim_binding_v1([2u32; 8], b"journal").expect("binding")
        );
        assert_ne!(
            baseline,
            derive_risc0_verified_claim_binding_v1(image, b"journal\0").expect("binding")
        );
    }
}
