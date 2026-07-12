use core::fmt;

use risc0_zkvm::Receipt;
use sha2::{Digest as _, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_value_aggregate_proposal_v5, encode_value_aggregate_proposal_v5, CommitmentV3,
    NodeLevelV3, ProfileIdV3, ProgramIdV3, ProposedValueAggregateV5,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, risc0_image_words_to_bytes,
};

use super::{
    verify_canonical_succinct_receipt_artifact, VerifiedNodeReceiptErrorV3,
    VerifiedReceiptProfileV3,
};

const VERIFIED_IDENTITY_BINDING_DOMAIN_V5: &[u8] =
    b"zenodex.zrpf.value_aggregate_verified_identity.v5";

/// Governed parent identity expected by a V5 aggregate receipt consumer.
///
/// The expected aggregate level is checked against the receipt-authenticated
/// proposal. The profile and manifest are outer governed metadata: the V5
/// proposal does not carry them, so an authority-bearing consumer must commit
/// this identity in its certificate or release manifest. The evidence harness
/// supplies it explicitly and grants no governance, ledger, settlement,
/// release, or production authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ExpectedValueAggregateReceiptIdentityV5 {
    aggregate_level: NodeLevelV3,
    proof_profile_id: ProfileIdV3,
    program_manifest_root: CommitmentV3,
}

impl ExpectedValueAggregateReceiptIdentityV5 {
    pub fn new(
        aggregate_level: NodeLevelV3,
        proof_profile_id: ProfileIdV3,
        program_manifest_root: CommitmentV3,
    ) -> Result<Self, VerifiedValueAggregateReceiptErrorV5> {
        if aggregate_level == NodeLevelV3::LEAF {
            return Err(VerifiedValueAggregateReceiptErrorV5::InvalidExpectedAggregateLevel);
        }
        Ok(Self {
            aggregate_level,
            proof_profile_id,
            program_manifest_root,
        })
    }

    pub const fn aggregate_level(self) -> NodeLevelV3 {
        self.aggregate_level
    }

    pub const fn proof_profile_id(self) -> ProfileIdV3 {
        self.proof_profile_id
    }

    pub const fn program_manifest_root(self) -> CommitmentV3 {
        self.program_manifest_root
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedValueAggregateReceiptErrorV5 {
    InvalidExpectedAggregateLevel,
    ReceiptArtifact(VerifiedNodeReceiptErrorV3),
    ProposalDecodeFailed,
    AggregateLevelMismatch,
    ProgramIdDerivationFailed,
    ClaimBindingFailed,
    IdentityBindingFailed,
    ExpectedProposalEncodingFailed,
    ProposalBytesMismatch,
}

impl VerifiedValueAggregateReceiptErrorV5 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::InvalidExpectedAggregateLevel => {
                "value_aggregate_v5_invalid_expected_aggregate_level"
            }
            Self::ReceiptArtifact(_) => "value_aggregate_v5_receipt_artifact_rejected",
            Self::ProposalDecodeFailed => "value_aggregate_v5_proposal_decode_failed",
            Self::AggregateLevelMismatch => "value_aggregate_v5_aggregate_level_mismatch",
            Self::ProgramIdDerivationFailed => "value_aggregate_v5_program_id_derivation_failed",
            Self::ClaimBindingFailed => "value_aggregate_v5_claim_binding_failed",
            Self::IdentityBindingFailed => "value_aggregate_v5_identity_binding_failed",
            Self::ExpectedProposalEncodingFailed => {
                "expected_value_aggregate_v5_proposal_encoding_failed"
            }
            Self::ProposalBytesMismatch => "value_aggregate_v5_proposal_bytes_mismatch",
        }
    }
}

impl From<VerifiedNodeReceiptErrorV3> for VerifiedValueAggregateReceiptErrorV5 {
    fn from(error: VerifiedNodeReceiptErrorV3) -> Self {
        Self::ReceiptArtifact(error)
    }
}

impl fmt::Display for VerifiedValueAggregateReceiptErrorV5 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidExpectedAggregateLevel => {
                formatter.write_str("expected V5 aggregate level must be one or two")
            }
            Self::ReceiptArtifact(error) => {
                write!(formatter, "V5 aggregate receipt artifact rejected: {error}")
            }
            Self::ProposalDecodeFailed => {
                formatter.write_str("verified V5 aggregate proposal strict decoding failed")
            }
            Self::AggregateLevelMismatch => formatter
                .write_str("verified V5 proposal level differs from the governed expectation"),
            Self::ProgramIdDerivationFailed => formatter.write_str(
                "verified V5 aggregate program ID derivation from the expected image failed",
            ),
            Self::ClaimBindingFailed => {
                formatter.write_str("verified V5 aggregate RISC0 claim binding derivation failed")
            }
            Self::IdentityBindingFailed => formatter
                .write_str("verified V5 aggregate certificate identity binding derivation failed"),
            Self::ExpectedProposalEncodingFailed => {
                formatter.write_str("expected V5 aggregate proposal encoding failed")
            }
            Self::ProposalBytesMismatch => formatter
                .write_str("verified V5 aggregate proposal differs from the exact expectation"),
        }
    }
}

/// A V5 aggregate receipt whose runtime identity was attached only after
/// cryptographic verification under the expected image.
///
/// The aggregate level is receipt-authenticated and checked. The outer profile
/// and manifest are retained as typed expectations for a consuming certificate
/// or release manifest; they are not fields of the V5 guest journal and are not
/// part of the RISC0 claim binding by themselves. The derived certificate
/// identity binding commits them together with the verified claim and program;
/// a consuming certificate or release manifest must commit that binding.
///
/// The proof-neutral proposal cannot become this sealed verified type:
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::ProposedValueAggregateV5;
/// use zenodex_zrpf_risc0_verifier::VerifiedValueAggregateReceiptV5;
/// let proposal: ProposedValueAggregateV5 = unimplemented!();
/// let _: VerifiedValueAggregateReceiptV5 = proposal.into();
/// ```
///
/// A caller-supplied receipt object cannot bypass canonical persisted bytes:
///
/// ```compile_fail
/// use risc0_zkvm::Receipt;
/// use zenodex_zrpf_risc0_verifier::VerifiedValueAggregateReceiptV5;
/// let receipt: Receipt = unimplemented!();
/// let _: VerifiedValueAggregateReceiptV5 = receipt.into();
/// ```
pub struct VerifiedValueAggregateReceiptV5 {
    receipt: Receipt,
    receipt_profile: VerifiedReceiptProfileV3,
    proposal: ProposedValueAggregateV5,
    verified_program_id: ProgramIdV3,
    bound_identity: ExpectedValueAggregateReceiptIdentityV5,
    claim_binding: CommitmentV3,
    certificate_identity_binding: CommitmentV3,
}

impl VerifiedValueAggregateReceiptV5 {
    /// Verify canonical bounded receipt bytes before decoding their V5 journal.
    ///
    /// Reject precedence is image, byte bounds/canonicality, pinned receipt
    /// profile, cryptographic verification, strict V5 decoding, then attached
    /// runtime and governed identity material.
    pub fn verify_canonical_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
        expected_identity: ExpectedValueAggregateReceiptIdentityV5,
    ) -> Result<Self, VerifiedValueAggregateReceiptErrorV5> {
        let (receipt, receipt_profile) =
            verify_canonical_succinct_receipt_artifact(receipt_bytes, expected_image_id)?;
        let proposal = decode_exact_value_aggregate_proposal_v5(&receipt.journal.bytes)
            .map_err(|_| VerifiedValueAggregateReceiptErrorV5::ProposalDecodeFailed)?;
        require_expected_aggregate_level(proposal.aggregate_level(), expected_identity)?;
        let verified_program_id = verified_program_id(expected_image_id)?;
        let claim_binding =
            derive_risc0_verified_claim_binding_v1(expected_image_id, &receipt.journal.bytes)
                .map_err(|_| VerifiedValueAggregateReceiptErrorV5::ClaimBindingFailed)?;
        let certificate_identity_binding = derive_certificate_identity_binding_v5(
            claim_binding,
            verified_program_id,
            expected_identity,
        )?;
        Ok(Self {
            receipt,
            receipt_profile,
            proposal,
            verified_program_id,
            bound_identity: expected_identity,
            claim_binding,
            certificate_identity_binding,
        })
    }

    /// Verify canonical receipt bytes and bind the exact expected V5 proposal.
    pub fn verify_exact_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
        expected_identity: ExpectedValueAggregateReceiptIdentityV5,
        expected_proposal: &ProposedValueAggregateV5,
    ) -> Result<Self, VerifiedValueAggregateReceiptErrorV5> {
        let verified = Self::verify_canonical_succinct_bytes(
            receipt_bytes,
            expected_image_id,
            expected_identity,
        )?;
        let expected_bytes = encode_value_aggregate_proposal_v5(expected_proposal)
            .map_err(|_| VerifiedValueAggregateReceiptErrorV5::ExpectedProposalEncodingFailed)?;
        require_exact_proposal_bytes(&verified.receipt.journal.bytes, &expected_bytes)?;
        Ok(verified)
    }

    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn receipt_profile(&self) -> &VerifiedReceiptProfileV3 {
        &self.receipt_profile
    }

    pub const fn proposal(&self) -> &ProposedValueAggregateV5 {
        &self.proposal
    }

    pub const fn verified_program_id(&self) -> ProgramIdV3 {
        self.verified_program_id
    }

    pub const fn bound_identity(&self) -> ExpectedValueAggregateReceiptIdentityV5 {
        self.bound_identity
    }

    pub const fn claim_binding(&self) -> CommitmentV3 {
        self.claim_binding
    }

    pub const fn certificate_identity_binding(&self) -> CommitmentV3 {
        self.certificate_identity_binding
    }

    pub fn into_receipt(self) -> Receipt {
        self.receipt
    }
}

fn verified_program_id(
    expected_image_id: [u32; 8],
) -> Result<ProgramIdV3, VerifiedValueAggregateReceiptErrorV5> {
    ProgramIdV3::new(risc0_image_words_to_bytes(expected_image_id))
        .map_err(|_| VerifiedValueAggregateReceiptErrorV5::ProgramIdDerivationFailed)
}

fn require_exact_proposal_bytes(
    actual: &[u8],
    expected: &[u8],
) -> Result<(), VerifiedValueAggregateReceiptErrorV5> {
    if actual != expected {
        return Err(VerifiedValueAggregateReceiptErrorV5::ProposalBytesMismatch);
    }
    Ok(())
}

fn require_expected_aggregate_level(
    actual_level: u8,
    expected_identity: ExpectedValueAggregateReceiptIdentityV5,
) -> Result<(), VerifiedValueAggregateReceiptErrorV5> {
    if actual_level != expected_identity.aggregate_level().get() {
        return Err(VerifiedValueAggregateReceiptErrorV5::AggregateLevelMismatch);
    }
    Ok(())
}

fn derive_certificate_identity_binding_v5(
    claim_binding: CommitmentV3,
    verified_program_id: ProgramIdV3,
    expected_identity: ExpectedValueAggregateReceiptIdentityV5,
) -> Result<CommitmentV3, VerifiedValueAggregateReceiptErrorV5> {
    let domain_length = u16::try_from(VERIFIED_IDENTITY_BINDING_DOMAIN_V5.len())
        .map_err(|_| VerifiedValueAggregateReceiptErrorV5::IdentityBindingFailed)?;
    let mut hasher = Sha256::new();
    hasher.update(domain_length.to_be_bytes());
    hasher.update(VERIFIED_IDENTITY_BINDING_DOMAIN_V5);
    hasher.update(claim_binding.as_bytes());
    hasher.update(verified_program_id.as_bytes());
    hasher.update([expected_identity.aggregate_level().get()]);
    hasher.update(expected_identity.proof_profile_id().as_bytes());
    hasher.update(expected_identity.program_manifest_root().as_bytes());
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| VerifiedValueAggregateReceiptErrorV5::IdentityBindingFailed)
}

#[cfg(test)]
#[path = "value_aggregate_v5/tests.rs"]
mod tests;
