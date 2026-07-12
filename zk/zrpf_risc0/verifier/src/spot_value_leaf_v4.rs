use core::fmt;

use risc0_zkvm::Receipt;
use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v4, encode_node_journal_v4, CommitmentV3,
    ExpectedV1AdapterLeafIdentityV1, NodeJournalV4, NodeKindV3, ProgramIdV3,
    ProposedSemanticLeafV1, V1AdapterSemanticLeafOpeningV1,
};
use zenodex_zrpf_risc0_semantic_shared::spot_residual_application_statement_hash_v4;
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, program_id_from_risc0_words_v3,
    risc0_image_words_to_bytes,
};
use zenodex_zrpf_risc0_value_node_shared::{
    risc0_proof_system_id_v4, risc0_succinct_receipt_security_profile_id_v4,
    risc0_verifier_parameters_root_v4, spot_value_leaf_manifest_root_v4,
    spot_value_leaf_profile_id_v4, PINNED_V1_ADAPTER_IMAGE_ID_A,
};

use super::{
    verify_canonical_succinct_receipt_artifact, VerifiedNodeReceiptErrorV3,
    VerifiedReceiptProfileV3,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum SpotValueLeafIdentityFieldV4 {
    LeafShape,
    AdapterProgramId,
    AdapterProfileId,
    AdapterManifestRoot,
    AdapterCountUnitId,
    AdapterSemanticBinding,
    LeafRecordBinding,
    ProofProfileId,
    ProofSystemId,
    ReceiptSecurityProfileId,
    VerifierParametersRoot,
    ProgramManifestRoot,
    ApplicationStatementHash,
}

impl fmt::Display for SpotValueLeafIdentityFieldV4 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::LeafShape => "leaf shape",
            Self::AdapterProgramId => "adapter program ID",
            Self::AdapterProfileId => "adapter profile ID",
            Self::AdapterManifestRoot => "adapter manifest root",
            Self::AdapterCountUnitId => "adapter count unit ID",
            Self::AdapterSemanticBinding => "adapter semantic binding",
            Self::LeafRecordBinding => "semantic leaf-record binding",
            Self::ProofProfileId => "V4 proof profile ID",
            Self::ProofSystemId => "proof system ID",
            Self::ReceiptSecurityProfileId => "receipt security profile ID",
            Self::VerifierParametersRoot => "verifier parameters root",
            Self::ProgramManifestRoot => "program manifest root",
            Self::ApplicationStatementHash => "residual application statement hash",
        })
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedSpotValueLeafReceiptErrorV4 {
    ReceiptArtifact(VerifiedNodeReceiptErrorV3),
    JournalDecodeFailed,
    ProgramIdMismatch,
    GovernedDerivationFailed(SpotValueLeafIdentityFieldV4),
    GovernedMismatch(SpotValueLeafIdentityFieldV4),
    ClaimBindingFailed,
    ExpectedJournalEncodingFailed,
    JournalBytesMismatch,
}

impl VerifiedSpotValueLeafReceiptErrorV4 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::ReceiptArtifact(_) => "spot_value_leaf_receipt_artifact_rejected",
            Self::JournalDecodeFailed => "spot_value_leaf_journal_decode_failed",
            Self::ProgramIdMismatch => "spot_value_leaf_program_id_mismatch",
            Self::GovernedDerivationFailed(_) => "spot_value_leaf_governed_derivation_failed",
            Self::GovernedMismatch(_) => "spot_value_leaf_governed_mismatch",
            Self::ClaimBindingFailed => "spot_value_leaf_claim_binding_failed",
            Self::ExpectedJournalEncodingFailed => "expected_spot_value_leaf_encoding_failed",
            Self::JournalBytesMismatch => "spot_value_leaf_journal_bytes_mismatch",
        }
    }
}

impl From<VerifiedNodeReceiptErrorV3> for VerifiedSpotValueLeafReceiptErrorV4 {
    fn from(error: VerifiedNodeReceiptErrorV3) -> Self {
        Self::ReceiptArtifact(error)
    }
}

impl fmt::Display for VerifiedSpotValueLeafReceiptErrorV4 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ReceiptArtifact(error) => {
                write!(formatter, "Spot value leaf receipt rejected: {error}")
            }
            Self::JournalDecodeFailed => {
                formatter.write_str("verified Spot value leaf journal strict decoding failed")
            }
            Self::ProgramIdMismatch => formatter.write_str(
                "Spot value leaf program ID differs from the image used to verify the receipt",
            ),
            Self::GovernedDerivationFailed(field) => {
                write!(formatter, "failed to derive governed {field}")
            }
            Self::GovernedMismatch(field) => write!(formatter, "governed {field} mismatch"),
            Self::ClaimBindingFailed => {
                formatter.write_str("verified Spot value leaf claim binding derivation failed")
            }
            Self::ExpectedJournalEncodingFailed => {
                formatter.write_str("expected Spot value leaf journal encoding failed")
            }
            Self::JournalBytesMismatch => formatter.write_str(
                "verified Spot value leaf journal differs from the exact expected journal",
            ),
        }
    }
}

/// A cryptographically authenticated residual Spot value-leaf receipt.
///
/// This type authenticates a receipt under the caller-supplied expected guest
/// image, plus the compiled receipt security profile, pinned nested adapter
/// leaf, and self-derived residual statement. Governance of the outer expected
/// image remains separate. Raw scalar state endpoints are receipt-authenticated
/// because the journal commits only the lane hash needed to derive their vector
/// roots. This type grants no ledger, settlement, release, governance,
/// conservation, or production authority.
///
/// A proof-neutral journal cannot enter this typestate:
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::NodeJournalV4;
/// use zenodex_zrpf_risc0_verifier::historical_spot_value_leaf_v4::AuthenticatedSpotValueLeafReceiptV4;
/// let journal: NodeJournalV4 = unimplemented!();
/// let _: AuthenticatedSpotValueLeafReceiptV4 = journal.into();
/// ```
pub struct AuthenticatedSpotValueLeafReceiptV4 {
    receipt: Receipt,
    receipt_profile: VerifiedReceiptProfileV3,
    journal: NodeJournalV4,
    claim_binding: CommitmentV3,
}

impl AuthenticatedSpotValueLeafReceiptV4 {
    pub fn verify_canonical_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
    ) -> Result<Self, VerifiedSpotValueLeafReceiptErrorV4> {
        let (receipt, receipt_profile) =
            verify_canonical_succinct_receipt_artifact(receipt_bytes, expected_image_id)?;
        let journal = decode_exact_node_journal_v4(&receipt.journal.bytes)
            .map_err(|_| VerifiedSpotValueLeafReceiptErrorV4::JournalDecodeFailed)?;
        validate_authenticated_spot_value_leaf_journal_v4(&journal, expected_image_id)?;
        let claim_binding =
            derive_risc0_verified_claim_binding_v1(expected_image_id, &receipt.journal.bytes)
                .map_err(|_| VerifiedSpotValueLeafReceiptErrorV4::ClaimBindingFailed)?;
        Ok(Self {
            receipt,
            receipt_profile,
            journal,
            claim_binding,
        })
    }

    pub fn bind_exact_expected_journal(
        self,
        expected_journal: &NodeJournalV4,
    ) -> Result<ExactSpotValueLeafReceiptV4, VerifiedSpotValueLeafReceiptErrorV4> {
        let expected_bytes = encode_node_journal_v4(expected_journal)
            .map_err(|_| VerifiedSpotValueLeafReceiptErrorV4::ExpectedJournalEncodingFailed)?;
        if self.receipt.journal.bytes != expected_bytes {
            return Err(VerifiedSpotValueLeafReceiptErrorV4::JournalBytesMismatch);
        }
        Ok(ExactSpotValueLeafReceiptV4 {
            authenticated: self,
        })
    }

    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }

    pub const fn receipt_profile(&self) -> &VerifiedReceiptProfileV3 {
        &self.receipt_profile
    }

    pub const fn journal(&self) -> &NodeJournalV4 {
        &self.journal
    }

    pub const fn claim_binding(&self) -> CommitmentV3 {
        self.claim_binding
    }

    pub fn into_receipt(self) -> Receipt {
        self.receipt
    }
}

/// Authenticated residual receipt bound to one exact expected journal.
///
/// Expected-journal provenance remains a separate admission concern. This type
/// alone grants no ledger, settlement, governance, conservation, release, or
/// production authority.
pub struct ExactSpotValueLeafReceiptV4 {
    authenticated: AuthenticatedSpotValueLeafReceiptV4,
}

impl ExactSpotValueLeafReceiptV4 {
    pub fn verify_exact_succinct_bytes(
        receipt_bytes: &[u8],
        expected_image_id: [u32; 8],
        expected_journal: &NodeJournalV4,
    ) -> Result<Self, VerifiedSpotValueLeafReceiptErrorV4> {
        AuthenticatedSpotValueLeafReceiptV4::verify_canonical_succinct_bytes(
            receipt_bytes,
            expected_image_id,
        )?
        .bind_exact_expected_journal(expected_journal)
    }

    pub const fn authenticated(&self) -> &AuthenticatedSpotValueLeafReceiptV4 {
        &self.authenticated
    }

    pub const fn journal(&self) -> &NodeJournalV4 {
        self.authenticated.journal()
    }

    pub const fn claim_binding(&self) -> CommitmentV3 {
        self.authenticated.claim_binding()
    }

    pub fn into_receipt(self) -> Receipt {
        self.authenticated.into_receipt()
    }
}

fn validate_authenticated_spot_value_leaf_journal_v4(
    journal: &NodeJournalV4,
    expected_image_id: [u32; 8],
) -> Result<(), VerifiedSpotValueLeafReceiptErrorV4> {
    let verified_program_id = ProgramIdV3::new(risc0_image_words_to_bytes(expected_image_id))
        .map_err(|_| VerifiedSpotValueLeafReceiptErrorV4::ProgramIdMismatch)?;
    if journal.actual_program_id() != verified_program_id {
        return Err(VerifiedSpotValueLeafReceiptErrorV4::ProgramIdMismatch);
    }
    validate_v4_backend_identity(journal, verified_program_id)?;
    validate_adapter_leaf_and_record(journal)?;
    validate_residual_statement(journal)
}

fn validate_v4_backend_identity(
    journal: &NodeJournalV4,
    verified_program_id: ProgramIdV3,
) -> Result<(), VerifiedSpotValueLeafReceiptErrorV4> {
    require_identity(
        journal.proof_profile_id(),
        derive_identity(SpotValueLeafIdentityFieldV4::ProofProfileId, || {
            spot_value_leaf_profile_id_v4()
        })?,
        SpotValueLeafIdentityFieldV4::ProofProfileId,
    )?;
    require_identity(
        journal.proof_system_id(),
        derive_identity(SpotValueLeafIdentityFieldV4::ProofSystemId, || {
            risc0_proof_system_id_v4()
        })?,
        SpotValueLeafIdentityFieldV4::ProofSystemId,
    )?;
    require_identity(
        journal.receipt_security_profile_id(),
        derive_identity(
            SpotValueLeafIdentityFieldV4::ReceiptSecurityProfileId,
            risc0_succinct_receipt_security_profile_id_v4,
        )?,
        SpotValueLeafIdentityFieldV4::ReceiptSecurityProfileId,
    )?;
    require_identity(
        journal.verifier_parameters_root(),
        derive_identity(
            SpotValueLeafIdentityFieldV4::VerifierParametersRoot,
            risc0_verifier_parameters_root_v4,
        )?,
        SpotValueLeafIdentityFieldV4::VerifierParametersRoot,
    )?;
    let adapter_program_id = adapter_program_id()?;
    let manifest = derive_identity(SpotValueLeafIdentityFieldV4::ProgramManifestRoot, || {
        spot_value_leaf_manifest_root_v4(verified_program_id, adapter_program_id)
    })?;
    require_identity(
        journal.program_manifest_root(),
        manifest,
        SpotValueLeafIdentityFieldV4::ProgramManifestRoot,
    )
}

fn validate_adapter_leaf_and_record(
    journal: &NodeJournalV4,
) -> Result<(), VerifiedSpotValueLeafReceiptErrorV4> {
    let structural = journal.structural();
    let subtree = journal.semantic_subtree();
    if structural.node_kind() != NodeKindV3::Leaf
        || structural.operation_count() != 1
        || structural.immediate_child_count() != 0
        || subtree.leaf_count() != 1
        || subtree.leaf_records().len() != 1
        || !journal.child_semantic_journal_hashes().is_empty()
    {
        return mismatch(SpotValueLeafIdentityFieldV4::LeafShape);
    }
    let expected = ExpectedV1AdapterLeafIdentityV1::new(adapter_program_id()?).map_err(|_| {
        VerifiedSpotValueLeafReceiptErrorV4::GovernedDerivationFailed(
            SpotValueLeafIdentityFieldV4::AdapterSemanticBinding,
        )
    })?;
    require_adapter_identity(structural, expected)?;
    let record = &subtree.leaf_records()[0];
    let leaf = ProposedSemanticLeafV1::bind_v1_adapter_journal(
        structural,
        V1AdapterSemanticLeafOpeningV1::new(record.semantic_source_id()),
        &expected,
    )
    .map_err(|_| {
        VerifiedSpotValueLeafReceiptErrorV4::GovernedMismatch(
            SpotValueLeafIdentityFieldV4::AdapterSemanticBinding,
        )
    })?;
    validate_leaf_record_binding(record, &leaf)
}

fn require_adapter_identity(
    structural: &zenodex_zrpf_protocol_v3::NodeJournalV3,
    expected: ExpectedV1AdapterLeafIdentityV1,
) -> Result<(), VerifiedSpotValueLeafReceiptErrorV4> {
    for (matches, field) in [
        (
            structural.actual_program_id() == expected.adapter_program_id(),
            SpotValueLeafIdentityFieldV4::AdapterProgramId,
        ),
        (
            structural.proof_profile_id() == expected.adapter_profile_id(),
            SpotValueLeafIdentityFieldV4::AdapterProfileId,
        ),
        (
            structural.program_manifest_root() == expected.adapter_manifest_root(),
            SpotValueLeafIdentityFieldV4::AdapterManifestRoot,
        ),
        (
            structural.count_unit_id() == expected.count_unit_id(),
            SpotValueLeafIdentityFieldV4::AdapterCountUnitId,
        ),
    ] {
        if !matches {
            return mismatch(field);
        }
    }
    Ok(())
}

fn validate_leaf_record_binding(
    record: &zenodex_zrpf_protocol_v3::SemanticValueLeafRecordV2,
    leaf: &ProposedSemanticLeafV1,
) -> Result<(), VerifiedSpotValueLeafReceiptErrorV4> {
    let leaf_hash = leaf.canonical_hash().map_err(|_| {
        VerifiedSpotValueLeafReceiptErrorV4::GovernedDerivationFailed(
            SpotValueLeafIdentityFieldV4::LeafRecordBinding,
        )
    })?;
    let commitments = leaf.commitments().to_input();
    let matches = record.partition() == leaf.partition()
        && record.semantic_leaf_hash() == leaf_hash
        && record.source_claim_id() == leaf.source_claim_id().into_commitment()
        && record.semantic_source_id() == leaf.semantic_source_id().into_commitment()
        && record.task_id() == leaf.task_id()
        && record.pre_state_vector_root() == commitments.pre_state_vector_root
        && record.post_state_vector_root() == commitments.post_state_vector_root
        && record.transaction_root() == commitments.transaction_root
        && record.effect_root() == commitments.effect_root
        && record.asset_delta_root() == commitments.asset_delta_root;
    if !matches {
        return mismatch(SpotValueLeafIdentityFieldV4::LeafRecordBinding);
    }
    Ok(())
}

fn validate_residual_statement(
    journal: &NodeJournalV4,
) -> Result<(), VerifiedSpotValueLeafReceiptErrorV4> {
    let expected = spot_residual_application_statement_hash_v4(journal.semantic_subtree())
        .map_err(|_| {
            VerifiedSpotValueLeafReceiptErrorV4::GovernedDerivationFailed(
                SpotValueLeafIdentityFieldV4::ApplicationStatementHash,
            )
        })?;
    require_identity(
        journal.application_statement_hash(),
        expected,
        SpotValueLeafIdentityFieldV4::ApplicationStatementHash,
    )
}

fn adapter_program_id() -> Result<ProgramIdV3, VerifiedSpotValueLeafReceiptErrorV4> {
    program_id_from_risc0_words_v3(PINNED_V1_ADAPTER_IMAGE_ID_A).map_err(|_| {
        VerifiedSpotValueLeafReceiptErrorV4::GovernedDerivationFailed(
            SpotValueLeafIdentityFieldV4::AdapterProgramId,
        )
    })
}

fn derive_identity<T, E>(
    field: SpotValueLeafIdentityFieldV4,
    derive: impl FnOnce() -> Result<T, E>,
) -> Result<T, VerifiedSpotValueLeafReceiptErrorV4> {
    derive().map_err(|_| VerifiedSpotValueLeafReceiptErrorV4::GovernedDerivationFailed(field))
}

fn require_identity<T: PartialEq>(
    actual: T,
    expected: T,
    field: SpotValueLeafIdentityFieldV4,
) -> Result<(), VerifiedSpotValueLeafReceiptErrorV4> {
    if actual != expected {
        return mismatch(field);
    }
    Ok(())
}

fn mismatch<T>(
    field: SpotValueLeafIdentityFieldV4,
) -> Result<T, VerifiedSpotValueLeafReceiptErrorV4> {
    Err(VerifiedSpotValueLeafReceiptErrorV4::GovernedMismatch(field))
}

#[cfg(test)]
#[path = "spot_value_leaf_v4/tests.rs"]
mod tests;
