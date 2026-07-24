//! Sealed host verification boundary for Spot settlement V7.
//!
//! The only production-shaped constructor accepts bounded canonical V7 and V6
//! receipt bytes plus the exact guest input bytes. It authenticates and retains
//! the actual V6 child artifact, verifies the V7 receipt once, then recomposes
//! the entire journal from the retained guest input. The resulting private
//! value retains complete pre/post state openings and the internally derived
//! Plan B for a future atomic store.

use core::fmt;
use std::collections::BTreeMap;

use risc0_zkvm::{
    sha::Digestible, InnerReceipt, Receipt, SuccinctReceiptVerifierParameters, VerifierContext,
};
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    encode_settlement_effect_plan_v2, CommitmentV3, ProfileIdV3, ProgramIdV3,
    SettlementEffectPlanV2,
};
use zenodex_zrpf_risc0_shared::{
    derive_risc0_verified_claim_binding_v1, program_id_from_risc0_words_v3,
};
use zenodex_zrpf_risc0_spot_settlement_v7_child_policy::final_source_opened_spot_settlement_v6_image_id_v1;
use zenodex_zrpf_risc0_spot_settlement_v7_methods::ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID;
use zenodex_zrpf_risc0_spot_settlement_v7_shared::{
    compose_spot_settlement_v7_after_source_receipt_verification_v1,
    decode_exact_spot_settlement_v7_guest_envelope_v1, decode_exact_spot_settlement_v7_journal_v1,
    encode_spot_settlement_v7_journal_v1, required_source_child_receipt_security_profile_id_v1,
    SourceOpenedSpotSettlementV7OpeningV1, SpotSettlementV7JournalV1,
    MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1,
    MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1, MAX_SPOT_SETTLEMENT_V7_JOURNAL_BYTES_V1,
    SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_VERSION_V1, SPOT_SETTLEMENT_V7_JOURNAL_MAGIC_V1,
    SPOT_SETTLEMENT_V7_JOURNAL_VERSION_V1,
};
use zenodex_zrpf_risc0_verifier::VerifiedSourceOpenedSpotSettlementReceiptV6;

pub const SPOT_SETTLEMENT_V7_VERIFIER_SCHEMA_V1: &str =
    "zenodex/zrpf_spot_settlement_v7_verified_output/v1";
pub const SPOT_SETTLEMENT_V7_VERIFIER_SETTLEMENT_AUTHORITY: bool = false;
pub const SPOT_SETTLEMENT_V7_VERIFIER_PRODUCTION_AUTHORITY: bool = false;
pub const ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1: &str =
    "risc0_succinct_poseidon2_resolve_3_0_5_v1";
pub const MAX_CANONICAL_SPOT_SETTLEMENT_V7_RECEIPT_BYTES_V1: usize = 16 * 1_024 * 1_024;

pub const SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_MAGIC_V1: [u8; 8] = *b"ZSPTV7O1";
pub const SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_VERSION_V1: u16 = 1;

const RECEIPT_KIND_SUCCINCT_V1: &str = "succinct";
const RECEIPT_VERIFIER_PARAMETERS_V1: &str =
    "ece5e9b8ae2cd6ea6b1827b464ff0348f9a7f4decd269c0087fdfd75098da013";
const RECEIPT_HASHFN_POSEIDON2_V1: &str = "poseidon2";
const RECEIPT_CONTROL_ID_V1: &str =
    "53a7b23d07f99e5d5685e85874f5181e8486aa267a0ae607ffe9ba47c8bdda4a";
const V7_PROFILE_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_settlement_v7.profile.v1";
const V7_MANIFEST_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_settlement_v7.manifest.v1";
const OUTPUT_FIXED_FIELD_COUNT_V1: usize = 19;
const OUTPUT_HEADER_BYTES_V1: usize = 8 + 2 + 4 + 4 + 4 + 4 + OUTPUT_FIXED_FIELD_COUNT_V1 * 32;

const _: [(); 1] = [(); (OUTPUT_HEADER_BYTES_V1 + MAX_SPOT_SETTLEMENT_V7_JOURNAL_BYTES_V1
    <= MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1) as usize];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum VerifiedSpotSettlementV7ErrorV1 {
    FinalV6ImageIdUnmaterialized,
    V7ImageIdUnmaterialized,
    EmptyGuestInput,
    GuestInputTooLarge { actual: usize, maximum: usize },
    GuestInputDecode,
    EmptyReceiptBytes,
    ReceiptBytesTooLarge { actual: usize, maximum: usize },
    ReceiptJsonDecode,
    ReceiptJsonEncode,
    NonCanonicalReceiptJson,
    NonSuccinctReceipt,
    ReceiptMetadataMismatch,
    ReceiptProfileMismatch(&'static str),
    ReceiptVerificationFailed,
    SourceChildReceiptVerificationFailed,
    SourceChildProgramMismatch,
    SourceChildReceiptProfileMismatch,
    SourceChildJournalMismatch,
    VerifiedJournalDecode,
    ChildClaimBinding,
    JournalRecomposition,
    JournalBytesMismatch,
    RuntimeIdentityDerivation,
    OutputEncoding,
    OutputDecode,
    NonCanonicalOutput,
    OutputTooLarge { actual: usize, maximum: usize },
}

impl VerifiedSpotSettlementV7ErrorV1 {
    pub const fn code(self) -> &'static str {
        match self {
            Self::FinalV6ImageIdUnmaterialized => "final_v6_image_id_unmaterialized",
            Self::V7ImageIdUnmaterialized => "v7_image_id_unmaterialized",
            Self::EmptyGuestInput => "empty_guest_input",
            Self::GuestInputTooLarge { .. } => "guest_input_too_large",
            Self::GuestInputDecode => "guest_input_decode",
            Self::EmptyReceiptBytes => "empty_receipt_bytes",
            Self::ReceiptBytesTooLarge { .. } => "receipt_bytes_too_large",
            Self::ReceiptJsonDecode => "receipt_json_decode",
            Self::ReceiptJsonEncode => "receipt_json_encode",
            Self::NonCanonicalReceiptJson => "noncanonical_receipt_json",
            Self::NonSuccinctReceipt => "non_succinct_receipt",
            Self::ReceiptMetadataMismatch => "receipt_metadata_mismatch",
            Self::ReceiptProfileMismatch(_) => "receipt_profile_mismatch",
            Self::ReceiptVerificationFailed => "receipt_verification_failed",
            Self::SourceChildReceiptVerificationFailed => {
                "source_child_receipt_verification_failed"
            }
            Self::SourceChildProgramMismatch => "source_child_program_mismatch",
            Self::SourceChildReceiptProfileMismatch => "source_child_receipt_profile_mismatch",
            Self::SourceChildJournalMismatch => "source_child_journal_mismatch",
            Self::VerifiedJournalDecode => "verified_journal_decode",
            Self::ChildClaimBinding => "child_claim_binding",
            Self::JournalRecomposition => "journal_recomposition",
            Self::JournalBytesMismatch => "journal_bytes_mismatch",
            Self::RuntimeIdentityDerivation => "runtime_identity_derivation",
            Self::OutputEncoding => "output_encoding",
            Self::OutputDecode => "output_decode",
            Self::NonCanonicalOutput => "noncanonical_output",
            Self::OutputTooLarge { .. } => "output_too_large",
        }
    }
}

impl fmt::Display for VerifiedSpotSettlementV7ErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::GuestInputTooLarge { actual, maximum }
            | Self::ReceiptBytesTooLarge { actual, maximum }
            | Self::OutputTooLarge { actual, maximum } => {
                write!(formatter, "{}: {actual} > {maximum}", self.code())
            }
            Self::ReceiptProfileMismatch(field) => {
                write!(formatter, "receipt profile mismatch: {field}")
            }
            _ => formatter.write_str(self.code()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct VerifiedReceiptProfileV1 {
    profile_id: &'static str,
    receipt_kind: &'static str,
    verifier_parameters: String,
    hashfn: String,
    control_id: String,
}

impl VerifiedReceiptProfileV1 {
    pub const fn profile_id(&self) -> &'static str {
        self.profile_id
    }
    pub const fn receipt_kind(&self) -> &'static str {
        self.receipt_kind
    }
    pub fn verifier_parameters(&self) -> &str {
        &self.verifier_parameters
    }
    pub fn hashfn(&self) -> &str {
        &self.hashfn
    }
    pub fn control_id(&self) -> &str {
        &self.control_id
    }
}

/// Receipt-authenticated, exact-recomposed settlement capability.
///
/// This type is deliberately non-cloneable and non-serializable. The full
/// opening remains available only until a future atomic store consumes it.
///
/// ```compile_fail
/// use risc0_zkvm::Receipt;
/// use zenodex_zrpf_risc0_spot_settlement_v7_verifier::VerifiedSpotSettlementV7ReceiptV1;
/// let receipt: Receipt = unimplemented!();
/// let _: VerifiedSpotSettlementV7ReceiptV1 = receipt.into();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v7_verifier::VerifiedSpotSettlementV7ReceiptV1;
/// let value: VerifiedSpotSettlementV7ReceiptV1 = unimplemented!();
/// let _ = value.settlement_authority();
/// ```
pub struct VerifiedSpotSettlementV7ReceiptV1 {
    receipt: Receipt,
    receipt_profile: VerifiedReceiptProfileV1,
    verified_source_child: VerifiedSourceOpenedSpotSettlementReceiptV6,
    verified_program_id: ProgramIdV3,
    verified_profile_id: ProfileIdV3,
    verified_program_manifest_root: CommitmentV3,
    journal: SpotSettlementV7JournalV1,
    journal_sha256: CommitmentV3,
    exact_guest_input_bytes: Vec<u8>,
    opening: SourceOpenedSpotSettlementV7OpeningV1,
}

impl VerifiedSpotSettlementV7ReceiptV1 {
    pub const fn receipt(&self) -> &Receipt {
        &self.receipt
    }
    pub const fn receipt_profile(&self) -> &VerifiedReceiptProfileV1 {
        &self.receipt_profile
    }
    pub const fn verified_source_child(&self) -> &VerifiedSourceOpenedSpotSettlementReceiptV6 {
        &self.verified_source_child
    }
    pub const fn verified_program_id(&self) -> ProgramIdV3 {
        self.verified_program_id
    }
    pub const fn verified_profile_id(&self) -> ProfileIdV3 {
        self.verified_profile_id
    }
    pub const fn verified_program_manifest_root(&self) -> CommitmentV3 {
        self.verified_program_manifest_root
    }
    pub const fn journal(&self) -> &SpotSettlementV7JournalV1 {
        &self.journal
    }
    pub const fn journal_sha256(&self) -> CommitmentV3 {
        self.journal_sha256
    }
    pub fn exact_guest_input_bytes(&self) -> &[u8] {
        &self.exact_guest_input_bytes
    }
    pub const fn pre_state(&self) -> &tau_state_proof_risc0_shared::DexSnapshotV1 {
        self.opening.pre_state()
    }
    pub const fn post_state(&self) -> &tau_state_proof_risc0_shared::DexSnapshotV1 {
        self.opening.post_state()
    }
    pub const fn plan_b(&self) -> &SettlementEffectPlanV2 {
        self.opening.plan_b()
    }

    /// Freeze the data-only payload consumed after Firecracker validates the
    /// VM execution record. Plan B is encoded once inside `journal_bytes`; the
    /// decoder exposes its exact canonical bytes from that validated journal.
    pub fn firecracker_output(
        &self,
    ) -> Result<SpotSettlementV7VerifierOutputV1, VerifiedSpotSettlementV7ErrorV1> {
        let journal_bytes = encode_spot_settlement_v7_journal_v1(&self.journal)
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
        SpotSettlementV7VerifierOutputV1::from_verified(self, journal_bytes)
    }
}

/// Data-only result carried by the one-shot Firecracker replay payload.
///
/// This record grants no Python or ledger authority on its own. The adapter
/// must first validate the governed Firecracker execution, then match the host
/// input length/hash against the exact bytes it supplied.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v7_verifier::SpotSettlementV7VerifierOutputV1;
/// let output: SpotSettlementV7VerifierOutputV1 = unimplemented!();
/// let _ = output.settlement_authority();
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpotSettlementV7VerifierOutputV1 {
    verified_program_id: ProgramIdV3,
    verified_profile_id: ProfileIdV3,
    verified_program_manifest_root: CommitmentV3,
    journal_sha256: CommitmentV3,
    source_child_program_id: ProgramIdV3,
    required_source_child_receipt_security_profile_id: CommitmentV3,
    source_child_claim_binding: CommitmentV3,
    source_child_journal_sha256: CommitmentV3,
    data_availability_certificate_root: CommitmentV3,
    data_root: CommitmentV3,
    settlement_effect_plan_commitment: CommitmentV3,
    settlement_effect_plan_bytes_sha256: CommitmentV3,
    pre_state_root: CommitmentV3,
    post_state_root: CommitmentV3,
    action_ids_root: CommitmentV3,
    action_authorization_bindings_root: CommitmentV3,
    authorization_grant_spends_root: CommitmentV3,
    consumed_object_ids_root: CommitmentV3,
    state_root_host_input_sha256: CommitmentV3,
    state_root_host_input_length: u32,
    journal_bytes: Vec<u8>,
}

impl SpotSettlementV7VerifierOutputV1 {
    fn from_verified(
        verified: &VerifiedSpotSettlementV7ReceiptV1,
        journal_bytes: Vec<u8>,
    ) -> Result<Self, VerifiedSpotSettlementV7ErrorV1> {
        let journal = verified.journal();
        let plan = journal.settlement_effect_plan();
        let exact_plan_b_bytes = encode_settlement_effect_plan_v2(plan)
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
        let exact_plan_b_bytes_sha256 = sha256_commitment(&exact_plan_b_bytes)?;
        let batch = plan.economic_action_batch();
        let value = Self {
            verified_program_id: verified.verified_program_id,
            verified_profile_id: verified.verified_profile_id,
            verified_program_manifest_root: verified.verified_program_manifest_root,
            journal_sha256: verified.journal_sha256,
            source_child_program_id: journal.source_child_program_id(),
            required_source_child_receipt_security_profile_id: journal
                .required_source_child_receipt_security_profile_id(),
            source_child_claim_binding: journal.source_child_claim_binding(),
            source_child_journal_sha256: journal.source_child_journal_sha256(),
            data_availability_certificate_root: journal.data_availability_certificate_root(),
            data_root: journal.data_root(),
            settlement_effect_plan_commitment: journal.settlement_effect_plan_commitment(),
            settlement_effect_plan_bytes_sha256: exact_plan_b_bytes_sha256,
            pre_state_root: journal.effect_binding_journal().pre_state_root(),
            post_state_root: journal.effect_binding_journal().post_state_root(),
            action_ids_root: journal.action_ids_root(),
            action_authorization_bindings_root: batch.action_authorization_bindings_root(),
            authorization_grant_spends_root: batch.authorization_grant_spends_root(),
            consumed_object_ids_root: batch.consumed_object_ids_root(),
            state_root_host_input_sha256: journal.state_root_host_input_sha256(),
            state_root_host_input_length: journal.state_root_host_input_length(),
            journal_bytes,
        };
        let encoded = encode_spot_settlement_v7_verifier_output_v1(&value)?;
        if encoded.len() > MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1 {
            return Err(VerifiedSpotSettlementV7ErrorV1::OutputTooLarge {
                actual: encoded.len(),
                maximum: MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1,
            });
        }
        Ok(value)
    }

    pub const fn state_root_host_input_length(&self) -> u32 {
        self.state_root_host_input_length
    }
    pub const fn verified_program_id(&self) -> ProgramIdV3 {
        self.verified_program_id
    }
    pub const fn verified_profile_id(&self) -> ProfileIdV3 {
        self.verified_profile_id
    }
    pub const fn verified_program_manifest_root(&self) -> CommitmentV3 {
        self.verified_program_manifest_root
    }
    pub const fn journal_sha256(&self) -> CommitmentV3 {
        self.journal_sha256
    }
    pub const fn source_child_program_id(&self) -> ProgramIdV3 {
        self.source_child_program_id
    }
    pub const fn required_source_child_receipt_security_profile_id(&self) -> CommitmentV3 {
        self.required_source_child_receipt_security_profile_id
    }
    pub const fn source_child_claim_binding(&self) -> CommitmentV3 {
        self.source_child_claim_binding
    }
    pub const fn source_child_journal_sha256(&self) -> CommitmentV3 {
        self.source_child_journal_sha256
    }
    pub const fn data_availability_certificate_root(&self) -> CommitmentV3 {
        self.data_availability_certificate_root
    }
    pub const fn data_root(&self) -> CommitmentV3 {
        self.data_root
    }
    pub const fn settlement_effect_plan_commitment(&self) -> CommitmentV3 {
        self.settlement_effect_plan_commitment
    }
    pub const fn settlement_effect_plan_bytes_sha256(&self) -> CommitmentV3 {
        self.settlement_effect_plan_bytes_sha256
    }
    pub const fn pre_state_root(&self) -> CommitmentV3 {
        self.pre_state_root
    }
    pub const fn post_state_root(&self) -> CommitmentV3 {
        self.post_state_root
    }
    pub const fn action_ids_root(&self) -> CommitmentV3 {
        self.action_ids_root
    }
    pub const fn action_authorization_bindings_root(&self) -> CommitmentV3 {
        self.action_authorization_bindings_root
    }
    pub const fn authorization_grant_spends_root(&self) -> CommitmentV3 {
        self.authorization_grant_spends_root
    }
    pub const fn consumed_object_ids_root(&self) -> CommitmentV3 {
        self.consumed_object_ids_root
    }
    pub const fn state_root_host_input_sha256(&self) -> CommitmentV3 {
        self.state_root_host_input_sha256
    }
    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }
    pub fn exact_plan_b_bytes(&self) -> Result<Vec<u8>, VerifiedSpotSettlementV7ErrorV1> {
        let journal = decode_exact_spot_settlement_v7_journal_v1(&self.journal_bytes)
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
        encode_settlement_effect_plan_v2(journal.settlement_effect_plan())
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)
    }
}

pub fn verify_spot_settlement_v7_canonical_succinct_bytes(
    receipt_bytes: &[u8],
    exact_guest_input_bytes: &[u8],
    canonical_source_v6_receipt_bytes: &[u8],
) -> Result<VerifiedSpotSettlementV7ReceiptV1, VerifiedSpotSettlementV7ErrorV1> {
    let child_image = final_source_opened_spot_settlement_v6_image_id_v1()
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::FinalV6ImageIdUnmaterialized)?;
    if ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID
        .iter()
        .all(|word| *word == 0)
    {
        return Err(VerifiedSpotSettlementV7ErrorV1::V7ImageIdUnmaterialized);
    }
    if exact_guest_input_bytes.is_empty() {
        return Err(VerifiedSpotSettlementV7ErrorV1::EmptyGuestInput);
    }
    if exact_guest_input_bytes.len() > MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1 {
        return Err(VerifiedSpotSettlementV7ErrorV1::GuestInputTooLarge {
            actual: exact_guest_input_bytes.len(),
            maximum: MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1,
        });
    }
    let envelope = decode_exact_spot_settlement_v7_guest_envelope_v1(exact_guest_input_bytes)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::GuestInputDecode)?;
    let expected_child_program = program_id_from_risc0_words_v3(child_image)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::RuntimeIdentityDerivation)?;
    let verified_source_child =
        VerifiedSourceOpenedSpotSettlementReceiptV6::verify_canonical_succinct_bytes(
            canonical_source_v6_receipt_bytes,
        )
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::SourceChildReceiptVerificationFailed)?;
    if verified_source_child.verified_program_id() != expected_child_program {
        return Err(VerifiedSpotSettlementV7ErrorV1::SourceChildProgramMismatch);
    }
    if verified_source_child.receipt_profile().profile_id()
        != ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1
    {
        return Err(VerifiedSpotSettlementV7ErrorV1::SourceChildReceiptProfileMismatch);
    }
    if verified_source_child.receipt().journal.bytes.as_slice()
        != envelope.source_child_journal_bytes()
    {
        return Err(VerifiedSpotSettlementV7ErrorV1::SourceChildJournalMismatch);
    }
    let receipt = decode_canonical_receipt(receipt_bytes)?;
    let receipt_profile = verify_pinned_receipt_profile(&receipt)?;
    let context = explicit_succinct_verifier_context()?;
    receipt
        .verify_with_context(&context, ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::ReceiptVerificationFailed)?;
    let journal = decode_exact_spot_settlement_v7_journal_v1(&receipt.journal.bytes)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::VerifiedJournalDecode)?;
    let child_claim =
        derive_risc0_verified_claim_binding_v1(child_image, envelope.source_child_journal_bytes())
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::ChildClaimBinding)?;
    let composed = compose_spot_settlement_v7_after_source_receipt_verification_v1(
        envelope,
        child_image,
        child_claim,
    )
    .map_err(|_| VerifiedSpotSettlementV7ErrorV1::JournalRecomposition)?;
    if composed.journal_bytes() != receipt.journal.bytes.as_slice()
        || composed.journal() != &journal
    {
        return Err(VerifiedSpotSettlementV7ErrorV1::JournalBytesMismatch);
    }
    let verified_program_id =
        program_id_from_risc0_words_v3(ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID)
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::RuntimeIdentityDerivation)?;
    let verified_profile_id = spot_settlement_v7_profile_id_v1()?;
    let verified_program_manifest_root = spot_settlement_v7_program_manifest_root_v1(
        verified_program_id,
        verified_profile_id,
        journal.source_child_program_id(),
        journal.required_source_child_receipt_security_profile_id(),
    )?;
    let journal_sha256 = sha256_commitment(&receipt.journal.bytes)?;
    let (opening, _, _) = composed.into_parts();
    Ok(VerifiedSpotSettlementV7ReceiptV1 {
        receipt,
        receipt_profile,
        verified_source_child,
        verified_program_id,
        verified_profile_id,
        verified_program_manifest_root,
        journal,
        journal_sha256,
        exact_guest_input_bytes: exact_guest_input_bytes.to_vec(),
        opening,
    })
}

pub fn encode_spot_settlement_v7_verifier_output_v1(
    output: &SpotSettlementV7VerifierOutputV1,
) -> Result<Vec<u8>, VerifiedSpotSettlementV7ErrorV1> {
    let journal = decode_exact_spot_settlement_v7_journal_v1(&output.journal_bytes)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    require_output_matches_journal(output, &journal)?;
    encode_canonical_output_fields_v1(output)
}

fn encode_canonical_output_fields_v1(
    output: &SpotSettlementV7VerifierOutputV1,
) -> Result<Vec<u8>, VerifiedSpotSettlementV7ErrorV1> {
    let total = OUTPUT_HEADER_BYTES_V1
        .checked_add(output.journal_bytes.len())
        .ok_or(VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    if total > MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1 {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputTooLarge {
            actual: total,
            maximum: MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1,
        });
    }
    let total_u32 =
        u32::try_from(total).map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let journal_u32 = u32::try_from(output.journal_bytes.len())
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let plan_u32 = u32::try_from(output.exact_plan_b_bytes()?.len())
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_MAGIC_V1);
    bytes.extend_from_slice(&SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_VERSION_V1.to_be_bytes());
    bytes.extend_from_slice(&total_u32.to_be_bytes());
    bytes.extend_from_slice(&journal_u32.to_be_bytes());
    bytes.extend_from_slice(&plan_u32.to_be_bytes());
    bytes.extend_from_slice(&output.state_root_host_input_length.to_be_bytes());
    for field in output.fixed_fields() {
        bytes.extend_from_slice(&field);
    }
    bytes.extend_from_slice(&output.journal_bytes);
    Ok(bytes)
}

pub fn decode_exact_spot_settlement_v7_verifier_output_v1(
    bytes: &[u8],
) -> Result<SpotSettlementV7VerifierOutputV1, VerifiedSpotSettlementV7ErrorV1> {
    let (output, declared_plan_length) = decode_canonical_output_fields_v1(bytes)?;
    let journal = decode_exact_spot_settlement_v7_journal_v1(&output.journal_bytes)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)?;
    require_output_matches_journal(&output, &journal)?;
    if output.exact_plan_b_bytes()?.len() != declared_plan_length {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputDecode);
    }
    if encode_canonical_output_fields_v1(&output)?.as_slice() != bytes {
        return Err(VerifiedSpotSettlementV7ErrorV1::NonCanonicalOutput);
    }
    Ok(output)
}

fn decode_canonical_output_fields_v1(
    bytes: &[u8],
) -> Result<(SpotSettlementV7VerifierOutputV1, usize), VerifiedSpotSettlementV7ErrorV1> {
    if bytes.len() < OUTPUT_HEADER_BYTES_V1 {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputDecode);
    }
    if bytes.len() > MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1 {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1,
        });
    }
    let mut cursor = OutputCursorV1::new(bytes);
    if cursor.read_array()? != SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_MAGIC_V1 {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputDecode);
    }
    if cursor.read_u16()? != SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_VERSION_V1 {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputDecode);
    }
    let total = usize::try_from(cursor.read_u32()?)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)?;
    let journal_length = usize::try_from(cursor.read_u32()?)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)?;
    let declared_plan_length = usize::try_from(cursor.read_u32()?)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)?;
    let state_root_host_input_length = cursor.read_u32()?;
    if total != bytes.len() || state_root_host_input_length == 0 {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputDecode);
    }
    let fixed = cursor.read_fixed_fields()?;
    let journal_bytes = cursor.read(journal_length)?.to_vec();
    if !cursor.is_finished() {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputDecode);
    }
    let output = SpotSettlementV7VerifierOutputV1 {
        verified_program_id: ProgramIdV3::new(fixed[0])
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)?,
        verified_profile_id: ProfileIdV3::new(fixed[1])
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)?,
        verified_program_manifest_root: output_commitment(fixed[2])?,
        journal_sha256: output_commitment(fixed[3])?,
        source_child_program_id: ProgramIdV3::new(fixed[4])
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)?,
        required_source_child_receipt_security_profile_id: output_commitment(fixed[5])?,
        source_child_claim_binding: output_commitment(fixed[6])?,
        source_child_journal_sha256: output_commitment(fixed[7])?,
        data_availability_certificate_root: output_commitment(fixed[8])?,
        data_root: output_commitment(fixed[9])?,
        settlement_effect_plan_commitment: output_commitment(fixed[10])?,
        settlement_effect_plan_bytes_sha256: output_commitment(fixed[11])?,
        pre_state_root: output_commitment(fixed[12])?,
        post_state_root: output_commitment(fixed[13])?,
        action_ids_root: output_commitment(fixed[14])?,
        action_authorization_bindings_root: output_commitment(fixed[15])?,
        authorization_grant_spends_root: output_commitment(fixed[16])?,
        consumed_object_ids_root: output_commitment(fixed[17])?,
        state_root_host_input_sha256: output_commitment(fixed[18])?,
        state_root_host_input_length,
        journal_bytes,
    };
    Ok((output, declared_plan_length))
}

impl SpotSettlementV7VerifierOutputV1 {
    fn fixed_fields(&self) -> [[u8; 32]; OUTPUT_FIXED_FIELD_COUNT_V1] {
        [
            self.verified_program_id.into_bytes(),
            self.verified_profile_id.into_bytes(),
            self.verified_program_manifest_root.into_bytes(),
            self.journal_sha256.into_bytes(),
            self.source_child_program_id.into_bytes(),
            self.required_source_child_receipt_security_profile_id
                .into_bytes(),
            self.source_child_claim_binding.into_bytes(),
            self.source_child_journal_sha256.into_bytes(),
            self.data_availability_certificate_root.into_bytes(),
            self.data_root.into_bytes(),
            self.settlement_effect_plan_commitment.into_bytes(),
            self.settlement_effect_plan_bytes_sha256.into_bytes(),
            self.pre_state_root.into_bytes(),
            self.post_state_root.into_bytes(),
            self.action_ids_root.into_bytes(),
            self.action_authorization_bindings_root.into_bytes(),
            self.authorization_grant_spends_root.into_bytes(),
            self.consumed_object_ids_root.into_bytes(),
            self.state_root_host_input_sha256.into_bytes(),
        ]
    }
}

fn require_output_matches_journal(
    output: &SpotSettlementV7VerifierOutputV1,
    journal: &SpotSettlementV7JournalV1,
) -> Result<(), VerifiedSpotSettlementV7ErrorV1> {
    require_output_journal_associations_v1(output, journal)?;
    require_governed_output_identity_v1(output)
}

fn require_output_journal_associations_v1(
    output: &SpotSettlementV7VerifierOutputV1,
    journal: &SpotSettlementV7JournalV1,
) -> Result<(), VerifiedSpotSettlementV7ErrorV1> {
    let plan = journal.settlement_effect_plan();
    let exact_plan_b_bytes = encode_settlement_effect_plan_v2(plan)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let exact_plan_b_bytes_sha256 = sha256_commitment(&exact_plan_b_bytes)?;
    let batch = plan.economic_action_batch();
    let journal_hash = sha256_commitment(&output.journal_bytes)?;
    let matches = output.journal_sha256 == journal_hash
        && output.source_child_program_id == journal.source_child_program_id()
        && output.required_source_child_receipt_security_profile_id
            == journal.required_source_child_receipt_security_profile_id()
        && output.source_child_claim_binding == journal.source_child_claim_binding()
        && output.source_child_journal_sha256 == journal.source_child_journal_sha256()
        && output.data_availability_certificate_root
            == journal.data_availability_certificate_root()
        && output.data_root == journal.data_root()
        && output.settlement_effect_plan_commitment == journal.settlement_effect_plan_commitment()
        && output.settlement_effect_plan_bytes_sha256
            == journal.settlement_effect_plan_bytes_sha256()
        && output.settlement_effect_plan_bytes_sha256 == exact_plan_b_bytes_sha256
        && output.pre_state_root == journal.effect_binding_journal().pre_state_root()
        && output.post_state_root == journal.effect_binding_journal().post_state_root()
        && output.action_ids_root == journal.action_ids_root()
        && output.action_authorization_bindings_root == batch.action_authorization_bindings_root()
        && output.authorization_grant_spends_root == batch.authorization_grant_spends_root()
        && output.consumed_object_ids_root == batch.consumed_object_ids_root()
        && output.state_root_host_input_sha256 == journal.state_root_host_input_sha256()
        && output.state_root_host_input_length == journal.state_root_host_input_length();
    if !matches {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputEncoding);
    }
    Ok(())
}

fn require_governed_output_identity_v1(
    output: &SpotSettlementV7VerifierOutputV1,
) -> Result<(), VerifiedSpotSettlementV7ErrorV1> {
    let expected_program = program_id_from_risc0_words_v3(ZENODEX_ZRPF_RISC0_SPOT_SETTLEMENT_V7_ID)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let expected_profile = spot_settlement_v7_profile_id_v1()
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let expected_child_image = final_source_opened_spot_settlement_v6_image_id_v1()
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let expected_child_program = program_id_from_risc0_words_v3(expected_child_image)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let expected_child_receipt_profile = required_source_child_receipt_security_profile_id_v1()
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let expected_manifest = spot_settlement_v7_program_manifest_root_v1(
        expected_program,
        expected_profile,
        expected_child_program,
        expected_child_receipt_profile,
    )
    .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)?;
    let matches = output.verified_program_id == expected_program
        && output.verified_profile_id == expected_profile
        && output.verified_program_manifest_root == expected_manifest
        && output.source_child_program_id == expected_child_program
        && output.required_source_child_receipt_security_profile_id
            == expected_child_receipt_profile;
    if !matches {
        return Err(VerifiedSpotSettlementV7ErrorV1::OutputEncoding);
    }
    Ok(())
}

fn output_commitment(bytes: [u8; 32]) -> Result<CommitmentV3, VerifiedSpotSettlementV7ErrorV1> {
    CommitmentV3::new(bytes).map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)
}

struct OutputCursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> OutputCursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }
    fn read_u16(&mut self) -> Result<u16, VerifiedSpotSettlementV7ErrorV1> {
        Ok(u16::from_be_bytes(self.read_array()?))
    }
    fn read_u32(&mut self) -> Result<u32, VerifiedSpotSettlementV7ErrorV1> {
        Ok(u32::from_be_bytes(self.read_array()?))
    }
    fn read_fixed_fields(
        &mut self,
    ) -> Result<[[u8; 32]; OUTPUT_FIXED_FIELD_COUNT_V1], VerifiedSpotSettlementV7ErrorV1> {
        let mut fields = [[0_u8; 32]; OUTPUT_FIXED_FIELD_COUNT_V1];
        for field in &mut fields {
            *field = self.read_array()?;
        }
        Ok(fields)
    }
    fn read_array<const N: usize>(&mut self) -> Result<[u8; N], VerifiedSpotSettlementV7ErrorV1> {
        self.read(N)?
            .try_into()
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputDecode)
    }
    fn read(&mut self, length: usize) -> Result<&'a [u8], VerifiedSpotSettlementV7ErrorV1> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(VerifiedSpotSettlementV7ErrorV1::OutputDecode)?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(VerifiedSpotSettlementV7ErrorV1::OutputDecode)?;
        self.offset = end;
        Ok(value)
    }
    const fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}

fn decode_canonical_receipt(bytes: &[u8]) -> Result<Receipt, VerifiedSpotSettlementV7ErrorV1> {
    if bytes.is_empty() {
        return Err(VerifiedSpotSettlementV7ErrorV1::EmptyReceiptBytes);
    }
    if bytes.len() > MAX_CANONICAL_SPOT_SETTLEMENT_V7_RECEIPT_BYTES_V1 {
        return Err(VerifiedSpotSettlementV7ErrorV1::ReceiptBytesTooLarge {
            actual: bytes.len(),
            maximum: MAX_CANONICAL_SPOT_SETTLEMENT_V7_RECEIPT_BYTES_V1,
        });
    }
    let receipt: Receipt = serde_json::from_slice(bytes)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::ReceiptJsonDecode)?;
    let canonical = serde_json::to_vec(&receipt)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::ReceiptJsonEncode)?;
    if canonical.as_slice() != bytes {
        return Err(VerifiedSpotSettlementV7ErrorV1::NonCanonicalReceiptJson);
    }
    Ok(receipt)
}

fn verify_pinned_receipt_profile(
    receipt: &Receipt,
) -> Result<VerifiedReceiptProfileV1, VerifiedSpotSettlementV7ErrorV1> {
    let InnerReceipt::Succinct(inner) = &receipt.inner else {
        return Err(VerifiedSpotSettlementV7ErrorV1::NonSuccinctReceipt);
    };
    if receipt.metadata.verifier_parameters != inner.verifier_parameters {
        return Err(VerifiedSpotSettlementV7ErrorV1::ReceiptMetadataMismatch);
    }
    let actual = VerifiedReceiptProfileV1 {
        profile_id: ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
        receipt_kind: RECEIPT_KIND_SUCCINCT_V1,
        verifier_parameters: inner.verifier_parameters.to_string(),
        hashfn: inner.hashfn.clone(),
        control_id: inner.control_id.to_string(),
    };
    for (matches, field) in [
        (
            actual.verifier_parameters == RECEIPT_VERIFIER_PARAMETERS_V1,
            "verifier parameters",
        ),
        (
            actual.hashfn == RECEIPT_HASHFN_POSEIDON2_V1,
            "hash function",
        ),
        (actual.control_id == RECEIPT_CONTROL_ID_V1, "control ID"),
    ] {
        if !matches {
            return Err(VerifiedSpotSettlementV7ErrorV1::ReceiptProfileMismatch(
                field,
            ));
        }
    }
    if SuccinctReceiptVerifierParameters::default()
        .digest()
        .to_string()
        != RECEIPT_VERIFIER_PARAMETERS_V1
    {
        return Err(VerifiedSpotSettlementV7ErrorV1::ReceiptProfileMismatch(
            "compiled verifier parameters",
        ));
    }
    Ok(actual)
}

fn explicit_succinct_verifier_context() -> Result<VerifierContext, VerifiedSpotSettlementV7ErrorV1>
{
    let mut suites = VerifierContext::default_hash_suites();
    let poseidon2 = suites.remove(RECEIPT_HASHFN_POSEIDON2_V1).ok_or(
        VerifiedSpotSettlementV7ErrorV1::ReceiptProfileMismatch("compiled hash suite"),
    )?;
    Ok(VerifierContext::empty()
        .with_suites(BTreeMap::from([(
            RECEIPT_HASHFN_POSEIDON2_V1.to_owned(),
            poseidon2,
        )]))
        .with_succinct_verifier_parameters(SuccinctReceiptVerifierParameters::default()))
}

fn spot_settlement_v7_profile_id_v1() -> Result<ProfileIdV3, VerifiedSpotSettlementV7ErrorV1> {
    ProfileIdV3::new(domain_hash(V7_PROFILE_DOMAIN_V1, &[])?)
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::RuntimeIdentityDerivation)
}

fn spot_settlement_v7_program_manifest_root_v1(
    program_id: ProgramIdV3,
    profile_id: ProfileIdV3,
    child_program_id: ProgramIdV3,
    child_receipt_security_profile_id: CommitmentV3,
) -> Result<CommitmentV3, VerifiedSpotSettlementV7ErrorV1> {
    let envelope_version = SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_VERSION_V1.to_be_bytes();
    let journal_version = SPOT_SETTLEMENT_V7_JOURNAL_VERSION_V1.to_be_bytes();
    let output_version = SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_VERSION_V1.to_be_bytes();
    let hash = domain_hash(
        V7_MANIFEST_DOMAIN_V1,
        &[
            program_id.as_bytes(),
            profile_id.as_bytes(),
            child_program_id.as_bytes(),
            child_receipt_security_profile_id.as_bytes(),
            ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1.as_bytes(),
            SPOT_SETTLEMENT_V7_VERIFIER_SCHEMA_V1.as_bytes(),
            &envelope_version,
            &SPOT_SETTLEMENT_V7_JOURNAL_MAGIC_V1,
            &journal_version,
            &SPOT_SETTLEMENT_V7_VERIFIER_OUTPUT_MAGIC_V1,
            &output_version,
        ],
    )?;
    CommitmentV3::new(hash).map_err(|_| VerifiedSpotSettlementV7ErrorV1::RuntimeIdentityDerivation)
}

fn domain_hash(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<[u8; 32], VerifiedSpotSettlementV7ErrorV1> {
    let mut hasher = Sha256::new();
    let domain_len = u16::try_from(domain.len())
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::RuntimeIdentityDerivation)?;
    hasher.update(domain_len.to_be_bytes());
    hasher.update(domain);
    let field_count = u16::try_from(fields.len())
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::RuntimeIdentityDerivation)?;
    hasher.update(field_count.to_be_bytes());
    for field in fields {
        let length = u32::try_from(field.len())
            .map_err(|_| VerifiedSpotSettlementV7ErrorV1::RuntimeIdentityDerivation)?;
        hasher.update(length.to_be_bytes());
        hasher.update(field);
    }
    Ok(hasher.finalize().into())
}

fn sha256_commitment(bytes: &[u8]) -> Result<CommitmentV3, VerifiedSpotSettlementV7ErrorV1> {
    CommitmentV3::new(Sha256::digest(bytes).into())
        .map_err(|_| VerifiedSpotSettlementV7ErrorV1::OutputEncoding)
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet;

    use super::*;

    const VERIFIER_SOURCE: &str = include_str!("lib.rs");
    const JOURNAL_GOLDEN_V1: &str =
        include_str!("../../shared/tests/vectors/spot_settlement_v7_journal_v1.hex");
    const FIRECRACKER_OUTPUT_GOLDEN_V1: &str =
        include_str!("../tests/vectors/spot_settlement_v7_firecracker_output_v1.hex");

    #[test]
    fn placeholder_identity_fails_before_receipt_parsing() {
        let result = verify_spot_settlement_v7_canonical_succinct_bytes(
            b"not JSON",
            b"not input",
            b"not child",
        );
        assert!(matches!(
            result,
            Err(VerifiedSpotSettlementV7ErrorV1::FinalV6ImageIdUnmaterialized)
        ));
    }

    #[test]
    fn source_child_receipt_authentication_precedes_v7_capability_construction() {
        let child_verify = VERIFIER_SOURCE
            .find("VerifiedSourceOpenedSpotSettlementReceiptV6::verify_canonical_succinct_bytes")
            .unwrap();
        let capability = VERIFIER_SOURCE
            .find("Ok(VerifiedSpotSettlementV7ReceiptV1 {")
            .unwrap();
        assert!(child_verify < capability);
        assert!(VERIFIER_SOURCE.contains("verified_source_child,"));
    }

    #[test]
    fn reject_codes_are_stable_and_unique() {
        let errors = [
            VerifiedSpotSettlementV7ErrorV1::FinalV6ImageIdUnmaterialized,
            VerifiedSpotSettlementV7ErrorV1::V7ImageIdUnmaterialized,
            VerifiedSpotSettlementV7ErrorV1::EmptyGuestInput,
            VerifiedSpotSettlementV7ErrorV1::GuestInputTooLarge {
                actual: 2,
                maximum: 1,
            },
            VerifiedSpotSettlementV7ErrorV1::GuestInputDecode,
            VerifiedSpotSettlementV7ErrorV1::EmptyReceiptBytes,
            VerifiedSpotSettlementV7ErrorV1::ReceiptBytesTooLarge {
                actual: 2,
                maximum: 1,
            },
            VerifiedSpotSettlementV7ErrorV1::ReceiptJsonDecode,
            VerifiedSpotSettlementV7ErrorV1::ReceiptJsonEncode,
            VerifiedSpotSettlementV7ErrorV1::NonCanonicalReceiptJson,
            VerifiedSpotSettlementV7ErrorV1::NonSuccinctReceipt,
            VerifiedSpotSettlementV7ErrorV1::ReceiptMetadataMismatch,
            VerifiedSpotSettlementV7ErrorV1::ReceiptProfileMismatch("test"),
            VerifiedSpotSettlementV7ErrorV1::ReceiptVerificationFailed,
            VerifiedSpotSettlementV7ErrorV1::SourceChildReceiptVerificationFailed,
            VerifiedSpotSettlementV7ErrorV1::SourceChildProgramMismatch,
            VerifiedSpotSettlementV7ErrorV1::SourceChildReceiptProfileMismatch,
            VerifiedSpotSettlementV7ErrorV1::SourceChildJournalMismatch,
            VerifiedSpotSettlementV7ErrorV1::VerifiedJournalDecode,
            VerifiedSpotSettlementV7ErrorV1::ChildClaimBinding,
            VerifiedSpotSettlementV7ErrorV1::JournalRecomposition,
            VerifiedSpotSettlementV7ErrorV1::JournalBytesMismatch,
            VerifiedSpotSettlementV7ErrorV1::RuntimeIdentityDerivation,
            VerifiedSpotSettlementV7ErrorV1::OutputEncoding,
            VerifiedSpotSettlementV7ErrorV1::OutputDecode,
            VerifiedSpotSettlementV7ErrorV1::NonCanonicalOutput,
            VerifiedSpotSettlementV7ErrorV1::OutputTooLarge {
                actual: 2,
                maximum: 1,
            },
        ];
        let codes = errors
            .iter()
            .map(|error| error.code())
            .collect::<BTreeSet<_>>();
        assert_eq!(codes.len(), errors.len());
    }

    #[test]
    fn proof_independent_firecracker_output_vector_is_canonical() {
        let journal_bytes = decode_golden_hex(JOURNAL_GOLDEN_V1);
        let journal = decode_exact_spot_settlement_v7_journal_v1(&journal_bytes).unwrap();
        let plan = journal.settlement_effect_plan();
        let batch = plan.economic_action_batch();
        let output = SpotSettlementV7VerifierOutputV1 {
            verified_program_id: ProgramIdV3::new([0xb1; 32]).unwrap(),
            verified_profile_id: ProfileIdV3::new([0xb2; 32]).unwrap(),
            verified_program_manifest_root: CommitmentV3::new([0xb3; 32]).unwrap(),
            journal_sha256: sha256_commitment(&journal_bytes).unwrap(),
            source_child_program_id: journal.source_child_program_id(),
            required_source_child_receipt_security_profile_id: journal
                .required_source_child_receipt_security_profile_id(),
            source_child_claim_binding: journal.source_child_claim_binding(),
            source_child_journal_sha256: journal.source_child_journal_sha256(),
            data_availability_certificate_root: journal.data_availability_certificate_root(),
            data_root: journal.data_root(),
            settlement_effect_plan_commitment: journal.settlement_effect_plan_commitment(),
            settlement_effect_plan_bytes_sha256: journal.settlement_effect_plan_bytes_sha256(),
            pre_state_root: journal.effect_binding_journal().pre_state_root(),
            post_state_root: journal.effect_binding_journal().post_state_root(),
            action_ids_root: journal.action_ids_root(),
            action_authorization_bindings_root: batch.action_authorization_bindings_root(),
            authorization_grant_spends_root: batch.authorization_grant_spends_root(),
            consumed_object_ids_root: batch.consumed_object_ids_root(),
            state_root_host_input_sha256: journal.state_root_host_input_sha256(),
            state_root_host_input_length: journal.state_root_host_input_length(),
            journal_bytes,
        };
        require_output_journal_associations_v1(&output, &journal).unwrap();
        let bytes = encode_canonical_output_fields_v1(&output).unwrap();
        assert_eq!(bytes, decode_golden_hex(FIRECRACKER_OUTPUT_GOLDEN_V1));
        assert_eq!(
            Sha256::digest(&bytes).as_slice(),
            &[
                0x97, 0x9b, 0x2e, 0x9c, 0xb4, 0x75, 0x7d, 0xe5, 0x0e, 0xc9, 0x35, 0xc5, 0x5c, 0xa8,
                0x27, 0xc6, 0x93, 0xad, 0x5c, 0xb4, 0xe2, 0x2e, 0xe8, 0x03, 0x4b, 0xee, 0x9e, 0x78,
                0x66, 0xde, 0x14, 0x8c,
            ]
        );
        let (decoded, declared_plan_length) = decode_canonical_output_fields_v1(&bytes).unwrap();
        assert_eq!(decoded, output);
        assert_eq!(
            declared_plan_length,
            output.exact_plan_b_bytes().unwrap().len()
        );
        assert!(matches!(
            decode_exact_spot_settlement_v7_verifier_output_v1(&bytes),
            Err(VerifiedSpotSettlementV7ErrorV1::OutputEncoding)
        ));
    }

    fn decode_golden_hex(value: &str) -> Vec<u8> {
        let compact = value
            .lines()
            .filter(|line| !line.starts_with("//"))
            .collect::<String>();
        compact
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| u8::from_str_radix(core::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    }
}
