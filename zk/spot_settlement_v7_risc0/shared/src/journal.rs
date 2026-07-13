use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_effect_plan_v2, encode_settlement_effect_plan_v2, CommitmentV3,
    ProgramIdV3, SettlementEffectPlanV2,
};
use zenodex_zrpf_risc0_spot_settlement_v7_effect_binding_shared::{
    decode_exact_spot_settlement_v7_effect_binding_journal_v1,
    encode_spot_settlement_v7_effect_binding_journal_v1, SpotSettlementV7EffectBindingJournalV1,
    SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1,
};
use zenodex_zrpf_risc0_spot_state_root_v7_semantic_shared::{
    decode_exact_spot_state_root_v7_semantic_journal_v1,
    encode_spot_state_root_v7_semantic_journal_v1, SpotStateRootV7SemanticJournalV1,
    SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1,
};
use zenodex_zrpf_risc0_value_node_shared::risc0_succinct_receipt_security_profile_id_v4;

use crate::{SourceOpenedSpotSettlementV7OpeningV1, SpotSettlementV7ErrorV1};

pub const SPOT_SETTLEMENT_V7_JOURNAL_MAGIC_V1: [u8; 8] = *b"ZSPTV7J1";
pub const SPOT_SETTLEMENT_V7_JOURNAL_VERSION_V1: u16 = 1;

/// Firecracker's governed replay payload cap is 64 KiB. Reserve room for the
/// fixed journal surface and verifier-output framing by capping the exact V7
/// plan at 48 KiB.
pub const MAX_SPOT_SETTLEMENT_V7_PLAN_B_BYTES_V1: usize = 48 * 1_024;
pub const MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1: usize = 64 * 1_024;

const FIXED_COMMITMENT_COUNT_V1: usize = 12;
const JOURNAL_HEADER_BYTES_V1: usize = 8 + 2 + 4 + 4 + 2 + 2 + 4;
const JOURNAL_FIXED_BYTES_V1: usize = JOURNAL_HEADER_BYTES_V1
    + FIXED_COMMITMENT_COUNT_V1 * 32
    + SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1
    + SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1;

pub const MAX_SPOT_SETTLEMENT_V7_JOURNAL_BYTES_V1: usize =
    JOURNAL_FIXED_BYTES_V1 + MAX_SPOT_SETTLEMENT_V7_PLAN_B_BYTES_V1;

const _: [(); 1] = [(); (MAX_SPOT_SETTLEMENT_V7_JOURNAL_BYTES_V1
    < MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1) as usize];

/// Exact journal committed by the V7 guest.
///
/// The journal contains the complete derived Plan B and only a byte length and
/// SHA-256 commitment for the larger host state-opening input. Receipt
/// verification and exact host recomposition remain mandatory before the
/// state openings acquire any authority.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v7_shared::SpotSettlementV7JournalV1;
/// let journal: SpotSettlementV7JournalV1 = unimplemented!();
/// let _ = journal.settlement_authority();
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpotSettlementV7JournalV1 {
    source_child_program_id: ProgramIdV3,
    required_source_child_receipt_security_profile_id: CommitmentV3,
    source_child_claim_binding: CommitmentV3,
    source_child_journal_sha256: CommitmentV3,
    data_availability_certificate_root: CommitmentV3,
    data_root: CommitmentV3,
    source_replay_sha256: CommitmentV3,
    state_root_host_input_sha256: CommitmentV3,
    semantic_journal_sha256: CommitmentV3,
    effect_binding_journal_commitment: CommitmentV3,
    settlement_effect_plan_commitment: CommitmentV3,
    action_ids_root: CommitmentV3,
    state_root_host_input_length: u32,
    semantic_journal: SpotStateRootV7SemanticJournalV1,
    effect_binding_journal: SpotSettlementV7EffectBindingJournalV1,
    settlement_effect_plan: SettlementEffectPlanV2,
}

impl SpotSettlementV7JournalV1 {
    pub(crate) fn from_opening(
        opening: &SourceOpenedSpotSettlementV7OpeningV1,
    ) -> Result<Self, SpotSettlementV7ErrorV1> {
        let semantic_bytes = encode_spot_state_root_v7_semantic_journal_v1(opening.state_journal());
        let effect_binding_journal = opening.bound_state().journal();
        let effect_binding_journal_commitment = effect_binding_journal
            .canonical_commitment()
            .map_err(|_| SpotSettlementV7ErrorV1::DerivedCommitment("effect binding journal"))?;
        let settlement_effect_plan = opening.plan_b();
        let plan_bytes = encode_settlement_effect_plan_v2(settlement_effect_plan)
            .map_err(|_| SpotSettlementV7ErrorV1::SettlementPlanEncoding)?;
        require_plan_length(plan_bytes.len())?;
        let batch = settlement_effect_plan.economic_action_batch();
        let journal = Self {
            source_child_program_id: opening.source_child_program_id(),
            required_source_child_receipt_security_profile_id:
                required_source_child_receipt_security_profile_id_v1()?,
            source_child_claim_binding: opening.source_child_claim_binding(),
            source_child_journal_sha256: opening.source_child_journal_sha256(),
            data_availability_certificate_root: opening
                .data_availability_certificate()
                .certificate_root(),
            data_root: opening.data_availability_certificate().data_root(),
            source_replay_sha256: opening.source_replay_sha256(),
            state_root_host_input_sha256: opening.state_root_host_input_sha256(),
            semantic_journal_sha256: sha256_commitment(&semantic_bytes, "semantic journal")?,
            effect_binding_journal_commitment,
            settlement_effect_plan_commitment: settlement_effect_plan
                .canonical_commitment()
                .map_err(|_| SpotSettlementV7ErrorV1::DerivedCommitment("settlement plan"))?,
            action_ids_root: batch.action_ids_root(),
            state_root_host_input_length: opening.state_root_host_input_length(),
            semantic_journal: opening.state_journal().clone(),
            effect_binding_journal: effect_binding_journal.clone(),
            settlement_effect_plan: settlement_effect_plan.clone(),
        };
        journal.validate_associations()?;
        Ok(journal)
    }

    fn validate_associations(&self) -> Result<(), SpotSettlementV7ErrorV1> {
        if self.required_source_child_receipt_security_profile_id
            != required_source_child_receipt_security_profile_id_v1()?
        {
            return Err(SpotSettlementV7ErrorV1::JournalAssociation(
                "source child receipt security profile",
            ));
        }
        let semantic_bytes = encode_spot_state_root_v7_semantic_journal_v1(&self.semantic_journal);
        if sha256_commitment(&semantic_bytes, "semantic journal")? != self.semantic_journal_sha256 {
            return Err(SpotSettlementV7ErrorV1::JournalComponentHashMismatch(
                "semantic journal",
            ));
        }
        if self
            .effect_binding_journal
            .canonical_commitment()
            .map_err(|_| SpotSettlementV7ErrorV1::DerivedCommitment("effect binding journal"))?
            != self.effect_binding_journal_commitment
        {
            return Err(SpotSettlementV7ErrorV1::JournalComponentHashMismatch(
                "effect binding journal",
            ));
        }
        self.settlement_effect_plan
            .validate_self_consistency()
            .map_err(|_| SpotSettlementV7ErrorV1::SettlementPlanDecode)?;
        if self
            .settlement_effect_plan
            .canonical_commitment()
            .map_err(|_| SpotSettlementV7ErrorV1::DerivedCommitment("settlement plan"))?
            != self.settlement_effect_plan_commitment
            || self
                .effect_binding_journal
                .settlement_effect_plan_commitment()
                != self.settlement_effect_plan_commitment
        {
            return Err(SpotSettlementV7ErrorV1::JournalAssociation(
                "settlement plan commitment",
            ));
        }
        let batch = self.settlement_effect_plan.economic_action_batch();
        let [action] = batch.actions() else {
            return Err(SpotSettlementV7ErrorV1::JournalAssociation(
                "singleton economic action",
            ));
        };
        if batch.action_ids_root() != self.action_ids_root
            || action
                .action_id()
                .map_err(|_| SpotSettlementV7ErrorV1::JournalAssociation("economic action"))?
                != self.effect_binding_journal.economic_action_id()
        {
            return Err(SpotSettlementV7ErrorV1::JournalAssociation(
                "economic action identity",
            ));
        }
        if batch.pre_state_root() != self.effect_binding_journal.pre_state_root()
            || self.settlement_effect_plan.post_state_root()
                != self.effect_binding_journal.post_state_root()
            || self.settlement_effect_plan.public_policy_hash()
                != self.effect_binding_journal.public_policy_hash()
        {
            return Err(SpotSettlementV7ErrorV1::JournalAssociation(
                "state or policy",
            ));
        }
        if self.semantic_journal.compatibility_profile_id()
            != self
                .effect_binding_journal
                .compatibility_profile_id()
                .into_bytes()
            || self.semantic_journal.state_root_scheme_id()
                != self
                    .effect_binding_journal
                    .state_root_scheme_id()
                    .into_bytes()
            || self.semantic_journal.pre_state_root_v5()
                != self.effect_binding_journal.pre_state_root().into_bytes()
            || self.semantic_journal.post_state_root_v5()
                != self.effect_binding_journal.post_state_root().into_bytes()
        {
            return Err(SpotSettlementV7ErrorV1::JournalAssociation(
                "semantic state journal",
            ));
        }
        Ok(())
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
    pub const fn source_replay_sha256(&self) -> CommitmentV3 {
        self.source_replay_sha256
    }
    pub const fn state_root_host_input_sha256(&self) -> CommitmentV3 {
        self.state_root_host_input_sha256
    }
    pub const fn state_root_host_input_length(&self) -> u32 {
        self.state_root_host_input_length
    }
    pub const fn semantic_journal_sha256(&self) -> CommitmentV3 {
        self.semantic_journal_sha256
    }
    pub const fn effect_binding_journal_commitment(&self) -> CommitmentV3 {
        self.effect_binding_journal_commitment
    }
    pub const fn settlement_effect_plan_commitment(&self) -> CommitmentV3 {
        self.settlement_effect_plan_commitment
    }
    pub const fn action_ids_root(&self) -> CommitmentV3 {
        self.action_ids_root
    }
    pub const fn semantic_journal(&self) -> &SpotStateRootV7SemanticJournalV1 {
        &self.semantic_journal
    }
    pub const fn effect_binding_journal(&self) -> &SpotSettlementV7EffectBindingJournalV1 {
        &self.effect_binding_journal
    }
    pub const fn settlement_effect_plan(&self) -> &SettlementEffectPlanV2 {
        &self.settlement_effect_plan
    }
}

pub fn encode_spot_settlement_v7_journal_v1(
    journal: &SpotSettlementV7JournalV1,
) -> Result<Vec<u8>, SpotSettlementV7ErrorV1> {
    journal.validate_associations()?;
    let semantic = encode_spot_state_root_v7_semantic_journal_v1(&journal.semantic_journal);
    let binding =
        encode_spot_settlement_v7_effect_binding_journal_v1(&journal.effect_binding_journal);
    let plan = encode_settlement_effect_plan_v2(&journal.settlement_effect_plan)
        .map_err(|_| SpotSettlementV7ErrorV1::SettlementPlanEncoding)?;
    require_plan_length(plan.len())?;
    let total = JOURNAL_FIXED_BYTES_V1
        .checked_add(plan.len())
        .ok_or(SpotSettlementV7ErrorV1::LengthOverflow("journal total"))?;
    let total_u32 = u32::try_from(total)
        .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow("journal total"))?;
    let semantic_u16 = u16::try_from(semantic.len())
        .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow("semantic journal"))?;
    let binding_u16 = u16::try_from(binding.len())
        .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow("binding journal"))?;
    let plan_u32 = u32::try_from(plan.len())
        .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow("settlement plan"))?;
    let mut output = Vec::with_capacity(total);
    output.extend_from_slice(&SPOT_SETTLEMENT_V7_JOURNAL_MAGIC_V1);
    output.extend_from_slice(&SPOT_SETTLEMENT_V7_JOURNAL_VERSION_V1.to_be_bytes());
    output.extend_from_slice(&total_u32.to_be_bytes());
    output.extend_from_slice(&journal.state_root_host_input_length.to_be_bytes());
    output.extend_from_slice(&semantic_u16.to_be_bytes());
    output.extend_from_slice(&binding_u16.to_be_bytes());
    output.extend_from_slice(&plan_u32.to_be_bytes());
    for value in [
        journal.source_child_program_id.into_bytes(),
        journal
            .required_source_child_receipt_security_profile_id
            .into_bytes(),
        journal.source_child_claim_binding.into_bytes(),
        journal.source_child_journal_sha256.into_bytes(),
        journal.data_availability_certificate_root.into_bytes(),
        journal.data_root.into_bytes(),
        journal.source_replay_sha256.into_bytes(),
        journal.state_root_host_input_sha256.into_bytes(),
        journal.semantic_journal_sha256.into_bytes(),
        journal.effect_binding_journal_commitment.into_bytes(),
        journal.settlement_effect_plan_commitment.into_bytes(),
        journal.action_ids_root.into_bytes(),
    ] {
        output.extend_from_slice(&value);
    }
    output.extend_from_slice(&semantic);
    output.extend_from_slice(&binding);
    output.extend_from_slice(&plan);
    Ok(output)
}

pub fn decode_exact_spot_settlement_v7_journal_v1(
    bytes: &[u8],
) -> Result<SpotSettlementV7JournalV1, SpotSettlementV7ErrorV1> {
    if bytes.len() < JOURNAL_FIXED_BYTES_V1 {
        return Err(SpotSettlementV7ErrorV1::TruncatedInput("V7 journal"));
    }
    if bytes.len() > MAX_SPOT_SETTLEMENT_V7_JOURNAL_BYTES_V1 {
        return Err(SpotSettlementV7ErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SPOT_SETTLEMENT_V7_JOURNAL_BYTES_V1,
        });
    }
    let mut cursor = JournalCursorV1::new(bytes);
    if cursor.read_array("journal magic")? != SPOT_SETTLEMENT_V7_JOURNAL_MAGIC_V1 {
        return Err(SpotSettlementV7ErrorV1::InvalidJournalMagic);
    }
    let version = cursor.read_u16("journal version")?;
    if version != SPOT_SETTLEMENT_V7_JOURNAL_VERSION_V1 {
        return Err(SpotSettlementV7ErrorV1::InvalidJournalVersion(version));
    }
    let declared_total = usize::try_from(cursor.read_u32("journal total")?)
        .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow("journal total"))?;
    if declared_total != bytes.len() {
        return Err(SpotSettlementV7ErrorV1::JournalLengthMismatch);
    }
    let state_root_host_input_length = cursor.read_u32("host input length")?;
    if state_root_host_input_length == 0 {
        return Err(SpotSettlementV7ErrorV1::JournalLengthMismatch);
    }
    let semantic_length = usize::from(cursor.read_u16("semantic length")?);
    let binding_length = usize::from(cursor.read_u16("binding length")?);
    let plan_length = usize::try_from(cursor.read_u32("plan length")?)
        .map_err(|_| SpotSettlementV7ErrorV1::LengthOverflow("settlement plan"))?;
    if semantic_length != SPOT_STATE_ROOT_V7_SEMANTIC_JOURNAL_BYTES_V1
        || binding_length != SPOT_SETTLEMENT_V7_EFFECT_BINDING_JOURNAL_BYTES_V1
    {
        return Err(SpotSettlementV7ErrorV1::JournalLengthMismatch);
    }
    require_plan_length(plan_length)?;
    let source_child_program_id = ProgramIdV3::new(cursor.read_array("child program")?)
        .map_err(|_| SpotSettlementV7ErrorV1::DerivedCommitment("child program"))?;
    let required_source_child_receipt_security_profile_id =
        read_commitment(&mut cursor, "child receipt profile")?;
    let source_child_claim_binding = read_commitment(&mut cursor, "child claim")?;
    let source_child_journal_sha256 = read_commitment(&mut cursor, "child journal hash")?;
    let data_availability_certificate_root = read_commitment(&mut cursor, "DA certificate")?;
    let data_root = read_commitment(&mut cursor, "DA data")?;
    let source_replay_sha256 = read_commitment(&mut cursor, "source replay")?;
    let state_root_host_input_sha256 = read_commitment(&mut cursor, "host input")?;
    let semantic_journal_sha256 = read_commitment(&mut cursor, "semantic journal")?;
    let effect_binding_journal_commitment = read_commitment(&mut cursor, "binding journal")?;
    let settlement_effect_plan_commitment = read_commitment(&mut cursor, "settlement plan")?;
    let action_ids_root = read_commitment(&mut cursor, "action ids")?;
    let semantic_bytes = cursor.read(semantic_length, "semantic journal")?;
    let binding_bytes = cursor.read(binding_length, "binding journal")?;
    let plan_bytes = cursor.read(plan_length, "settlement plan")?;
    if !cursor.is_finished() {
        return Err(SpotSettlementV7ErrorV1::TrailingBytes);
    }
    let journal = SpotSettlementV7JournalV1 {
        source_child_program_id,
        required_source_child_receipt_security_profile_id,
        source_child_claim_binding,
        source_child_journal_sha256,
        data_availability_certificate_root,
        data_root,
        source_replay_sha256,
        state_root_host_input_sha256,
        semantic_journal_sha256,
        effect_binding_journal_commitment,
        settlement_effect_plan_commitment,
        action_ids_root,
        state_root_host_input_length,
        semantic_journal: decode_exact_spot_state_root_v7_semantic_journal_v1(semantic_bytes)
            .map_err(|_| SpotSettlementV7ErrorV1::StateJournalEncoding)?,
        effect_binding_journal: decode_exact_spot_settlement_v7_effect_binding_journal_v1(
            binding_bytes,
        )
        .map_err(|_| SpotSettlementV7ErrorV1::JournalAssociation("binding journal"))?,
        settlement_effect_plan: decode_exact_settlement_effect_plan_v2(plan_bytes)
            .map_err(|_| SpotSettlementV7ErrorV1::SettlementPlanDecode)?,
    };
    journal.validate_associations()?;
    if encode_spot_settlement_v7_journal_v1(&journal)?.as_slice() != bytes {
        return Err(SpotSettlementV7ErrorV1::NonCanonicalJournal);
    }
    Ok(journal)
}

fn require_plan_length(length: usize) -> Result<(), SpotSettlementV7ErrorV1> {
    if length == 0 || length > MAX_SPOT_SETTLEMENT_V7_PLAN_B_BYTES_V1 {
        return Err(SpotSettlementV7ErrorV1::ComponentTooLarge {
            component: "settlement Plan B",
            actual: length,
            maximum: MAX_SPOT_SETTLEMENT_V7_PLAN_B_BYTES_V1,
        });
    }
    Ok(())
}

/// Exact RISC0 Succinct/Poseidon2/resolve profile required for the V6 child.
///
/// The profile identity is derived from the established ZRPF receipt-profile
/// constants. The guest commits this governed requirement without accepting a
/// host-proposed profile field. The evidence harness verifies the actual child
/// receipt before registering the assumption, and the sealed V7 host verifier
/// independently authenticates and retains that canonical child artifact.
pub fn required_source_child_receipt_security_profile_id_v1(
) -> Result<CommitmentV3, SpotSettlementV7ErrorV1> {
    risc0_succinct_receipt_security_profile_id_v4().map_err(|_| {
        SpotSettlementV7ErrorV1::DerivedCommitment("source child receipt security profile")
    })
}

fn sha256_commitment(
    bytes: &[u8],
    field: &'static str,
) -> Result<CommitmentV3, SpotSettlementV7ErrorV1> {
    CommitmentV3::new(Sha256::digest(bytes).into())
        .map_err(|_| SpotSettlementV7ErrorV1::DerivedCommitment(field))
}

fn read_commitment(
    cursor: &mut JournalCursorV1<'_>,
    field: &'static str,
) -> Result<CommitmentV3, SpotSettlementV7ErrorV1> {
    CommitmentV3::new(cursor.read_array(field)?)
        .map_err(|_| SpotSettlementV7ErrorV1::DerivedCommitment(field))
}

struct JournalCursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> JournalCursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }
    fn read_u16(&mut self, field: &'static str) -> Result<u16, SpotSettlementV7ErrorV1> {
        Ok(u16::from_be_bytes(self.read_array(field)?))
    }
    fn read_u32(&mut self, field: &'static str) -> Result<u32, SpotSettlementV7ErrorV1> {
        Ok(u32::from_be_bytes(self.read_array(field)?))
    }
    fn read_array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<[u8; N], SpotSettlementV7ErrorV1> {
        self.read(N, field)?
            .try_into()
            .map_err(|_| SpotSettlementV7ErrorV1::TruncatedInput(field))
    }
    fn read(
        &mut self,
        length: usize,
        field: &'static str,
    ) -> Result<&'a [u8], SpotSettlementV7ErrorV1> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(SpotSettlementV7ErrorV1::LengthOverflow(field))?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(SpotSettlementV7ErrorV1::TruncatedInput(field))?;
        self.offset = end;
        Ok(value)
    }
    const fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use alloc::vec;

    use serde_json::Value;
    use tau_state_proof_risc0_shared::DexSnapshotV1;
    use zenodex_zrpf_protocol_v3::{
        ApplicationIdV3, AssetEffectInputV2, AssetEffectKindV2, AssetEffectV2,
        AuthorizationGrantIdV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1,
        AuthorizedEconomicActionV1, EconomicActionBatchV1, EconomicActionRecordInputV1,
        EconomicActionRecordV1, EconomicActionTypeIdV1, LedgerCellWriteInputV2, LedgerCellWriteV2,
        SettlementEffectPlanInputV2, ValueHashV2,
    };
    use zenodex_zrpf_risc0_spot_settlement_v7_effect_binding_shared::{
        bind_spot_settlement_effect_plan_v1, derive_spot_settlement_state_effect_opening_v1,
    };

    use super::*;

    const V5_FIXTURE: &str =
        include_str!("../../../../tests/fixtures/zrpf_spot_state_root_v5_bridge_v1.json");
    const V7_FIXTURE: &str =
        include_str!("../../../../tests/fixtures/zrpf_spot_state_root_v7_semantic_v1.json");
    const JOURNAL_GOLDEN_V1: &str =
        include_str!("../tests/vectors/spot_settlement_v7_journal_v1.hex");

    #[test]
    fn exact_journal_round_trip_binds_plan_and_state() {
        let journal = fixture_journal();
        let bytes = encode_spot_settlement_v7_journal_v1(&journal).unwrap();
        assert_eq!(bytes, decode_golden_hex(JOURNAL_GOLDEN_V1));
        assert_eq!(
            Sha256::digest(&bytes).as_slice(),
            &[
                0xc5, 0xee, 0x64, 0xc6, 0x2a, 0x27, 0xf0, 0x9f, 0x39, 0x66, 0xab, 0x62, 0xc3, 0xde,
                0x46, 0x9e, 0x4c, 0x70, 0xbd, 0xa8, 0xf2, 0x03, 0x69, 0xcc, 0x4e, 0xde, 0xac, 0x6a,
                0xe9, 0x1c, 0x7e, 0x74,
            ]
        );
        assert_eq!(
            decode_exact_spot_settlement_v7_journal_v1(&bytes).unwrap(),
            journal
        );
        assert!(bytes.len() < MAX_SPOT_SETTLEMENT_V7_FIRECRACKER_PAYLOAD_BYTES_V1);
    }

    #[test]
    fn exact_journal_rejects_truncation_trailing_and_component_mutation() {
        let bytes = encode_spot_settlement_v7_journal_v1(&fixture_journal()).unwrap();
        for end in 0..bytes.len() {
            assert!(decode_exact_spot_settlement_v7_journal_v1(&bytes[..end]).is_err());
        }
        let mut trailing = bytes.clone();
        trailing.push(0);
        assert!(decode_exact_spot_settlement_v7_journal_v1(&trailing).is_err());
        let mut semantic_hash = bytes;
        let semantic_hash_offset = JOURNAL_HEADER_BYTES_V1 + 8 * 32;
        semantic_hash[semantic_hash_offset] ^= 1;
        assert!(matches!(
            decode_exact_spot_settlement_v7_journal_v1(&semantic_hash),
            Err(SpotSettlementV7ErrorV1::JournalComponentHashMismatch(
                "semantic journal"
            ))
        ));
    }

    fn fixture_journal() -> SpotSettlementV7JournalV1 {
        let (semantic_journal, pre_state, post_state) = fixture();
        let opening = derive_spot_settlement_state_effect_opening_v1(
            &semantic_journal,
            &pre_state,
            &post_state,
        )
        .unwrap();
        let source_plan = source_plan(&opening);
        let bound = bind_spot_settlement_effect_plan_v1(opening, &source_plan).unwrap();
        let semantic_bytes = encode_spot_state_root_v7_semantic_journal_v1(&semantic_journal);
        let plan = bound.plan().clone();
        SpotSettlementV7JournalV1 {
            source_child_program_id: ProgramIdV3::new([0xa1; 32]).unwrap(),
            required_source_child_receipt_security_profile_id:
                required_source_child_receipt_security_profile_id_v1().unwrap(),
            source_child_claim_binding: commitment(0xa2),
            source_child_journal_sha256: commitment(0xa3),
            data_availability_certificate_root: commitment(0xa4),
            data_root: commitment(0xa5),
            source_replay_sha256: commitment(0xa6),
            state_root_host_input_sha256: commitment(0xa7),
            semantic_journal_sha256: sha256_commitment(&semantic_bytes, "semantic journal")
                .unwrap(),
            effect_binding_journal_commitment: bound.journal().canonical_commitment().unwrap(),
            settlement_effect_plan_commitment: plan.canonical_commitment().unwrap(),
            action_ids_root: plan.economic_action_batch().action_ids_root(),
            state_root_host_input_length: 1_024,
            semantic_journal,
            effect_binding_journal: bound.journal().clone(),
            settlement_effect_plan: plan,
        }
    }

    fn fixture() -> (
        SpotStateRootV7SemanticJournalV1,
        DexSnapshotV1,
        DexSnapshotV1,
    ) {
        let v5: Value = serde_json::from_str(V5_FIXTURE).unwrap();
        let v7: Value = serde_json::from_str(V7_FIXTURE).unwrap();
        let pre_state = serde_json::from_value(v5["pre_state"].clone()).unwrap();
        let post_state = serde_json::from_value(v5["post_state"].clone()).unwrap();
        let bytes = decode_hex(v7["journal_hex"].as_str().unwrap());
        let journal = decode_exact_spot_state_root_v7_semantic_journal_v1(&bytes).unwrap();
        (journal, pre_state, post_state)
    }

    fn source_plan(
        opening: &zenodex_zrpf_risc0_spot_settlement_v7_effect_binding_shared::SpotSettlementStateEffectOpeningV1,
    ) -> SettlementEffectPlanV2 {
        let source_pre_root = commitment(0x31);
        let record = EconomicActionRecordV1::new(EconomicActionRecordInputV1 {
            application_id: ApplicationIdV3::new([1; 32]).unwrap(),
            chain_or_domain_id: zenodex_zrpf_protocol_v3::DomainIdV3::new([2; 32]).unwrap(),
            action_type_id: EconomicActionTypeIdV1::new([3; 32]).unwrap(),
            authorization_subject_id: AuthorizationSubjectIdV1::new([4; 32]).unwrap(),
            authorization_scope_id: AuthorizationScopeIdV1::new([5; 32]).unwrap(),
            authorization_nonce: u64::from(opening.ingress_nonce()),
            valid_from_epoch: 9,
            valid_through_epoch: 9,
            pre_state_root: source_pre_root,
            action_semantics_hash: commitment(0x32),
            effect_commitment: commitment(0x33),
            consumed_object_ids: vec![commitment(0x34)],
        })
        .unwrap();
        let action =
            AuthorizedEconomicActionV1::new(record, AuthorizationGrantIdV1::new([6; 32]).unwrap())
                .unwrap();
        let action_id = action.action_id().unwrap();
        let batch = EconomicActionBatchV1::new(9, source_pre_root, vec![action]).unwrap();
        let write = LedgerCellWriteV2::new(LedgerCellWriteInputV2 {
            economic_action_id: action_id,
            cell_key: commitment(0x41),
            pre_value_hash: ValueHashV2::new([0x42; 32]),
            post_value_hash: ValueHashV2::new([0x43; 32]),
        })
        .unwrap();
        let effect = AssetEffectV2::new(AssetEffectInputV2 {
            kind: AssetEffectKindV2::OrdinaryTransfer,
            economic_action_id: action_id,
            asset_id: commitment(0x51),
            debit_atoms: 10,
            credit_atoms: 10,
            authorized_mint_atoms: 0,
            authorized_burn_atoms: 0,
            authority_scope_id: None,
            action_authorization_binding: None,
        })
        .unwrap();
        SettlementEffectPlanV2::new(SettlementEffectPlanInputV2 {
            source_semantic_journal_hash: commitment(0x52),
            public_policy_hash: commitment(0x53),
            post_state_root: commitment(0x54),
            economic_action_batch: batch,
            ledger_cell_writes: vec![write],
            asset_effects: vec![effect],
            message_effects: vec![],
            carry_effects: vec![],
            reward_effects: vec![],
        })
        .unwrap()
    }

    fn commitment(seed: u8) -> CommitmentV3 {
        CommitmentV3::new([seed; 32]).unwrap()
    }

    fn decode_hex(value: &str) -> Vec<u8> {
        value
            .strip_prefix("0x")
            .unwrap()
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| u8::from_str_radix(core::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    }

    fn decode_golden_hex(value: &str) -> Vec<u8> {
        let compact = value
            .lines()
            .filter(|line| !line.starts_with("//"))
            .collect::<alloc::string::String>();
        compact
            .as_bytes()
            .chunks_exact(2)
            .map(|pair| u8::from_str_radix(core::str::from_utf8(pair).unwrap(), 16).unwrap())
            .collect()
    }
}
