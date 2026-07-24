use alloc::vec::Vec;

use super::hash::sha256;
use super::{
    SettlementAdmissionJournalErrorV1, SettlementAdmissionJournalV1,
    MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1, SETTLEMENT_ADMISSION_FIXED_BYTES_V1,
    SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1, SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1,
};
use crate::{
    decode_exact_settlement_effect_plan_v2, decode_exact_settlement_epoch_certificate_v1,
    CommitmentV3, SettlementSemanticRootV1, MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2,
    MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1,
};

pub fn encode_settlement_admission_journal_v1(
    journal: &SettlementAdmissionJournalV1,
) -> Result<Vec<u8>, SettlementAdmissionJournalErrorV1> {
    journal.validate_self_consistency()?;
    encode_unchecked(journal)
}

pub fn decode_exact_settlement_admission_journal_v1(
    bytes: &[u8],
) -> Result<SettlementAdmissionJournalV1, SettlementAdmissionJournalErrorV1> {
    require_size(bytes.len())?;
    let mut reader = Reader::new(bytes);
    if reader.read_array::<8>()? != SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1 {
        return Err(SettlementAdmissionJournalErrorV1::InvalidMagic);
    }
    let version = reader.read_u16()?;
    if version != SETTLEMENT_ADMISSION_JOURNAL_VERSION_V1 {
        return Err(SettlementAdmissionJournalErrorV1::InvalidVersion(version));
    }
    let declared_total = usize::try_from(reader.read_u32()?).map_err(|_| {
        SettlementAdmissionJournalErrorV1::ArithmeticOverflow("declared_total_length")
    })?;
    if bytes.len() > declared_total {
        return Err(SettlementAdmissionJournalErrorV1::TrailingBytes);
    }
    if bytes.len() < declared_total {
        return Err(SettlementAdmissionJournalErrorV1::TruncatedInput);
    }
    let certificate_len = usize::try_from(reader.read_u32()?)
        .map_err(|_| SettlementAdmissionJournalErrorV1::ArithmeticOverflow("certificate_length"))?;
    let effect_plan_len = usize::try_from(reader.read_u32()?)
        .map_err(|_| SettlementAdmissionJournalErrorV1::ArithmeticOverflow("effect_plan_length"))?;
    require_inner_lengths(certificate_len, effect_plan_len)?;
    let expected_total = SETTLEMENT_ADMISSION_FIXED_BYTES_V1
        .checked_add(certificate_len)
        .and_then(|value| value.checked_add(effect_plan_len))
        .ok_or(SettlementAdmissionJournalErrorV1::ArithmeticOverflow(
            "framed_total_length",
        ))?;
    if declared_total != expected_total {
        return Err(SettlementAdmissionJournalErrorV1::FrameLengthMismatch);
    }

    let certificate_bytes = reader.read_slice(certificate_len)?;
    let effect_plan_bytes = reader.read_slice(effect_plan_len)?;
    let certificate_sha256 = reader.read_array::<32>()?;
    if sha256(certificate_bytes) != certificate_sha256 {
        return Err(SettlementAdmissionJournalErrorV1::CertificateHashMismatch);
    }
    let effect_plan_sha256 = reader.read_array::<32>()?;
    if sha256(effect_plan_bytes) != effect_plan_sha256 {
        return Err(SettlementAdmissionJournalErrorV1::EffectPlanHashMismatch);
    }

    let certificate = decode_exact_settlement_epoch_certificate_v1(certificate_bytes)?;
    let effect_plan = decode_exact_settlement_effect_plan_v2(effect_plan_bytes)?;
    let expected = SettlementAdmissionJournalV1::derive(&certificate, &effect_plan)?;
    if encode_unchecked(&expected)?.as_slice() != bytes {
        return Err(SettlementAdmissionJournalErrorV1::DuplicatedFieldMismatch);
    }
    Ok(expected)
}

pub(super) fn encode_unchecked(
    journal: &SettlementAdmissionJournalV1,
) -> Result<Vec<u8>, SettlementAdmissionJournalErrorV1> {
    let certificate_len = u32::try_from(journal.certificate_bytes().len())
        .map_err(|_| SettlementAdmissionJournalErrorV1::ArithmeticOverflow("certificate_length"))?;
    let effect_plan_len = u32::try_from(journal.effect_plan_bytes().len())
        .map_err(|_| SettlementAdmissionJournalErrorV1::ArithmeticOverflow("effect_plan_length"))?;
    require_inner_lengths(
        usize::try_from(certificate_len).map_err(|_| {
            SettlementAdmissionJournalErrorV1::ArithmeticOverflow("certificate_length")
        })?,
        usize::try_from(effect_plan_len).map_err(|_| {
            SettlementAdmissionJournalErrorV1::ArithmeticOverflow("effect_plan_length")
        })?,
    )?;
    let total_len = SETTLEMENT_ADMISSION_FIXED_BYTES_V1
        .checked_add(journal.certificate_bytes().len())
        .and_then(|value| value.checked_add(journal.effect_plan_bytes().len()))
        .ok_or(SettlementAdmissionJournalErrorV1::ArithmeticOverflow(
            "journal_length",
        ))?;
    require_size(total_len)?;
    let total_len_u32 = u32::try_from(total_len)
        .map_err(|_| SettlementAdmissionJournalErrorV1::ArithmeticOverflow("journal_length"))?;
    let mut bytes = Vec::with_capacity(total_len);
    bytes.extend_from_slice(&SETTLEMENT_ADMISSION_JOURNAL_MAGIC_V1);
    write_u16(&mut bytes, journal.journal_version());
    write_u32(&mut bytes, total_len_u32);
    write_u32(&mut bytes, certificate_len);
    write_u32(&mut bytes, effect_plan_len);
    bytes.extend_from_slice(journal.certificate_bytes());
    bytes.extend_from_slice(journal.effect_plan_bytes());
    bytes.extend_from_slice(&journal.certificate_sha256());
    bytes.extend_from_slice(&journal.effect_plan_sha256());
    write_u16(&mut bytes, journal.certificate_version());
    write_u16(&mut bytes, journal.effect_plan_version());
    bytes.extend_from_slice(journal.application_id().as_bytes());
    bytes.extend_from_slice(journal.chain_or_domain_id().as_bytes());
    write_u64(&mut bytes, journal.epoch_id());
    bytes.extend_from_slice(journal.semantic_profile_id().as_bytes());
    write_commitment(&mut bytes, journal.semantic_journal_hash());
    write_commitment(&mut bytes, journal.semantic_claim_binding());
    write_commitment(&mut bytes, journal.proof_tree_root());
    write_semantic_root(&mut bytes, journal.semantic_root());
    write_commitment(&mut bytes, journal.dependency_manifest_root());
    write_commitment(&mut bytes, journal.public_policy_hash());
    write_commitment(&mut bytes, journal.economic_action_batch_commitment());
    write_commitment(&mut bytes, journal.settlement_effect_plan_commitment());
    write_commitment(&mut bytes, journal.economic_action_ids_root());
    write_commitment(&mut bytes, journal.action_authorization_bindings_root());
    write_commitment(&mut bytes, journal.authorization_grant_spends_root());
    write_commitment(&mut bytes, journal.consumed_object_ids_root());
    write_u32(&mut bytes, journal.action_count());
    write_u32(&mut bytes, journal.consumed_object_count());
    for root in [
        journal.pre_state_root(),
        journal.post_state_root(),
        journal.cell_writes_root(),
        journal.asset_effects_root(),
        journal.messages_root(),
        journal.carries_root(),
        journal.rewards_root(),
        journal.data_availability_certificate_root(),
        journal.schedule_certificate_root(),
        journal.carry_continuity_certificate_root(),
        journal.settlement_certificate_id(),
        journal.certificate_commitment(),
    ] {
        write_commitment(&mut bytes, root);
    }
    if bytes.len() != total_len {
        return Err(SettlementAdmissionJournalErrorV1::FrameLengthMismatch);
    }
    Ok(bytes)
}

fn write_semantic_root(bytes: &mut Vec<u8>, root: SettlementSemanticRootV1) {
    match root {
        SettlementSemanticRootV1::SemanticEpoch(commitment) => {
            bytes.push(0);
            write_commitment(bytes, commitment);
        }
        SettlementSemanticRootV1::ValueSubtree(commitment) => {
            bytes.push(1);
            write_commitment(bytes, commitment);
        }
    }
}

fn write_commitment(bytes: &mut Vec<u8>, value: CommitmentV3) {
    bytes.extend_from_slice(value.as_bytes());
}

fn write_u16(bytes: &mut Vec<u8>, value: u16) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn write_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn write_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_be_bytes());
}

fn require_size(size: usize) -> Result<(), SettlementAdmissionJournalErrorV1> {
    if size == 0 {
        return Err(SettlementAdmissionJournalErrorV1::EmptyInput);
    }
    if size > MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1 {
        return Err(SettlementAdmissionJournalErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_SETTLEMENT_ADMISSION_JOURNAL_BYTES_V1,
        });
    }
    Ok(())
}

fn require_inner_lengths(
    certificate_len: usize,
    effect_plan_len: usize,
) -> Result<(), SettlementAdmissionJournalErrorV1> {
    if certificate_len == 0 || certificate_len > MAX_SETTLEMENT_EPOCH_CERTIFICATE_BYTES_V1 {
        return Err(SettlementAdmissionJournalErrorV1::CertificateLengthInvalid);
    }
    if effect_plan_len == 0 || effect_plan_len > MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 {
        return Err(SettlementAdmissionJournalErrorV1::EffectPlanLengthInvalid);
    }
    Ok(())
}

struct Reader<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> Reader<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn read_array<const N: usize>(&mut self) -> Result<[u8; N], SettlementAdmissionJournalErrorV1> {
        self.read_slice(N)?
            .try_into()
            .map_err(|_| SettlementAdmissionJournalErrorV1::TruncatedInput)
    }

    fn read_slice(&mut self, length: usize) -> Result<&'a [u8], SettlementAdmissionJournalErrorV1> {
        let end = self.offset.checked_add(length).ok_or(
            SettlementAdmissionJournalErrorV1::ArithmeticOverflow("frame_offset"),
        )?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(SettlementAdmissionJournalErrorV1::TruncatedInput)?;
        self.offset = end;
        Ok(value)
    }

    fn read_u16(&mut self) -> Result<u16, SettlementAdmissionJournalErrorV1> {
        Ok(u16::from_be_bytes(self.read_array()?))
    }

    fn read_u32(&mut self) -> Result<u32, SettlementAdmissionJournalErrorV1> {
        Ok(u32::from_be_bytes(self.read_array()?))
    }
}
