use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};

use super::{
    OrdinarySpotSettlementReplayDataErrorV1, OrdinarySpotSettlementReplayDataV1,
    MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1,
    ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V1,
};

const FIXED_HEADER_BYTES_V1: usize = 10;

pub fn encode_ordinary_spot_settlement_replay_data_v1(
    replay_data: &OrdinarySpotSettlementReplayDataV1,
) -> Result<Vec<u8>, OrdinarySpotSettlementReplayDataErrorV1> {
    replay_data.validate_self_consistency()?;
    let total = require_part_lengths(
        replay_data.proposal_bytes().len(),
        replay_data.settlement_effect_plan_bytes().len(),
    )?;
    let proposal_length = u32::try_from(replay_data.proposal_bytes().len()).map_err(|_| {
        OrdinarySpotSettlementReplayDataErrorV1::ArithmeticOverflow("proposal_length")
    })?;
    let plan_length = u32::try_from(replay_data.settlement_effect_plan_bytes().len())
        .map_err(|_| OrdinarySpotSettlementReplayDataErrorV1::ArithmeticOverflow("plan_length"))?;
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V1.to_be_bytes());
    bytes.extend_from_slice(&proposal_length.to_be_bytes());
    bytes.extend_from_slice(replay_data.proposal_bytes());
    bytes.extend_from_slice(&plan_length.to_be_bytes());
    bytes.extend_from_slice(replay_data.settlement_effect_plan_bytes());
    Ok(bytes)
}

pub fn decode_exact_ordinary_spot_settlement_replay_data_v1(
    bytes: &[u8],
) -> Result<OrdinarySpotSettlementReplayDataV1, OrdinarySpotSettlementReplayDataErrorV1> {
    require_input_size(bytes.len())?;
    let mut cursor = ReplayCursorV1::new(bytes);
    let version = cursor.read_u16("replay_data_version")?;
    if version != ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V1 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::InvalidVersion(
            version,
        ));
    }
    let proposal_length = cursor.read_u32_length("proposal_length")?;
    require_proposal_length(proposal_length)?;
    let proposal_bytes = cursor.read_bytes(proposal_length, "proposal_bytes")?;
    let plan_length = cursor.read_u32_length("plan_length")?;
    require_plan_length(plan_length)?;
    let declared_total = checked_total(proposal_length, plan_length)?;
    if declared_total > MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::InputTooLarge {
            actual: declared_total,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1,
        });
    }
    let plan_bytes = cursor.read_bytes(plan_length, "plan_bytes")?;
    if !cursor.is_finished() {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::TrailingBytes);
    }
    let replay_data = OrdinarySpotSettlementReplayDataV1::from_encoded_parts(
        proposal_bytes.to_vec(),
        plan_bytes.to_vec(),
    )?;
    if encode_ordinary_spot_settlement_replay_data_v1(&replay_data)?.as_slice() != bytes {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::NonCanonicalEncoding);
    }
    Ok(replay_data)
}

pub(super) fn require_part_lengths(
    proposal_length: usize,
    plan_length: usize,
) -> Result<usize, OrdinarySpotSettlementReplayDataErrorV1> {
    require_proposal_length(proposal_length)?;
    require_plan_length(plan_length)?;
    let total = checked_total(proposal_length, plan_length)?;
    if total > MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::InputTooLarge {
            actual: total,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1,
        });
    }
    Ok(total)
}

fn require_input_size(size: usize) -> Result<(), OrdinarySpotSettlementReplayDataErrorV1> {
    if size == 0 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::EmptyInput);
    }
    if size > MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V1,
        });
    }
    Ok(())
}

fn require_proposal_length(length: usize) -> Result<(), OrdinarySpotSettlementReplayDataErrorV1> {
    if length == 0 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::EmptyProposalBytes);
    }
    if length > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        return Err(
            OrdinarySpotSettlementReplayDataErrorV1::ProposalBytesTooLarge {
                actual: length,
                maximum: MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
            },
        );
    }
    Ok(())
}

fn require_plan_length(length: usize) -> Result<(), OrdinarySpotSettlementReplayDataErrorV1> {
    if length == 0 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::EmptyPlanBytes);
    }
    if length > MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 {
        return Err(OrdinarySpotSettlementReplayDataErrorV1::PlanBytesTooLarge {
            actual: length,
            maximum: MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2,
        });
    }
    Ok(())
}

fn checked_total(
    proposal_length: usize,
    plan_length: usize,
) -> Result<usize, OrdinarySpotSettlementReplayDataErrorV1> {
    FIXED_HEADER_BYTES_V1
        .checked_add(proposal_length)
        .and_then(|value| value.checked_add(plan_length))
        .ok_or(OrdinarySpotSettlementReplayDataErrorV1::ArithmeticOverflow(
            "encoded_length",
        ))
}

struct ReplayCursorV1<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ReplayCursorV1<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn read_u16(
        &mut self,
        field: &'static str,
    ) -> Result<u16, OrdinarySpotSettlementReplayDataErrorV1> {
        Ok(u16::from_be_bytes(self.read_array(field)?))
    }

    fn read_u32_length(
        &mut self,
        field: &'static str,
    ) -> Result<usize, OrdinarySpotSettlementReplayDataErrorV1> {
        usize::try_from(u32::from_be_bytes(self.read_array(field)?))
            .map_err(|_| OrdinarySpotSettlementReplayDataErrorV1::ArithmeticOverflow(field))
    }

    fn read_array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<[u8; N], OrdinarySpotSettlementReplayDataErrorV1> {
        self.read_bytes(N, field)?
            .try_into()
            .map_err(|_| OrdinarySpotSettlementReplayDataErrorV1::TruncatedInput(field))
    }

    fn read_bytes(
        &mut self,
        length: usize,
        field: &'static str,
    ) -> Result<&'a [u8], OrdinarySpotSettlementReplayDataErrorV1> {
        let end = self.offset.checked_add(length).ok_or(
            OrdinarySpotSettlementReplayDataErrorV1::ArithmeticOverflow("cursor_offset"),
        )?;
        let value = self.bytes.get(self.offset..end).ok_or(
            OrdinarySpotSettlementReplayDataErrorV1::TruncatedInput(field),
        )?;
        self.offset = end;
        Ok(value)
    }

    const fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
