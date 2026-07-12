use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::{
    decode_exact_sparse_merkle_cell_transition_witness_v1,
    encode_sparse_merkle_cell_transition_witness_v1, MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2,
    MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};

use super::{
    OrdinarySpotSettlementReplayDataErrorV2, OrdinarySpotSettlementReplayDataV2,
    MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2,
    ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V2,
};
use crate::spot_certificate_v1::wire_v2::{
    read_authorization_v2, write_authorization_v2, ExactCursorV2, AUTHORIZATION_BYTES_V2,
};

const FIXED_HEADER_BYTES_V2: usize = 2 + 4 + AUTHORIZATION_BYTES_V2 + 4 + 4;

pub fn encode_ordinary_spot_settlement_replay_data_v2(
    replay: &OrdinarySpotSettlementReplayDataV2,
) -> Result<Vec<u8>, OrdinarySpotSettlementReplayDataErrorV2> {
    replay.validate_self_consistency()?;
    let witness_bytes = encode_sparse_merkle_cell_transition_witness_v1(replay.witness())?;
    let total = require_part_lengths(
        replay.proposal_bytes().len(),
        witness_bytes.len(),
        replay.settlement_effect_plan_bytes().len(),
    )?;
    let proposal_length = length_to_u32(replay.proposal_bytes().len(), "proposal_length")?;
    let witness_length = length_to_u32(witness_bytes.len(), "witness_length")?;
    let plan_length = length_to_u32(replay.settlement_effect_plan_bytes().len(), "plan_length")?;
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V2.to_be_bytes());
    bytes.extend_from_slice(&proposal_length.to_be_bytes());
    bytes.extend_from_slice(replay.proposal_bytes());
    write_authorization_v2(&mut bytes, replay.authorization())?;
    bytes.extend_from_slice(&witness_length.to_be_bytes());
    bytes.extend_from_slice(&witness_bytes);
    bytes.extend_from_slice(&plan_length.to_be_bytes());
    bytes.extend_from_slice(replay.settlement_effect_plan_bytes());
    Ok(bytes)
}

pub fn decode_exact_ordinary_spot_settlement_replay_data_v2(
    bytes: &[u8],
) -> Result<OrdinarySpotSettlementReplayDataV2, OrdinarySpotSettlementReplayDataErrorV2> {
    require_input_size(bytes.len())?;
    let mut cursor = ExactCursorV2::new(bytes);
    let version = cursor.read_u16("replay_data_version")?;
    if version != ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_VERSION_V2 {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::InvalidVersion(
            version,
        ));
    }
    let proposal_length = cursor.read_u32_length("proposal_length")?;
    require_proposal_length(proposal_length)?;
    let proposal_bytes = cursor.read_bytes(proposal_length, "proposal_bytes")?;
    let authorization = read_authorization_v2(&mut cursor)?;
    let witness_length = cursor.read_u32_length("witness_length")?;
    require_witness_length(witness_length)?;
    let witness_bytes = cursor.read_bytes(witness_length, "witness_bytes")?;
    let plan_length = cursor.read_u32_length("plan_length")?;
    require_plan_length(plan_length)?;
    require_total(proposal_length, witness_length, plan_length)?;
    let plan_bytes = cursor.read_bytes(plan_length, "plan_bytes")?;
    if !cursor.is_finished() {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::TrailingBytes);
    }
    let witness = decode_exact_sparse_merkle_cell_transition_witness_v1(witness_bytes)?;
    let replay = OrdinarySpotSettlementReplayDataV2::from_encoded_parts(
        proposal_bytes.to_vec(),
        authorization,
        witness,
        plan_bytes.to_vec(),
    )?;
    if encode_ordinary_spot_settlement_replay_data_v2(&replay)?.as_slice() != bytes {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::NonCanonicalEncoding);
    }
    Ok(replay)
}

pub(super) fn require_part_lengths(
    proposal_length: usize,
    witness_length: usize,
    plan_length: usize,
) -> Result<usize, OrdinarySpotSettlementReplayDataErrorV2> {
    require_proposal_length(proposal_length)?;
    require_witness_length(witness_length)?;
    require_plan_length(plan_length)?;
    require_total(proposal_length, witness_length, plan_length)
}

fn require_input_size(size: usize) -> Result<(), OrdinarySpotSettlementReplayDataErrorV2> {
    if size == 0 {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::EmptyInput);
    }
    if size > MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2 {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::InputTooLarge {
            actual: size,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2,
        });
    }
    Ok(())
}

fn require_proposal_length(length: usize) -> Result<(), OrdinarySpotSettlementReplayDataErrorV2> {
    if length == 0 {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::EmptyProposalBytes);
    }
    if length > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        return Err(
            OrdinarySpotSettlementReplayDataErrorV2::ProposalBytesTooLarge {
                actual: length,
                maximum: MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
            },
        );
    }
    Ok(())
}

fn require_witness_length(length: usize) -> Result<(), OrdinarySpotSettlementReplayDataErrorV2> {
    if length == 0 {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::EmptyWitnessBytes);
    }
    if length > MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1 {
        return Err(
            OrdinarySpotSettlementReplayDataErrorV2::WitnessBytesTooLarge {
                actual: length,
                maximum: MAX_SPARSE_MERKLE_CELL_TRANSITION_WITNESS_BYTES_V1,
            },
        );
    }
    Ok(())
}

fn require_plan_length(length: usize) -> Result<(), OrdinarySpotSettlementReplayDataErrorV2> {
    if length == 0 {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::EmptyPlanBytes);
    }
    if length > MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2 {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::PlanBytesTooLarge {
            actual: length,
            maximum: MAX_SETTLEMENT_EFFECT_PLAN_BYTES_V2,
        });
    }
    Ok(())
}

fn require_total(
    proposal_length: usize,
    witness_length: usize,
    plan_length: usize,
) -> Result<usize, OrdinarySpotSettlementReplayDataErrorV2> {
    let total = FIXED_HEADER_BYTES_V2
        .checked_add(proposal_length)
        .and_then(|value| value.checked_add(witness_length))
        .and_then(|value| value.checked_add(plan_length))
        .ok_or(OrdinarySpotSettlementReplayDataErrorV2::ArithmeticOverflow(
            "encoded_length",
        ))?;
    if total > MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2 {
        return Err(OrdinarySpotSettlementReplayDataErrorV2::InputTooLarge {
            actual: total,
            maximum: MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2,
        });
    }
    Ok(total)
}

fn length_to_u32(
    length: usize,
    field: &'static str,
) -> Result<u32, OrdinarySpotSettlementReplayDataErrorV2> {
    u32::try_from(length)
        .map_err(|_| OrdinarySpotSettlementReplayDataErrorV2::ArithmeticOverflow(field))
}
