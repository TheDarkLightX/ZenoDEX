use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, MAX_FULL_BLOB_DA_BYTES_V1};
use zenodex_zrpf_risc0_semantic_shared::{
    encode_ordinary_spot_settlement_replay_data_v2, OrdinarySpotSettlementReplayDataV2,
};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    encode_source_opened_spot_value_leaf_input_v6, SourceOpenedSpotValueLeafEnvelopeV6,
    MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
};

use crate::SourceOpenedSpotSettlementErrorV6;

pub const SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_VERSION_V3: u16 = 3;
const REPLAY_SCHEMA_DOMAIN_V3: &[u8] =
    b"zenodex.zrpf.source_opened_spot_settlement_replay.schema.v3";

pub fn encode_source_opened_spot_settlement_replay_v3(
    base: &OrdinarySpotSettlementReplayDataV2,
    source: &SourceOpenedSpotValueLeafEnvelopeV6,
) -> Result<Vec<u8>, SourceOpenedSpotSettlementErrorV6> {
    let base_bytes = encode_ordinary_spot_settlement_replay_data_v2(base)?;
    let source_bytes = encode_source_opened_spot_value_leaf_input_v6(source)?;
    require_component("base replay", base_bytes.len(), MAX_FULL_BLOB_DA_BYTES_V1)?;
    require_component(
        "source-opened leaf",
        source_bytes.len(),
        MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
    )?;
    let total = 2_usize
        .checked_add(4)
        .and_then(|value| value.checked_add(base_bytes.len()))
        .and_then(|value| value.checked_add(4))
        .and_then(|value| value.checked_add(source_bytes.len()))
        .ok_or(SourceOpenedSpotSettlementErrorV6::LengthOverflow(
            "replay total",
        ))?;
    if total > MAX_FULL_BLOB_DA_BYTES_V1 {
        return Err(SourceOpenedSpotSettlementErrorV6::InputTooLarge {
            actual: total,
            maximum: MAX_FULL_BLOB_DA_BYTES_V1,
        });
    }
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_VERSION_V3.to_be_bytes());
    write_component(&mut bytes, "base replay", &base_bytes)?;
    write_component(&mut bytes, "source-opened leaf", &source_bytes)?;
    Ok(bytes)
}

pub fn source_opened_spot_settlement_replay_schema_id_v3(
) -> Result<CommitmentV3, SourceOpenedSpotSettlementErrorV6> {
    let length = u16::try_from(REPLAY_SCHEMA_DOMAIN_V3.len())
        .map_err(|_| SourceOpenedSpotSettlementErrorV6::LengthOverflow("schema domain"))?;
    let mut hasher = Sha256::new();
    hasher.update(length.to_be_bytes());
    hasher.update(REPLAY_SCHEMA_DOMAIN_V3);
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| SourceOpenedSpotSettlementErrorV6::InvalidDerivedCommitment("schema"))
}

pub(crate) fn require_component(
    component: &'static str,
    actual: usize,
    maximum: usize,
) -> Result<(), SourceOpenedSpotSettlementErrorV6> {
    if actual == 0 {
        return Err(SourceOpenedSpotSettlementErrorV6::EmptyComponent(component));
    }
    if actual > maximum {
        return Err(SourceOpenedSpotSettlementErrorV6::ComponentTooLarge {
            component,
            actual,
            maximum,
        });
    }
    Ok(())
}

pub(crate) fn write_component(
    output: &mut Vec<u8>,
    component: &'static str,
    bytes: &[u8],
) -> Result<(), SourceOpenedSpotSettlementErrorV6> {
    let length = u32::try_from(bytes.len())
        .map_err(|_| SourceOpenedSpotSettlementErrorV6::LengthOverflow(component))?;
    output.extend_from_slice(&length.to_be_bytes());
    output.extend_from_slice(bytes);
    Ok(())
}
