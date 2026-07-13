use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, MAX_FULL_BLOB_DA_BYTES_V1};
use zenodex_zrpf_risc0_semantic_shared::{
    decode_exact_ordinary_spot_settlement_replay_data_v2,
    encode_ordinary_spot_settlement_replay_data_v2, OrdinarySpotSettlementReplayDataV2,
    MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2,
};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    decode_exact_source_opened_spot_value_leaf_input_v6,
    encode_source_opened_spot_value_leaf_input_v6, SourceOpenedSpotValueLeafEnvelopeV6,
    MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
};

use crate::SourceOpenedSpotSettlementErrorV6;

pub const SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_VERSION_V3: u16 = 3;
pub const MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3: usize = MAX_FULL_BLOB_DA_BYTES_V1;
const REPLAY_SCHEMA_DOMAIN_V3: &[u8] =
    b"zenodex.zrpf.source_opened_spot_settlement_replay.schema.v3";

/// Exact proof-neutral opening of one source-opened V6 replay blob.
///
/// This type proves only canonical decoding. It carries no receipt or data-
/// availability authority. A V7 guest must first verify the V6 settlement
/// receipt, require the supplied full-blob certificate root to equal the
/// authenticated child journal, and validate these exact replay bytes against
/// that certificate before constructing an authority-bearing local wrapper.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v6_shared::ProposedSourceOpenedSpotSettlementReplayV3;
/// let proposed: ProposedSourceOpenedSpotSettlementReplayV3 = unimplemented!();
/// let _ = proposed.receipt_verified();
/// ```
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_settlement_v6_shared::ProposedSourceOpenedSpotSettlementReplayV3;
/// let proposed: ProposedSourceOpenedSpotSettlementReplayV3 = unimplemented!();
/// let _ = proposed.settlement_authority();
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProposedSourceOpenedSpotSettlementReplayV3 {
    base: OrdinarySpotSettlementReplayDataV2,
    source: SourceOpenedSpotValueLeafEnvelopeV6,
}

impl ProposedSourceOpenedSpotSettlementReplayV3 {
    pub const fn base(&self) -> &OrdinarySpotSettlementReplayDataV2 {
        &self.base
    }

    pub const fn source(&self) -> &SourceOpenedSpotValueLeafEnvelopeV6 {
        &self.source
    }
}

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

/// Strictly decodes one canonical replay-v3 blob without authenticating it.
pub fn decode_exact_source_opened_spot_settlement_replay_v3(
    bytes: &[u8],
) -> Result<ProposedSourceOpenedSpotSettlementReplayV3, SourceOpenedSpotSettlementErrorV6> {
    if bytes.is_empty() {
        return Err(SourceOpenedSpotSettlementErrorV6::EmptyInput);
    }
    if bytes.len() > MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3 {
        return Err(SourceOpenedSpotSettlementErrorV6::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_BYTES_V3,
        });
    }

    let mut cursor = ReplayCursorV3::new(bytes);
    let version = cursor.read_u16("replay version")?;
    if version != SOURCE_OPENED_SPOT_SETTLEMENT_REPLAY_VERSION_V3 {
        return Err(SourceOpenedSpotSettlementErrorV6::InvalidVersion(version));
    }
    let base_bytes = cursor.read_component(
        "base replay",
        MAX_ORDINARY_SPOT_SETTLEMENT_REPLAY_DATA_BYTES_V2,
    )?;
    let source_bytes = cursor.read_component(
        "source-opened leaf",
        MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
    )?;
    if !cursor.is_finished() {
        return Err(SourceOpenedSpotSettlementErrorV6::TrailingBytes);
    }

    let replay = ProposedSourceOpenedSpotSettlementReplayV3 {
        base: decode_exact_ordinary_spot_settlement_replay_data_v2(base_bytes)?,
        source: decode_exact_source_opened_spot_value_leaf_input_v6(source_bytes)?,
    };
    if encode_source_opened_spot_settlement_replay_v3(&replay.base, &replay.source)?.as_slice()
        != bytes
    {
        return Err(SourceOpenedSpotSettlementErrorV6::NonCanonicalReplay);
    }
    Ok(replay)
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

struct ReplayCursorV3<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> ReplayCursorV3<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn read_u16(&mut self, field: &'static str) -> Result<u16, SourceOpenedSpotSettlementErrorV6> {
        Ok(u16::from_be_bytes(self.read_array(field)?))
    }

    fn read_u32(&mut self, field: &'static str) -> Result<u32, SourceOpenedSpotSettlementErrorV6> {
        Ok(u32::from_be_bytes(self.read_array(field)?))
    }

    fn read_component(
        &mut self,
        component: &'static str,
        maximum: usize,
    ) -> Result<&'a [u8], SourceOpenedSpotSettlementErrorV6> {
        let length = usize::try_from(self.read_u32(component)?)
            .map_err(|_| SourceOpenedSpotSettlementErrorV6::LengthOverflow(component))?;
        require_component(component, length, maximum)?;
        self.read(length, component)
    }

    fn read_array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<[u8; N], SourceOpenedSpotSettlementErrorV6> {
        self.read(N, field)?
            .try_into()
            .map_err(|_| SourceOpenedSpotSettlementErrorV6::Truncated(field))
    }

    fn read(
        &mut self,
        length: usize,
        field: &'static str,
    ) -> Result<&'a [u8], SourceOpenedSpotSettlementErrorV6> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(SourceOpenedSpotSettlementErrorV6::LengthOverflow(field))?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(SourceOpenedSpotSettlementErrorV6::Truncated(field))?;
        self.offset = end;
        Ok(value)
    }

    const fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
