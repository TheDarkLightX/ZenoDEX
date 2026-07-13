use alloc::vec::Vec;

use zenodex_zrpf_protocol_v3::decode_exact_value_aggregate_proposal_v5;
use zenodex_zrpf_risc0_semantic_shared::{
    bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2,
    decode_exact_ordinary_spot_settlement_guest_envelope_v2,
    encode_ordinary_spot_settlement_guest_input_v2, OrdinarySpotSettlementGuestEnvelopeV2,
    OrdinarySpotSettlementGuestInputV2, MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    decode_exact_source_opened_spot_value_leaf_input_v6,
    encode_source_opened_spot_value_leaf_input_v6, SourceOpenedSpotValueLeafEnvelopeV6,
    MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
};

use crate::{
    require_source_bound_spot_authorization_v6, validate_singleton_source_opened_spot_relation_v6,
    SourceOpenedSpotSettlementErrorV6,
};

pub const SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V3: u16 = 3;
pub const MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3: usize = 2
    + 4
    + MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2
    + 4
    + MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceOpenedSpotSettlementGuestEnvelopeV3 {
    base: OrdinarySpotSettlementGuestEnvelopeV2,
    source: SourceOpenedSpotValueLeafEnvelopeV6,
}

impl SourceOpenedSpotSettlementGuestEnvelopeV3 {
    pub fn proposal_bytes(&self) -> &[u8] {
        self.base.proposal_bytes()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceOpenedSpotSettlementGuestInputV3 {
    base: OrdinarySpotSettlementGuestInputV2,
    source: SourceOpenedSpotValueLeafEnvelopeV6,
}

impl SourceOpenedSpotSettlementGuestInputV3 {
    pub fn new(
        base: OrdinarySpotSettlementGuestInputV2,
        source: SourceOpenedSpotValueLeafEnvelopeV6,
    ) -> Result<Self, SourceOpenedSpotSettlementErrorV6> {
        base.validate_self_consistency()?;
        let proposal = decode_exact_value_aggregate_proposal_v5(base.proposal_bytes())?;
        let statement = validate_singleton_source_opened_spot_relation_v6(&proposal, &source)?;
        require_source_bound_spot_authorization_v6(&statement, base.authorization())?;
        Ok(Self { base, source })
    }

    pub const fn base(&self) -> &OrdinarySpotSettlementGuestInputV2 {
        &self.base
    }

    pub const fn source(&self) -> &SourceOpenedSpotValueLeafEnvelopeV6 {
        &self.source
    }

    pub fn validate_self_consistency(&self) -> Result<(), SourceOpenedSpotSettlementErrorV6> {
        self.base.validate_self_consistency()?;
        let proposal = decode_exact_value_aggregate_proposal_v5(self.base.proposal_bytes())?;
        let statement = validate_singleton_source_opened_spot_relation_v6(&proposal, &self.source)?;
        require_source_bound_spot_authorization_v6(&statement, self.base.authorization())?;
        Ok(())
    }
}

pub fn encode_source_opened_spot_settlement_guest_input_v3(
    input: &SourceOpenedSpotSettlementGuestInputV3,
) -> Result<Vec<u8>, SourceOpenedSpotSettlementErrorV6> {
    input.validate_self_consistency()?;
    let base_bytes = encode_ordinary_spot_settlement_guest_input_v2(input.base())?;
    let source_bytes = encode_source_opened_spot_value_leaf_input_v6(input.source())?;
    encode_parts(&base_bytes, &source_bytes)
}

pub fn decode_exact_source_opened_spot_settlement_guest_envelope_v3(
    bytes: &[u8],
) -> Result<SourceOpenedSpotSettlementGuestEnvelopeV3, SourceOpenedSpotSettlementErrorV6> {
    if bytes.is_empty() {
        return Err(SourceOpenedSpotSettlementErrorV6::EmptyInput);
    }
    if bytes.len() > MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3 {
        return Err(SourceOpenedSpotSettlementErrorV6::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3,
        });
    }
    let mut cursor = CursorV3::new(bytes);
    let version = cursor.read_u16("version")?;
    if version != SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V3 {
        return Err(SourceOpenedSpotSettlementErrorV6::InvalidVersion(version));
    }
    let base = cursor.read_component(
        "base settlement input",
        MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
    )?;
    let source = cursor.read_component(
        "source-opened leaf input",
        MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
    )?;
    if !cursor.is_finished() {
        return Err(SourceOpenedSpotSettlementErrorV6::TrailingBytes);
    }
    Ok(SourceOpenedSpotSettlementGuestEnvelopeV3 {
        base: decode_exact_ordinary_spot_settlement_guest_envelope_v2(base)?,
        source: decode_exact_source_opened_spot_value_leaf_input_v6(source)?,
    })
}

pub fn bind_source_opened_spot_settlement_guest_input_after_l2_receipt_verification_v3(
    envelope: SourceOpenedSpotSettlementGuestEnvelopeV3,
) -> Result<SourceOpenedSpotSettlementGuestInputV3, SourceOpenedSpotSettlementErrorV6> {
    let base =
        bind_ordinary_spot_settlement_guest_input_after_l2_receipt_verification_v2(envelope.base)?;
    SourceOpenedSpotSettlementGuestInputV3::new(base, envelope.source)
}

fn encode_parts(base: &[u8], source: &[u8]) -> Result<Vec<u8>, SourceOpenedSpotSettlementErrorV6> {
    require_component(
        "base settlement input",
        base.len(),
        MAX_ORDINARY_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V2,
    )?;
    require_component(
        "source-opened leaf input",
        source.len(),
        MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
    )?;
    let total = 2_usize
        .checked_add(4)
        .and_then(|value| value.checked_add(base.len()))
        .and_then(|value| value.checked_add(4))
        .and_then(|value| value.checked_add(source.len()))
        .ok_or(SourceOpenedSpotSettlementErrorV6::LengthOverflow(
            "guest total",
        ))?;
    if total > MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3 {
        return Err(SourceOpenedSpotSettlementErrorV6::InputTooLarge {
            actual: total,
            maximum: MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3,
        });
    }
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_VERSION_V3.to_be_bytes());
    write_component(&mut bytes, "base settlement input", base)?;
    write_component(&mut bytes, "source-opened leaf input", source)?;
    Ok(bytes)
}

fn require_component(
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

fn write_component(
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

struct CursorV3<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CursorV3<'a> {
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
