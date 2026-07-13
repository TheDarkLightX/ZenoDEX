use alloc::vec::Vec;

use tau_state_proof_risc0_shared::RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES;
use zenodex_zrpf_protocol_v3::MAX_NODE_JOURNAL_BYTES_V3;
use zenodex_zrpf_risc0_shared::V1_SOURCE_JOURNAL_MAX_BYTES;

use crate::SourceOpenedSpotValueLeafErrorV6;

pub const SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_SCHEMA_V6: u16 = 6;
pub const MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6: usize = 2
    + 8
    + (3 * 4)
    + MAX_NODE_JOURNAL_BYTES_V3
    + RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES as usize
    + V1_SOURCE_JOURNAL_MAX_BYTES;

const _: () = assert!(MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6 == 1_056_790);

/// Proposal-opaque V6 envelope decoded before adapter receipt verification.
///
/// Only the exact adapter journal bytes are publicly readable at this stage.
/// Source input and source journal interpretation occur after an enclosing
/// guest authenticates these adapter bytes under the pinned successor image.
///
/// ```compile_fail
/// use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::SourceOpenedSpotValueLeafEnvelopeV6;
/// let envelope: SourceOpenedSpotValueLeafEnvelopeV6 = unimplemented!();
/// let _ = envelope.expected_self_image_id();
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceOpenedSpotValueLeafEnvelopeV6 {
    assigned_leaf_ordinal: u64,
    adapter_journal_bytes: Vec<u8>,
    source_input_bytes: Vec<u8>,
    source_journal_bytes: Vec<u8>,
}

impl SourceOpenedSpotValueLeafEnvelopeV6 {
    pub fn new(
        assigned_leaf_ordinal: u64,
        adapter_journal_bytes: Vec<u8>,
        source_input_bytes: Vec<u8>,
        source_journal_bytes: Vec<u8>,
    ) -> Result<Self, SourceOpenedSpotValueLeafErrorV6> {
        assigned_leaf_ordinal.checked_add(1).ok_or(
            SourceOpenedSpotValueLeafErrorV6::LengthOverflow("assigned_leaf_ordinal"),
        )?;
        validate_component(
            "adapter journal",
            adapter_journal_bytes.len(),
            MAX_NODE_JOURNAL_BYTES_V3,
        )?;
        validate_component(
            "source input",
            source_input_bytes.len(),
            RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES as usize,
        )?;
        validate_component(
            "source journal",
            source_journal_bytes.len(),
            V1_SOURCE_JOURNAL_MAX_BYTES,
        )?;
        Ok(Self {
            assigned_leaf_ordinal,
            adapter_journal_bytes,
            source_input_bytes,
            source_journal_bytes,
        })
    }

    pub fn adapter_journal_bytes(&self) -> &[u8] {
        &self.adapter_journal_bytes
    }

    pub(crate) const fn assigned_leaf_ordinal(&self) -> u64 {
        self.assigned_leaf_ordinal
    }

    pub(crate) fn source_input_bytes(&self) -> &[u8] {
        &self.source_input_bytes
    }

    pub(crate) fn source_journal_bytes(&self) -> &[u8] {
        &self.source_journal_bytes
    }
}

pub fn encode_source_opened_spot_value_leaf_input_v6(
    input: &SourceOpenedSpotValueLeafEnvelopeV6,
) -> Result<Vec<u8>, SourceOpenedSpotValueLeafErrorV6> {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_SCHEMA_V6.to_be_bytes());
    bytes.extend_from_slice(&input.assigned_leaf_ordinal.to_be_bytes());
    write_component(&mut bytes, "adapter journal", &input.adapter_journal_bytes)?;
    write_component(&mut bytes, "source input", &input.source_input_bytes)?;
    write_component(&mut bytes, "source journal", &input.source_journal_bytes)?;
    if bytes.len() > MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6 {
        return Err(SourceOpenedSpotValueLeafErrorV6::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_source_opened_spot_value_leaf_input_v6(
    bytes: &[u8],
) -> Result<SourceOpenedSpotValueLeafEnvelopeV6, SourceOpenedSpotValueLeafErrorV6> {
    if bytes.is_empty() {
        return Err(SourceOpenedSpotValueLeafErrorV6::EmptyInput);
    }
    if bytes.len() > MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6 {
        return Err(SourceOpenedSpotValueLeafErrorV6::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
        });
    }
    let mut cursor = CursorV6::new(bytes);
    let schema = cursor.read_u16("schema")?;
    if schema != SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_SCHEMA_V6 {
        return Err(SourceOpenedSpotValueLeafErrorV6::InvalidInputSchema(schema));
    }
    let assigned_leaf_ordinal = cursor.read_u64("assigned_leaf_ordinal")?;
    let adapter_journal_bytes =
        cursor.read_component("adapter journal", MAX_NODE_JOURNAL_BYTES_V3)?;
    let source_input_bytes =
        cursor.read_component("source input", RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES as usize)?;
    let source_journal_bytes =
        cursor.read_component("source journal", V1_SOURCE_JOURNAL_MAX_BYTES)?;
    if !cursor.is_finished() {
        return Err(SourceOpenedSpotValueLeafErrorV6::TrailingInputBytes);
    }
    let input = SourceOpenedSpotValueLeafEnvelopeV6::new(
        assigned_leaf_ordinal,
        adapter_journal_bytes,
        source_input_bytes,
        source_journal_bytes,
    )?;
    if encode_source_opened_spot_value_leaf_input_v6(&input)?.as_slice() != bytes {
        return Err(SourceOpenedSpotValueLeafErrorV6::NonCanonicalInput);
    }
    Ok(input)
}

fn validate_component(
    component: &'static str,
    actual: usize,
    maximum: usize,
) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    if actual == 0 {
        return Err(SourceOpenedSpotValueLeafErrorV6::EmptyComponent(component));
    }
    if actual > maximum {
        return Err(SourceOpenedSpotValueLeafErrorV6::ComponentTooLarge {
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
) -> Result<(), SourceOpenedSpotValueLeafErrorV6> {
    let length = u32::try_from(bytes.len())
        .map_err(|_| SourceOpenedSpotValueLeafErrorV6::LengthOverflow(component))?;
    output.extend_from_slice(&length.to_be_bytes());
    output.extend_from_slice(bytes);
    Ok(())
}

struct CursorV6<'a> {
    bytes: &'a [u8],
    offset: usize,
}

impl<'a> CursorV6<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, offset: 0 }
    }

    fn read_u16(&mut self, field: &'static str) -> Result<u16, SourceOpenedSpotValueLeafErrorV6> {
        Ok(u16::from_be_bytes(self.read_array(field)?))
    }

    fn read_u32(&mut self, field: &'static str) -> Result<u32, SourceOpenedSpotValueLeafErrorV6> {
        Ok(u32::from_be_bytes(self.read_array(field)?))
    }

    fn read_u64(&mut self, field: &'static str) -> Result<u64, SourceOpenedSpotValueLeafErrorV6> {
        Ok(u64::from_be_bytes(self.read_array(field)?))
    }

    fn read_component(
        &mut self,
        component: &'static str,
        maximum: usize,
    ) -> Result<Vec<u8>, SourceOpenedSpotValueLeafErrorV6> {
        let length = usize::try_from(self.read_u32(component)?)
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::LengthOverflow(component))?;
        validate_component(component, length, maximum)?;
        Ok(self.read(length, component)?.to_vec())
    }

    fn read_array<const N: usize>(
        &mut self,
        field: &'static str,
    ) -> Result<[u8; N], SourceOpenedSpotValueLeafErrorV6> {
        self.read(N, field)?
            .try_into()
            .map_err(|_| SourceOpenedSpotValueLeafErrorV6::TruncatedInput(field))
    }

    fn read(
        &mut self,
        length: usize,
        field: &'static str,
    ) -> Result<&'a [u8], SourceOpenedSpotValueLeafErrorV6> {
        let end = self
            .offset
            .checked_add(length)
            .ok_or(SourceOpenedSpotValueLeafErrorV6::LengthOverflow(field))?;
        let value = self
            .bytes
            .get(self.offset..end)
            .ok_or(SourceOpenedSpotValueLeafErrorV6::TruncatedInput(field))?;
        self.offset = end;
        Ok(value)
    }

    const fn is_finished(&self) -> bool {
        self.offset == self.bytes.len()
    }
}
