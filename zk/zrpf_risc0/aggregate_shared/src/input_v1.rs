use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_JOURNAL_BYTES_V3};

pub const STRUCTURAL_AGGREGATE_INPUT_SCHEMA_VERSION_V1: u16 = 1;
const INPUT_HEADER_BYTES: usize = 2 + (8 * 4) + 1;
const CHILD_LENGTH_BYTES: usize = 2;
pub const MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1: usize = INPUT_HEADER_BYTES
    + MAX_IMMEDIATE_CHILDREN_V3 * (CHILD_LENGTH_BYTES + MAX_NODE_JOURNAL_BYTES_V3);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructuralAggregateInputV1 {
    pub expected_self_image_id: [u32; 8],
    pub child_journal_bytes: Vec<Vec<u8>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum StructuralAggregateInputErrorV1 {
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    Truncated,
    InvalidSchema(u16),
    ZeroSelfImageId,
    InvalidChildCount(usize),
    InvalidChildJournalLength { index: usize, length: usize },
    TrailingBytes,
    LengthOverflow,
    NonCanonicalEncoding,
}

impl fmt::Display for StructuralAggregateInputErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("structural aggregate input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(
                    formatter,
                    "structural aggregate input {actual} exceeds {maximum}"
                )
            }
            Self::Truncated => formatter.write_str("structural aggregate input is truncated"),
            Self::InvalidSchema(version) => {
                write!(
                    formatter,
                    "invalid structural aggregate input schema: {version}"
                )
            }
            Self::ZeroSelfImageId => formatter.write_str("structural aggregate self image is zero"),
            Self::InvalidChildCount(count) => {
                write!(
                    formatter,
                    "invalid structural aggregate child count: {count}"
                )
            }
            Self::InvalidChildJournalLength { index, length } => {
                write!(
                    formatter,
                    "invalid child journal length at {index}: {length}"
                )
            }
            Self::TrailingBytes => {
                formatter.write_str("structural aggregate input has trailing bytes")
            }
            Self::LengthOverflow => {
                formatter.write_str("structural aggregate input length overflow")
            }
            Self::NonCanonicalEncoding => {
                formatter.write_str("structural aggregate input is not canonical")
            }
        }
    }
}

impl StructuralAggregateInputV1 {
    pub fn validate(&self) -> Result<(), StructuralAggregateInputErrorV1> {
        if self.expected_self_image_id.iter().all(|word| *word == 0) {
            return Err(StructuralAggregateInputErrorV1::ZeroSelfImageId);
        }
        let count = self.child_journal_bytes.len();
        if count == 0 || count > MAX_IMMEDIATE_CHILDREN_V3 {
            return Err(StructuralAggregateInputErrorV1::InvalidChildCount(count));
        }
        for (index, journal) in self.child_journal_bytes.iter().enumerate() {
            if journal.is_empty() || journal.len() > MAX_NODE_JOURNAL_BYTES_V3 {
                return Err(StructuralAggregateInputErrorV1::InvalidChildJournalLength {
                    index,
                    length: journal.len(),
                });
            }
        }
        Ok(())
    }
}

pub fn encode_structural_aggregate_input_v1(
    input: &StructuralAggregateInputV1,
) -> Result<Vec<u8>, StructuralAggregateInputErrorV1> {
    input.validate()?;
    let mut total = INPUT_HEADER_BYTES;
    for journal in &input.child_journal_bytes {
        total = total
            .checked_add(CHILD_LENGTH_BYTES)
            .and_then(|value| value.checked_add(journal.len()))
            .ok_or(StructuralAggregateInputErrorV1::LengthOverflow)?;
    }
    if total > MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1 {
        return Err(StructuralAggregateInputErrorV1::InputTooLarge {
            actual: total,
            maximum: MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1,
        });
    }
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&STRUCTURAL_AGGREGATE_INPUT_SCHEMA_VERSION_V1.to_be_bytes());
    for word in input.expected_self_image_id {
        bytes.extend_from_slice(&word.to_be_bytes());
    }
    bytes.push(
        u8::try_from(input.child_journal_bytes.len())
            .map_err(|_| StructuralAggregateInputErrorV1::LengthOverflow)?,
    );
    for journal in &input.child_journal_bytes {
        let length = u16::try_from(journal.len())
            .map_err(|_| StructuralAggregateInputErrorV1::LengthOverflow)?;
        bytes.extend_from_slice(&length.to_be_bytes());
        bytes.extend_from_slice(journal);
    }
    Ok(bytes)
}

pub fn decode_exact_structural_aggregate_input_v1(
    bytes: &[u8],
) -> Result<StructuralAggregateInputV1, StructuralAggregateInputErrorV1> {
    if bytes.is_empty() {
        return Err(StructuralAggregateInputErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1 {
        return Err(StructuralAggregateInputErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1,
        });
    }
    let mut cursor = 0usize;
    let schema = read_u16(bytes, &mut cursor)?;
    if schema != STRUCTURAL_AGGREGATE_INPUT_SCHEMA_VERSION_V1 {
        return Err(StructuralAggregateInputErrorV1::InvalidSchema(schema));
    }
    let mut expected_self_image_id = [0u32; 8];
    for word in &mut expected_self_image_id {
        *word = read_u32(bytes, &mut cursor)?;
    }
    let child_count = usize::from(read_u8(bytes, &mut cursor)?);
    if child_count == 0 || child_count > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(StructuralAggregateInputErrorV1::InvalidChildCount(
            child_count,
        ));
    }
    let mut child_journal_bytes = Vec::with_capacity(child_count);
    for index in 0..child_count {
        let length = usize::from(read_u16(bytes, &mut cursor)?);
        if length == 0 || length > MAX_NODE_JOURNAL_BYTES_V3 {
            return Err(StructuralAggregateInputErrorV1::InvalidChildJournalLength {
                index,
                length,
            });
        }
        let end = cursor
            .checked_add(length)
            .ok_or(StructuralAggregateInputErrorV1::LengthOverflow)?;
        let journal = bytes
            .get(cursor..end)
            .ok_or(StructuralAggregateInputErrorV1::Truncated)?;
        child_journal_bytes.push(journal.to_vec());
        cursor = end;
    }
    if cursor != bytes.len() {
        return Err(StructuralAggregateInputErrorV1::TrailingBytes);
    }
    let input = StructuralAggregateInputV1 {
        expected_self_image_id,
        child_journal_bytes,
    };
    input.validate()?;
    let canonical = encode_structural_aggregate_input_v1(&input)?;
    if canonical != bytes {
        return Err(StructuralAggregateInputErrorV1::NonCanonicalEncoding);
    }
    Ok(input)
}

fn read_u8(bytes: &[u8], cursor: &mut usize) -> Result<u8, StructuralAggregateInputErrorV1> {
    let value = *bytes
        .get(*cursor)
        .ok_or(StructuralAggregateInputErrorV1::Truncated)?;
    *cursor = cursor
        .checked_add(1)
        .ok_or(StructuralAggregateInputErrorV1::LengthOverflow)?;
    Ok(value)
}

fn read_u16(bytes: &[u8], cursor: &mut usize) -> Result<u16, StructuralAggregateInputErrorV1> {
    let raw = read_array::<2>(bytes, cursor)?;
    Ok(u16::from_be_bytes(raw))
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32, StructuralAggregateInputErrorV1> {
    let raw = read_array::<4>(bytes, cursor)?;
    Ok(u32::from_be_bytes(raw))
}

fn read_array<const N: usize>(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<[u8; N], StructuralAggregateInputErrorV1> {
    let end = cursor
        .checked_add(N)
        .ok_or(StructuralAggregateInputErrorV1::LengthOverflow)?;
    let raw: [u8; N] = bytes
        .get(*cursor..end)
        .ok_or(StructuralAggregateInputErrorV1::Truncated)?
        .try_into()
        .map_err(|_| StructuralAggregateInputErrorV1::Truncated)?;
    *cursor = end;
    Ok(raw)
}
