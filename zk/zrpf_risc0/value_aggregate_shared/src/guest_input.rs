//! Exact bounded framing shared by future V5 aggregate guests and hosts.
//!
//! ```text
//! u16 schema | u8 child-wire kind | u8 child count
//! repeated child count times: u32 byte length | exact child bytes
//! ```
//!
//! Counts and lengths are rejected before their corresponding allocation or
//! payload copy. Claim bindings are deliberately absent from this wire.

use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{
    MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_JOURNAL_BYTES_V4, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};

use crate::{ValueAggregateLevelOneInputV5, ValueAggregateLevelTwoInputV5};

pub const VALUE_AGGREGATE_GUEST_INPUT_SCHEMA_V5: u16 = 1;
const LEVEL_ONE_V4_CHILDREN_TAG: u8 = 1;
const LEVEL_TWO_V5_CHILDREN_TAG: u8 = 2;
const LEVEL_ONE_SOURCE_OPENED_SPOT_V6_CHILDREN_TAG: u8 = 3;
const HEADER_BYTES: usize = 2 + 1 + 1;
const CHILD_LENGTH_BYTES: usize = 4;
const MAX_CHILD_BYTES: usize = if MAX_NODE_JOURNAL_BYTES_V4 > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5
{
    MAX_NODE_JOURNAL_BYTES_V4
} else {
    MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5
};
pub const MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5: usize =
    HEADER_BYTES + MAX_IMMEDIATE_CHILDREN_V3 * (CHILD_LENGTH_BYTES + MAX_CHILD_BYTES);

#[derive(Clone, Debug, PartialEq, Eq)]
/// Exactly framed, proof-neutral bytes presented to a future V5 aggregate guest.
///
/// No claim binding, receipt metadata, or caller assertion is encoded. A guest
/// must verify each exact child journal under its governed image and let the
/// recomposer establish inner canonicality before using the corresponding
/// composition wrapper.
pub enum ValueAggregateGuestInputV5 {
    LevelOne(ValueAggregateLevelOneInputV5),
    LevelOneSourceOpenedSpotV6(ValueAggregateLevelOneInputV5),
    LevelTwo(ValueAggregateLevelTwoInputV5),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ValueAggregateGuestInputErrorV5 {
    EmptyInput,
    InputTooLarge {
        actual: usize,
        maximum: usize,
    },
    Truncated,
    InvalidSchema(u16),
    InvalidChildWireKind(u8),
    InvalidChildCount(usize),
    EmptyChild(usize),
    ChildTooLarge {
        child: usize,
        actual: usize,
        maximum: usize,
    },
    TrailingBytes,
    LengthOverflow,
    NonCanonicalEncoding,
}

impl fmt::Display for ValueAggregateGuestInputErrorV5 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("V5 guest input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "V5 guest input {actual} exceeds {maximum}")
            }
            Self::Truncated => formatter.write_str("V5 guest input is truncated"),
            Self::InvalidSchema(schema) => write!(formatter, "invalid V5 input schema: {schema}"),
            Self::InvalidChildWireKind(kind) => {
                write!(formatter, "invalid V5 child wire kind: {kind}")
            }
            Self::InvalidChildCount(count) => {
                write!(formatter, "invalid V5 guest child count: {count}")
            }
            Self::EmptyChild(child) => write!(formatter, "V5 guest child {child} is empty"),
            Self::ChildTooLarge {
                child,
                actual,
                maximum,
            } => write!(
                formatter,
                "V5 guest child {child} length {actual} exceeds {maximum}"
            ),
            Self::TrailingBytes => formatter.write_str("V5 guest input has trailing bytes"),
            Self::LengthOverflow => formatter.write_str("V5 guest input length overflow"),
            Self::NonCanonicalEncoding => formatter.write_str("V5 guest input is not canonical"),
        }
    }
}

pub fn encode_value_aggregate_guest_input_v5(
    input: &ValueAggregateGuestInputV5,
) -> Result<Vec<u8>, ValueAggregateGuestInputErrorV5> {
    let (tag, children) = match input {
        ValueAggregateGuestInputV5::LevelOne(input) => {
            (LEVEL_ONE_V4_CHILDREN_TAG, input.child_journal_bytes())
        }
        ValueAggregateGuestInputV5::LevelOneSourceOpenedSpotV6(input) => (
            LEVEL_ONE_SOURCE_OPENED_SPOT_V6_CHILDREN_TAG,
            input.child_journal_bytes(),
        ),
        ValueAggregateGuestInputV5::LevelTwo(input) => {
            (LEVEL_TWO_V5_CHILDREN_TAG, input.child_proposal_bytes())
        }
    };
    let maximum = maximum_child_bytes(tag)?;
    validate_child_count(children.len())?;
    let mut total = HEADER_BYTES;
    for (index, child) in children.iter().enumerate() {
        validate_child_length(index, child.len(), maximum)?;
        total = total
            .checked_add(CHILD_LENGTH_BYTES)
            .and_then(|value| value.checked_add(child.len()))
            .ok_or(ValueAggregateGuestInputErrorV5::LengthOverflow)?;
    }
    if total > MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 {
        return Err(ValueAggregateGuestInputErrorV5::InputTooLarge {
            actual: total,
            maximum: MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5,
        });
    }
    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&VALUE_AGGREGATE_GUEST_INPUT_SCHEMA_V5.to_be_bytes());
    bytes.push(tag);
    bytes.push(
        u8::try_from(children.len())
            .map_err(|_| ValueAggregateGuestInputErrorV5::LengthOverflow)?,
    );
    for child in children {
        let length = u32::try_from(child.len())
            .map_err(|_| ValueAggregateGuestInputErrorV5::LengthOverflow)?;
        bytes.extend_from_slice(&length.to_be_bytes());
        bytes.extend_from_slice(child);
    }
    Ok(bytes)
}

pub fn decode_exact_value_aggregate_guest_input_v5(
    bytes: &[u8],
) -> Result<ValueAggregateGuestInputV5, ValueAggregateGuestInputErrorV5> {
    if bytes.is_empty() {
        return Err(ValueAggregateGuestInputErrorV5::EmptyInput);
    }
    if bytes.len() > MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 {
        return Err(ValueAggregateGuestInputErrorV5::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5,
        });
    }
    let mut cursor = 0usize;
    let schema = read_u16(bytes, &mut cursor)?;
    if schema != VALUE_AGGREGATE_GUEST_INPUT_SCHEMA_V5 {
        return Err(ValueAggregateGuestInputErrorV5::InvalidSchema(schema));
    }
    let tag = read_u8(bytes, &mut cursor)?;
    let maximum = maximum_child_bytes(tag)?;
    let child_count = usize::from(read_u8(bytes, &mut cursor)?);
    validate_child_count(child_count)?;
    let mut children = Vec::with_capacity(child_count);
    for index in 0..child_count {
        let length = usize::try_from(read_u32(bytes, &mut cursor)?)
            .map_err(|_| ValueAggregateGuestInputErrorV5::LengthOverflow)?;
        validate_child_length(index, length, maximum)?;
        let end = cursor
            .checked_add(length)
            .ok_or(ValueAggregateGuestInputErrorV5::LengthOverflow)?;
        let child = bytes
            .get(cursor..end)
            .ok_or(ValueAggregateGuestInputErrorV5::Truncated)?;
        children.push(child.to_vec());
        cursor = end;
    }
    if cursor != bytes.len() {
        return Err(ValueAggregateGuestInputErrorV5::TrailingBytes);
    }
    let input = match tag {
        LEVEL_ONE_V4_CHILDREN_TAG => ValueAggregateGuestInputV5::LevelOne(
            ValueAggregateLevelOneInputV5::new(children)
                .map_err(|_| ValueAggregateGuestInputErrorV5::NonCanonicalEncoding)?,
        ),
        LEVEL_ONE_SOURCE_OPENED_SPOT_V6_CHILDREN_TAG => {
            ValueAggregateGuestInputV5::LevelOneSourceOpenedSpotV6(
                ValueAggregateLevelOneInputV5::new(children)
                    .map_err(|_| ValueAggregateGuestInputErrorV5::NonCanonicalEncoding)?,
            )
        }
        LEVEL_TWO_V5_CHILDREN_TAG => ValueAggregateGuestInputV5::LevelTwo(
            ValueAggregateLevelTwoInputV5::new(children)
                .map_err(|_| ValueAggregateGuestInputErrorV5::NonCanonicalEncoding)?,
        ),
        _ => return Err(ValueAggregateGuestInputErrorV5::InvalidChildWireKind(tag)),
    };
    if encode_value_aggregate_guest_input_v5(&input)?.as_slice() != bytes {
        return Err(ValueAggregateGuestInputErrorV5::NonCanonicalEncoding);
    }
    Ok(input)
}

fn maximum_child_bytes(tag: u8) -> Result<usize, ValueAggregateGuestInputErrorV5> {
    match tag {
        LEVEL_ONE_V4_CHILDREN_TAG | LEVEL_ONE_SOURCE_OPENED_SPOT_V6_CHILDREN_TAG => {
            Ok(MAX_NODE_JOURNAL_BYTES_V4)
        }
        LEVEL_TWO_V5_CHILDREN_TAG => Ok(MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5),
        _ => Err(ValueAggregateGuestInputErrorV5::InvalidChildWireKind(tag)),
    }
}

fn validate_child_count(count: usize) -> Result<(), ValueAggregateGuestInputErrorV5> {
    if count == 0 || count > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(ValueAggregateGuestInputErrorV5::InvalidChildCount(count));
    }
    Ok(())
}

fn validate_child_length(
    child: usize,
    actual: usize,
    maximum: usize,
) -> Result<(), ValueAggregateGuestInputErrorV5> {
    if actual == 0 {
        return Err(ValueAggregateGuestInputErrorV5::EmptyChild(child));
    }
    if actual > maximum {
        return Err(ValueAggregateGuestInputErrorV5::ChildTooLarge {
            child,
            actual,
            maximum,
        });
    }
    Ok(())
}

fn read_u8(bytes: &[u8], cursor: &mut usize) -> Result<u8, ValueAggregateGuestInputErrorV5> {
    let value = *bytes
        .get(*cursor)
        .ok_or(ValueAggregateGuestInputErrorV5::Truncated)?;
    *cursor = cursor
        .checked_add(1)
        .ok_or(ValueAggregateGuestInputErrorV5::LengthOverflow)?;
    Ok(value)
}

fn read_u16(bytes: &[u8], cursor: &mut usize) -> Result<u16, ValueAggregateGuestInputErrorV5> {
    Ok(u16::from_be_bytes(read_array(bytes, cursor)?))
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32, ValueAggregateGuestInputErrorV5> {
    Ok(u32::from_be_bytes(read_array(bytes, cursor)?))
}

fn read_array<const N: usize>(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<[u8; N], ValueAggregateGuestInputErrorV5> {
    let end = cursor
        .checked_add(N)
        .ok_or(ValueAggregateGuestInputErrorV5::LengthOverflow)?;
    let value = bytes
        .get(*cursor..end)
        .ok_or(ValueAggregateGuestInputErrorV5::Truncated)?
        .try_into()
        .map_err(|_| ValueAggregateGuestInputErrorV5::Truncated)?;
    *cursor = end;
    Ok(value)
}
