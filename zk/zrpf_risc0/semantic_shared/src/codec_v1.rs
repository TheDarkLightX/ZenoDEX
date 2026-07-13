use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_JOURNAL_BYTES_V3};

use crate::{
    SemanticGuestDisclosureErrorV1, SemanticGuestLeafDisclosureV1,
    SemanticGuestLevelOneDisclosureV1,
};

pub const SEMANTIC_GUEST_INPUT_SCHEMA_VERSION_V1: u16 = 1;

const INPUT_HEADER_BYTES_V1: usize = 2 + (8 * 4) + 1;
const LEVEL_ONE_HEADER_BYTES_V1: usize = 2 + 1;
const LEAF_FIXED_BYTES_V1: usize = 2 + 32;

pub const MAX_SEMANTIC_GUEST_INPUT_BYTES_V1: usize = INPUT_HEADER_BYTES_V1
    + MAX_IMMEDIATE_CHILDREN_V3
        * (LEVEL_ONE_HEADER_BYTES_V1
            + MAX_NODE_JOURNAL_BYTES_V3
            + MAX_IMMEDIATE_CHILDREN_V3 * (LEAF_FIXED_BYTES_V1 + MAX_NODE_JOURNAL_BYTES_V3));

const _: () = assert!(MAX_SEMANTIC_GUEST_INPUT_BYTES_V1 == 297_147);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticGuestInputV1 {
    expected_self_image_id: [u32; 8],
    level_one_disclosures: Vec<SemanticGuestLevelOneDisclosureV1>,
}

impl SemanticGuestInputV1 {
    pub fn new(
        expected_self_image_id: [u32; 8],
        level_one_disclosures: Vec<SemanticGuestLevelOneDisclosureV1>,
    ) -> Result<Self, SemanticGuestInputErrorV1> {
        let input = Self {
            expected_self_image_id,
            level_one_disclosures,
        };
        input.validate()?;
        Ok(input)
    }

    pub const fn expected_self_image_id(&self) -> [u32; 8] {
        self.expected_self_image_id
    }

    pub fn level_one_disclosures(&self) -> &[SemanticGuestLevelOneDisclosureV1] {
        &self.level_one_disclosures
    }

    fn validate(&self) -> Result<(), SemanticGuestInputErrorV1> {
        if self.expected_self_image_id.iter().all(|word| *word == 0) {
            return Err(SemanticGuestInputErrorV1::ZeroSelfImageId);
        }
        validate_count(self.level_one_disclosures.len())
            .map_err(SemanticGuestInputErrorV1::InvalidLevelOneCount)?;
        for disclosure in &self.level_one_disclosures {
            validate_journal_length(disclosure.journal_bytes()).map_err(|length| {
                SemanticGuestInputErrorV1::InvalidLevelOneJournalLength { length }
            })?;
            validate_count(disclosure.leaves().len())
                .map_err(SemanticGuestInputErrorV1::InvalidLeafCount)?;
            for leaf in disclosure.leaves() {
                validate_journal_length(leaf.journal_bytes()).map_err(|length| {
                    SemanticGuestInputErrorV1::InvalidLeafJournalLength { length }
                })?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SemanticGuestInputErrorV1 {
    EmptyInput,
    InputTooLarge { actual: usize, maximum: usize },
    Truncated,
    InvalidSchema(u16),
    ZeroSelfImageId,
    InvalidLevelOneCount(usize),
    InvalidLeafCount(usize),
    InvalidLevelOneJournalLength { length: usize },
    InvalidLeafJournalLength { length: usize },
    TrailingBytes,
    LengthOverflow,
    NonCanonicalEncoding,
}

impl fmt::Display for SemanticGuestInputErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::EmptyInput => formatter.write_str("semantic guest input is empty"),
            Self::InputTooLarge { actual, maximum } => {
                write!(formatter, "semantic guest input {actual} exceeds {maximum}")
            }
            Self::Truncated => formatter.write_str("semantic guest input is truncated"),
            Self::InvalidSchema(version) => {
                write!(formatter, "invalid semantic guest input schema: {version}")
            }
            Self::ZeroSelfImageId => formatter.write_str("semantic guest self image is zero"),
            Self::InvalidLevelOneCount(count) => {
                write!(formatter, "invalid semantic level-one count: {count}")
            }
            Self::InvalidLeafCount(count) => {
                write!(formatter, "invalid semantic leaf count: {count}")
            }
            Self::InvalidLevelOneJournalLength { length } => {
                write!(
                    formatter,
                    "invalid semantic level-one journal length: {length}"
                )
            }
            Self::InvalidLeafJournalLength { length } => {
                write!(formatter, "invalid semantic leaf journal length: {length}")
            }
            Self::TrailingBytes => formatter.write_str("semantic guest input has trailing bytes"),
            Self::LengthOverflow => formatter.write_str("semantic guest input length overflow"),
            Self::NonCanonicalEncoding => {
                formatter.write_str("semantic guest input is not canonical")
            }
        }
    }
}

pub fn encode_semantic_guest_input_v1(
    input: &SemanticGuestInputV1,
) -> Result<Vec<u8>, SemanticGuestInputErrorV1> {
    input.validate()?;
    let total = encoded_length(input)?;
    if total > MAX_SEMANTIC_GUEST_INPUT_BYTES_V1 {
        return Err(SemanticGuestInputErrorV1::InputTooLarge {
            actual: total,
            maximum: MAX_SEMANTIC_GUEST_INPUT_BYTES_V1,
        });
    }

    let mut bytes = Vec::with_capacity(total);
    bytes.extend_from_slice(&SEMANTIC_GUEST_INPUT_SCHEMA_VERSION_V1.to_be_bytes());
    for word in input.expected_self_image_id() {
        bytes.extend_from_slice(&word.to_be_bytes());
    }
    bytes.push(count_to_u8(input.level_one_disclosures().len())?);
    for disclosure in input.level_one_disclosures() {
        write_journal(&mut bytes, disclosure.journal_bytes())?;
        bytes.push(count_to_u8(disclosure.leaves().len())?);
        for leaf in disclosure.leaves() {
            write_journal(&mut bytes, leaf.journal_bytes())?;
            bytes.extend_from_slice(&leaf.semantic_opening());
        }
    }
    Ok(bytes)
}

pub fn decode_exact_semantic_guest_input_v1(
    bytes: &[u8],
) -> Result<SemanticGuestInputV1, SemanticGuestInputErrorV1> {
    if bytes.is_empty() {
        return Err(SemanticGuestInputErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_SEMANTIC_GUEST_INPUT_BYTES_V1 {
        return Err(SemanticGuestInputErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_SEMANTIC_GUEST_INPUT_BYTES_V1,
        });
    }

    let mut cursor = 0usize;
    let schema = read_u16(bytes, &mut cursor)?;
    if schema != SEMANTIC_GUEST_INPUT_SCHEMA_VERSION_V1 {
        return Err(SemanticGuestInputErrorV1::InvalidSchema(schema));
    }
    let mut expected_self_image_id = [0u32; 8];
    for word in &mut expected_self_image_id {
        *word = read_u32(bytes, &mut cursor)?;
    }
    if expected_self_image_id.iter().all(|word| *word == 0) {
        return Err(SemanticGuestInputErrorV1::ZeroSelfImageId);
    }

    let level_one_count = usize::from(read_u8(bytes, &mut cursor)?);
    validate_count(level_one_count).map_err(SemanticGuestInputErrorV1::InvalidLevelOneCount)?;
    let level_one_disclosures = read_level_one_disclosures(bytes, &mut cursor, level_one_count)?;
    if cursor != bytes.len() {
        return Err(SemanticGuestInputErrorV1::TrailingBytes);
    }

    let input = SemanticGuestInputV1::new(expected_self_image_id, level_one_disclosures)?;
    if encode_semantic_guest_input_v1(&input)? != bytes {
        return Err(SemanticGuestInputErrorV1::NonCanonicalEncoding);
    }
    Ok(input)
}

fn encoded_length(input: &SemanticGuestInputV1) -> Result<usize, SemanticGuestInputErrorV1> {
    let mut total = INPUT_HEADER_BYTES_V1;
    for disclosure in input.level_one_disclosures() {
        total = checked_add(total, LEVEL_ONE_HEADER_BYTES_V1)?;
        total = checked_add(total, disclosure.journal_bytes().len())?;
        for leaf in disclosure.leaves() {
            total = checked_add(total, LEAF_FIXED_BYTES_V1)?;
            total = checked_add(total, leaf.journal_bytes().len())?;
        }
    }
    Ok(total)
}

fn read_level_one_disclosures(
    bytes: &[u8],
    cursor: &mut usize,
    count: usize,
) -> Result<Vec<SemanticGuestLevelOneDisclosureV1>, SemanticGuestInputErrorV1> {
    let mut disclosures = Vec::with_capacity(count);
    for _ in 0..count {
        disclosures.push(read_level_one_disclosure(bytes, cursor)?);
    }
    Ok(disclosures)
}

fn read_level_one_disclosure(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<SemanticGuestLevelOneDisclosureV1, SemanticGuestInputErrorV1> {
    let journal = read_journal(bytes, cursor, JournalKindV1::LevelOne)?;
    let leaf_count = usize::from(read_u8(bytes, cursor)?);
    validate_count(leaf_count).map_err(SemanticGuestInputErrorV1::InvalidLeafCount)?;
    let mut leaves = Vec::with_capacity(leaf_count);
    for _ in 0..leaf_count {
        let leaf_journal = read_journal(bytes, cursor, JournalKindV1::Leaf)?;
        let semantic_opening = read_array::<32>(bytes, cursor)?;
        leaves.push(
            SemanticGuestLeafDisclosureV1::new(leaf_journal, semantic_opening)
                .map_err(map_disclosure_error)?,
        );
    }
    SemanticGuestLevelOneDisclosureV1::new(journal, leaves).map_err(map_disclosure_error)
}

fn map_disclosure_error(error: SemanticGuestDisclosureErrorV1) -> SemanticGuestInputErrorV1 {
    match error {
        SemanticGuestDisclosureErrorV1::InvalidLevelOneJournalLength { length } => {
            SemanticGuestInputErrorV1::InvalidLevelOneJournalLength { length }
        }
        SemanticGuestDisclosureErrorV1::InvalidLeafJournalLength { length } => {
            SemanticGuestInputErrorV1::InvalidLeafJournalLength { length }
        }
        SemanticGuestDisclosureErrorV1::InvalidLeafCount(count) => {
            SemanticGuestInputErrorV1::InvalidLeafCount(count)
        }
    }
}

#[derive(Clone, Copy)]
enum JournalKindV1 {
    LevelOne,
    Leaf,
}

fn read_journal(
    bytes: &[u8],
    cursor: &mut usize,
    kind: JournalKindV1,
) -> Result<Vec<u8>, SemanticGuestInputErrorV1> {
    let length = usize::from(read_u16(bytes, cursor)?);
    if validate_journal_length_value(length).is_err() {
        return match kind {
            JournalKindV1::LevelOne => {
                Err(SemanticGuestInputErrorV1::InvalidLevelOneJournalLength { length })
            }
            JournalKindV1::Leaf => {
                Err(SemanticGuestInputErrorV1::InvalidLeafJournalLength { length })
            }
        };
    }
    let end = checked_add(*cursor, length)?;
    let journal = bytes
        .get(*cursor..end)
        .ok_or(SemanticGuestInputErrorV1::Truncated)?;
    *cursor = end;
    Ok(journal.to_vec())
}

fn write_journal(bytes: &mut Vec<u8>, journal: &[u8]) -> Result<(), SemanticGuestInputErrorV1> {
    let length =
        u16::try_from(journal.len()).map_err(|_| SemanticGuestInputErrorV1::LengthOverflow)?;
    bytes.extend_from_slice(&length.to_be_bytes());
    bytes.extend_from_slice(journal);
    Ok(())
}

fn validate_count(count: usize) -> Result<(), usize> {
    if count == 0 || count > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(count);
    }
    Ok(())
}

fn validate_journal_length(journal: &[u8]) -> Result<(), usize> {
    validate_journal_length_value(journal.len())
}

fn validate_journal_length_value(length: usize) -> Result<(), usize> {
    if length == 0 || length > MAX_NODE_JOURNAL_BYTES_V3 {
        return Err(length);
    }
    Ok(())
}

fn count_to_u8(count: usize) -> Result<u8, SemanticGuestInputErrorV1> {
    u8::try_from(count).map_err(|_| SemanticGuestInputErrorV1::LengthOverflow)
}

fn checked_add(left: usize, right: usize) -> Result<usize, SemanticGuestInputErrorV1> {
    left.checked_add(right)
        .ok_or(SemanticGuestInputErrorV1::LengthOverflow)
}

fn read_u8(bytes: &[u8], cursor: &mut usize) -> Result<u8, SemanticGuestInputErrorV1> {
    let value = *bytes
        .get(*cursor)
        .ok_or(SemanticGuestInputErrorV1::Truncated)?;
    *cursor = checked_add(*cursor, 1)?;
    Ok(value)
}

fn read_u16(bytes: &[u8], cursor: &mut usize) -> Result<u16, SemanticGuestInputErrorV1> {
    Ok(u16::from_be_bytes(read_array::<2>(bytes, cursor)?))
}

fn read_u32(bytes: &[u8], cursor: &mut usize) -> Result<u32, SemanticGuestInputErrorV1> {
    Ok(u32::from_be_bytes(read_array::<4>(bytes, cursor)?))
}

fn read_array<const N: usize>(
    bytes: &[u8],
    cursor: &mut usize,
) -> Result<[u8; N], SemanticGuestInputErrorV1> {
    let end = checked_add(*cursor, N)?;
    let raw = bytes
        .get(*cursor..end)
        .ok_or(SemanticGuestInputErrorV1::Truncated)?
        .try_into()
        .map_err(|_| SemanticGuestInputErrorV1::Truncated)?;
    *cursor = end;
    Ok(raw)
}
