use alloc::vec::Vec;
use core::fmt;

use zenodex_zrpf_protocol_v3::{MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_JOURNAL_BYTES_V3};

/// Shared, identity-free disclosure framing used by the historical V1 codec
/// and the active V2 semantic guest input.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticGuestLeafDisclosureV1 {
    journal_bytes: Vec<u8>,
    semantic_opening: [u8; 32],
}

impl SemanticGuestLeafDisclosureV1 {
    pub fn new(
        journal_bytes: Vec<u8>,
        semantic_opening: [u8; 32],
    ) -> Result<Self, SemanticGuestDisclosureErrorV1> {
        validate_journal_length(&journal_bytes).map_err(|length| {
            SemanticGuestDisclosureErrorV1::InvalidLeafJournalLength { length }
        })?;
        Ok(Self {
            journal_bytes,
            semantic_opening,
        })
    }

    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }

    pub const fn semantic_opening(&self) -> [u8; 32] {
        self.semantic_opening
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticGuestLevelOneDisclosureV1 {
    journal_bytes: Vec<u8>,
    leaves: Vec<SemanticGuestLeafDisclosureV1>,
}

impl SemanticGuestLevelOneDisclosureV1 {
    pub fn new(
        journal_bytes: Vec<u8>,
        leaves: Vec<SemanticGuestLeafDisclosureV1>,
    ) -> Result<Self, SemanticGuestDisclosureErrorV1> {
        validate_journal_length(&journal_bytes).map_err(|length| {
            SemanticGuestDisclosureErrorV1::InvalidLevelOneJournalLength { length }
        })?;
        validate_count(leaves.len()).map_err(SemanticGuestDisclosureErrorV1::InvalidLeafCount)?;
        Ok(Self {
            journal_bytes,
            leaves,
        })
    }

    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }

    pub fn leaves(&self) -> &[SemanticGuestLeafDisclosureV1] {
        &self.leaves
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SemanticGuestDisclosureErrorV1 {
    InvalidLevelOneJournalLength { length: usize },
    InvalidLeafJournalLength { length: usize },
    InvalidLeafCount(usize),
}

impl fmt::Display for SemanticGuestDisclosureErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidLevelOneJournalLength { length } => {
                write!(
                    formatter,
                    "invalid semantic level-one journal length: {length}"
                )
            }
            Self::InvalidLeafJournalLength { length } => {
                write!(formatter, "invalid semantic leaf journal length: {length}")
            }
            Self::InvalidLeafCount(count) => {
                write!(formatter, "invalid semantic leaf count: {count}")
            }
        }
    }
}

fn validate_count(count: usize) -> Result<(), usize> {
    if count == 0 || count > MAX_IMMEDIATE_CHILDREN_V3 {
        return Err(count);
    }
    Ok(())
}

fn validate_journal_length(journal: &[u8]) -> Result<(), usize> {
    let length = journal.len();
    if length == 0 || length > MAX_NODE_JOURNAL_BYTES_V3 {
        return Err(length);
    }
    Ok(())
}
