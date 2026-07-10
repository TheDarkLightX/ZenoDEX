use alloc::vec::Vec;

use serde::{Deserialize, Serialize};

use crate::{AdapterErrorV1, SourceKindV1, V1_SOURCE_JOURNAL_MAX_BYTES};

pub const V1_LEAF_ADAPTER_INPUT_SCHEMA_VERSION: u16 = 1;
pub const V1_LEAF_ADAPTER_MAX_INPUT_BYTES: usize = 8 * 1_024;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct V1LeafAdapterInputV1 {
    pub schema_version: u16,
    pub source_kind: SourceKindV1,
    pub source_journal_bytes: Vec<u8>,
    pub assigned_leaf_ordinal: u64,
    pub expected_adapter_image_id: [u32; 8],
}

impl V1LeafAdapterInputV1 {
    pub fn validate_envelope(&self) -> Result<(), AdapterErrorV1> {
        if self.schema_version != V1_LEAF_ADAPTER_INPUT_SCHEMA_VERSION {
            return Err(AdapterErrorV1::InvalidAdapterSchema(self.schema_version));
        }
        if self.source_journal_bytes.is_empty() {
            return Err(AdapterErrorV1::EmptySourceJournal);
        }
        if self.source_journal_bytes.len() > V1_SOURCE_JOURNAL_MAX_BYTES {
            return Err(AdapterErrorV1::SourceJournalTooLarge {
                actual: self.source_journal_bytes.len(),
                maximum: V1_SOURCE_JOURNAL_MAX_BYTES,
            });
        }
        self.assigned_leaf_ordinal
            .checked_add(1)
            .ok_or(AdapterErrorV1::AssignedLeafOrdinalOverflow)?;
        if self.expected_adapter_image_id.iter().all(|word| *word == 0) {
            return Err(AdapterErrorV1::ZeroAdapterImageId);
        }
        Ok(())
    }
}

pub fn decode_exact_adapter_input_v1(bytes: &[u8]) -> Result<V1LeafAdapterInputV1, AdapterErrorV1> {
    if bytes.is_empty() {
        return Err(AdapterErrorV1::EmptyAdapterInput);
    }
    if bytes.len() > V1_LEAF_ADAPTER_MAX_INPUT_BYTES {
        return Err(AdapterErrorV1::AdapterInputTooLarge {
            actual: bytes.len(),
            maximum: V1_LEAF_ADAPTER_MAX_INPUT_BYTES,
        });
    }
    let (input, remainder) = postcard::take_from_bytes::<V1LeafAdapterInputV1>(bytes)
        .map_err(|_| AdapterErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(AdapterErrorV1::TrailingBytes);
    }
    let canonical = postcard::to_allocvec(&input).map_err(|_| AdapterErrorV1::PostcardEncode)?;
    if canonical.as_slice() != bytes {
        return Err(AdapterErrorV1::NonCanonicalEncoding);
    }
    input.validate_envelope()?;
    Ok(input)
}
