use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, IgnoredAny, SeqAccess, Visitor},
    Deserializer,
};

use super::{
    SparseMerkleBatchEntryV1, SparseMerkleBatchTransitionErrorV1,
    MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1,
};

pub(super) fn deserialize_batch_entries<'de, D>(
    deserializer: D,
) -> Result<Vec<SparseMerkleBatchEntryV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BatchEntriesVisitor;

    impl<'de> Visitor<'de> for BatchEntriesVisitor {
        type Value = Vec<SparseMerkleBatchEntryV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "1..={MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1} sparse-Merkle batch entries"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence
                .size_hint()
                .ok_or_else(|| de::Error::custom("missing sparse-Merkle batch entry count"))?;
            require_entry_count(declared).map_err(de::Error::custom)?;
            let mut entries = Vec::new();
            entries.try_reserve_exact(declared).map_err(|_| {
                de::Error::custom(SparseMerkleBatchTransitionErrorV1::AllocationFailed(
                    "entries",
                ))
            })?;
            for index in 0..declared {
                entries.push(
                    sequence
                        .next_element()?
                        .ok_or_else(|| de::Error::invalid_length(index, &self))?,
                );
            }
            if sequence.next_element::<IgnoredAny>()?.is_some() {
                let excess = declared.checked_add(1).ok_or_else(|| {
                    de::Error::custom(SparseMerkleBatchTransitionErrorV1::ArithmeticOverflow(
                        "entry_count",
                    ))
                })?;
                return Err(de::Error::invalid_length(excess, &self));
            }
            Ok(entries)
        }
    }

    deserializer.deserialize_seq(BatchEntriesVisitor)
}

pub(super) fn require_entry_count(count: usize) -> Result<(), SparseMerkleBatchTransitionErrorV1> {
    if count == 0 {
        return Err(SparseMerkleBatchTransitionErrorV1::EmptyBatch);
    }
    if count > MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1 {
        return Err(SparseMerkleBatchTransitionErrorV1::TooManyEntries {
            actual: count,
            maximum: MAX_SPARSE_MERKLE_BATCH_ENTRIES_V1,
        });
    }
    Ok(())
}
