use alloc::vec::Vec;
use core::{fmt, marker::PhantomData};

use serde::de::{self, Deserialize, Deserializer, SeqAccess, Visitor};

use super::{
    GlobalAssetReconciliationV1, GlobalEconomicEffectRowV1, MAX_GLOBAL_ASSET_RECONCILIATIONS_V1,
    MAX_GLOBAL_ECONOMIC_EFFECT_ROWS_V1,
};

pub(super) fn deserialize_effect_rows<'de, D>(
    deserializer: D,
) -> Result<Vec<GlobalEconomicEffectRowV1>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded(
        deserializer,
        MAX_GLOBAL_ECONOMIC_EFFECT_ROWS_V1,
        "global economic effect rows",
    )
}

pub(super) fn deserialize_reconciliations<'de, D>(
    deserializer: D,
) -> Result<Vec<GlobalAssetReconciliationV1>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded(
        deserializer,
        MAX_GLOBAL_ASSET_RECONCILIATIONS_V1,
        "global asset reconciliations",
    )
}

fn deserialize_bounded<'de, D, T>(
    deserializer: D,
    maximum: usize,
    label: &'static str,
) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    struct BoundedVisitor<T> {
        maximum: usize,
        label: &'static str,
        marker: PhantomData<T>,
    }
    impl<'de, T: Deserialize<'de>> Visitor<'de> for BoundedVisitor<T> {
        type Value = Vec<T>;
        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(formatter, "at most {} {}", self.maximum, self.label)
        }
        fn visit_seq<A: SeqAccess<'de>>(self, mut sequence: A) -> Result<Self::Value, A::Error> {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > self.maximum {
                return Err(de::Error::invalid_length(declared, &self));
            }
            let mut rows = Vec::with_capacity(declared.min(self.maximum));
            while let Some(row) = sequence.next_element()? {
                if rows.len() == self.maximum {
                    return Err(de::Error::invalid_length(self.maximum + 1, &self));
                }
                rows.push(row);
            }
            Ok(rows)
        }
    }
    deserializer.deserialize_seq(BoundedVisitor {
        maximum,
        label,
        marker: PhantomData,
    })
}
