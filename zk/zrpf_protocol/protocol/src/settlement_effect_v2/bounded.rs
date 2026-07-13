use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

use serde::de::{self, Deserialize, Deserializer, SeqAccess, Visitor};

use super::MAX_SETTLEMENT_EFFECT_ROWS_V2;

pub(super) fn deserialize_settlement_rows<'de, D, T>(deserializer: D) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    deserializer.deserialize_seq(SettlementRowsVisitor::<T> {
        marker: PhantomData,
    })
}

struct SettlementRowsVisitor<T> {
    marker: PhantomData<T>,
}

impl<'de, T> Visitor<'de> for SettlementRowsVisitor<T>
where
    T: Deserialize<'de>,
{
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "at most {MAX_SETTLEMENT_EFFECT_ROWS_V2} settlement rows"
        )
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let declared = sequence.size_hint().unwrap_or(0);
        if declared > MAX_SETTLEMENT_EFFECT_ROWS_V2 {
            return Err(de::Error::invalid_length(declared, &self));
        }
        let mut values = Vec::with_capacity(declared.min(MAX_SETTLEMENT_EFFECT_ROWS_V2));
        while let Some(value) = sequence.next_element()? {
            if values.len() == MAX_SETTLEMENT_EFFECT_ROWS_V2 {
                return Err(de::Error::invalid_length(values.len() + 1, &self));
            }
            values.push(value);
        }
        Ok(values)
    }
}
