use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

use serde::de::{self, Deserialize, Deserializer, SeqAccess, Visitor};

pub(super) fn deserialize_bounded_vec<'de, D, T>(
    deserializer: D,
    maximum: usize,
    label: &'static str,
) -> Result<Vec<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    deserializer.deserialize_seq(BoundedVecVisitor::<T> {
        maximum,
        label,
        marker: PhantomData,
    })
}

struct BoundedVecVisitor<T> {
    maximum: usize,
    label: &'static str,
    marker: PhantomData<T>,
}

impl<'de, T> Visitor<'de> for BoundedVecVisitor<T>
where
    T: Deserialize<'de>,
{
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "{} with at most {} entries",
            self.label, self.maximum
        )
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let size_hint = sequence.size_hint().unwrap_or(0);
        if size_hint > self.maximum {
            return Err(de::Error::invalid_length(size_hint, &self));
        }
        let mut values = Vec::with_capacity(size_hint.min(self.maximum));
        while let Some(value) = sequence.next_element()? {
            if values.len() == self.maximum {
                return Err(de::Error::invalid_length(
                    values.len().saturating_add(1),
                    &self,
                ));
            }
            values.push(value);
        }
        Ok(values)
    }
}
