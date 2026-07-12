use alloc::vec::Vec;
use core::fmt;
use core::marker::PhantomData;

use serde::de::{self, Deserialize, Deserializer, SeqAccess, Visitor};

use crate::{
    ZusdValueFlowErrorV1, ZusdValueFlowRowV1, ZusdValueOperationV1,
    MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1, MAX_ZUSD_VALUE_FLOW_ROWS_V1,
};

pub(crate) fn deserialize_operations<'de, D>(
    deserializer: D,
) -> Result<Vec<ZusdValueOperationV1>, D::Error>
where
    D: Deserializer<'de>,
{
    deserializer.deserialize_seq(BoundedVisitor::<ZusdValueOperationV1> {
        maximum: MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1,
        collection: "operations",
        marker: PhantomData,
    })
}

pub(crate) fn deserialize_rows<'de, D>(deserializer: D) -> Result<Vec<ZusdValueFlowRowV1>, D::Error>
where
    D: Deserializer<'de>,
{
    deserializer.deserialize_seq(BoundedVisitor::<ZusdValueFlowRowV1> {
        maximum: MAX_ZUSD_VALUE_FLOW_ROWS_V1,
        collection: "rows",
        marker: PhantomData,
    })
}

struct BoundedVisitor<T> {
    maximum: usize,
    collection: &'static str,
    marker: PhantomData<T>,
}

impl<'de, T> Visitor<'de> for BoundedVisitor<T>
where
    T: Deserialize<'de>,
{
    type Value = Vec<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "at most {} zUSD {}",
            self.maximum, self.collection
        )
    }

    fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let declared = sequence.size_hint().unwrap_or(0);
        if declared > self.maximum {
            return Err(de::Error::custom(bound_error(
                self.collection,
                declared,
                self.maximum,
            )));
        }
        let mut values = Vec::with_capacity(declared.min(self.maximum));
        while let Some(value) = sequence.next_element()? {
            if values.len() == self.maximum {
                return Err(de::Error::custom(bound_error(
                    self.collection,
                    self.maximum + 1,
                    self.maximum,
                )));
            }
            values.push(value);
        }
        Ok(values)
    }
}

fn bound_error(collection: &str, actual: usize, maximum: usize) -> ZusdValueFlowErrorV1 {
    if collection == "operations" {
        ZusdValueFlowErrorV1::TooManyOperations { actual, maximum }
    } else {
        ZusdValueFlowErrorV1::TooManyRows { actual, maximum }
    }
}
