use alloc::vec::Vec;
use core::{fmt, marker::PhantomData};

use serde::de::{self, Deserialize, Deserializer, SeqAccess, Visitor};

use super::MAX_LANE_STATE_OPENING_WITNESSES_V1;
use crate::SparseMerkleCellTransitionWitnessV1;

pub(super) fn deserialize_lane_opening_witnesses<'de, D>(
    deserializer: D,
) -> Result<Vec<SparseMerkleCellTransitionWitnessV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct BoundedWitnessVisitor<T>(PhantomData<T>);

    impl<'de, T: Deserialize<'de>> Visitor<'de> for BoundedWitnessVisitor<T> {
        type Value = Vec<T>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "at most {MAX_LANE_STATE_OPENING_WITNESSES_V1} lane state-opening witnesses"
            )
        }

        fn visit_seq<A: SeqAccess<'de>>(self, mut sequence: A) -> Result<Self::Value, A::Error> {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_LANE_STATE_OPENING_WITNESSES_V1 {
                return Err(de::Error::invalid_length(declared, &self));
            }
            let mut witnesses =
                Vec::with_capacity(declared.min(MAX_LANE_STATE_OPENING_WITNESSES_V1));
            while let Some(witness) = sequence.next_element()? {
                if witnesses.len() == MAX_LANE_STATE_OPENING_WITNESSES_V1 {
                    return Err(de::Error::invalid_length(
                        MAX_LANE_STATE_OPENING_WITNESSES_V1 + 1,
                        &self,
                    ));
                }
                witnesses.push(witness);
            }
            Ok(witnesses)
        }
    }

    deserializer.deserialize_seq(BoundedWitnessVisitor(PhantomData))
}
