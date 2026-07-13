use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserializer, Serialize,
};

use super::{
    AuthorizedEconomicActionV1, EconomicActionBatchErrorV1, EconomicActionBatchV1,
    MAX_ECONOMIC_ACTIONS_PER_BATCH_V1, MAX_ECONOMIC_ACTION_BATCH_BYTES_V1,
};

pub fn encode_economic_action_batch_v1(
    batch: &EconomicActionBatchV1,
) -> Result<Vec<u8>, EconomicActionBatchErrorV1> {
    batch.validate_self_consistency()?;
    let bytes =
        postcard::to_allocvec(batch).map_err(|_| EconomicActionBatchErrorV1::PostcardDecode)?;
    require_input_size(bytes.len())?;
    Ok(bytes)
}

pub fn decode_exact_economic_action_batch_v1(
    bytes: &[u8],
) -> Result<EconomicActionBatchV1, EconomicActionBatchErrorV1> {
    require_input_size(bytes.len())?;
    let (batch, remainder) = postcard::take_from_bytes::<EconomicActionBatchV1>(bytes)
        .map_err(|_| EconomicActionBatchErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(EconomicActionBatchErrorV1::TrailingBytes);
    }
    if encode_economic_action_batch_v1(&batch)?.as_slice() != bytes {
        return Err(EconomicActionBatchErrorV1::NonCanonicalEncoding);
    }
    Ok(batch)
}

pub(super) fn serialize_actions<S>(
    actions: &[AuthorizedEconomicActionV1],
    serializer: S,
) -> Result<S::Ok, S::Error>
where
    S: serde::Serializer,
{
    actions.serialize(serializer)
}

pub(super) fn deserialize_actions<'de, D>(
    deserializer: D,
) -> Result<Vec<AuthorizedEconomicActionV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct ActionsVisitor;

    impl<'de> Visitor<'de> for ActionsVisitor {
        type Value = Vec<AuthorizedEconomicActionV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "1..={MAX_ECONOMIC_ACTIONS_PER_BATCH_V1} authorized economic actions"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_ECONOMIC_ACTIONS_PER_BATCH_V1 {
                return Err(de::Error::custom(
                    EconomicActionBatchErrorV1::TooManyActions {
                        actual: declared,
                        maximum: MAX_ECONOMIC_ACTIONS_PER_BATCH_V1,
                    },
                ));
            }
            let mut actions = Vec::with_capacity(declared);
            while let Some(action) = sequence.next_element()? {
                if actions.len() == MAX_ECONOMIC_ACTIONS_PER_BATCH_V1 {
                    return Err(de::Error::custom(
                        EconomicActionBatchErrorV1::TooManyActions {
                            actual: MAX_ECONOMIC_ACTIONS_PER_BATCH_V1 + 1,
                            maximum: MAX_ECONOMIC_ACTIONS_PER_BATCH_V1,
                        },
                    ));
                }
                actions.push(action);
            }
            if actions.is_empty() {
                return Err(de::Error::custom(EconomicActionBatchErrorV1::EmptyActions));
            }
            Ok(actions)
        }
    }

    deserializer.deserialize_seq(ActionsVisitor)
}

fn require_input_size(size: usize) -> Result<(), EconomicActionBatchErrorV1> {
    if size == 0 {
        return Err(EconomicActionBatchErrorV1::EmptyInput);
    }
    if size > MAX_ECONOMIC_ACTION_BATCH_BYTES_V1 {
        return Err(EconomicActionBatchErrorV1::InputTooLarge {
            actual: size,
            maximum: MAX_ECONOMIC_ACTION_BATCH_BYTES_V1,
        });
    }
    Ok(())
}
