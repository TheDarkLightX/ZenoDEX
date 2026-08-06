use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer,
};

use super::{
    EconomicLaneRegistryEntryV1, GlobalEconomicLaneRegistryV1, GlobalSettlementAbiErrorV1,
    ECONOMIC_LANE_COUNT_V1, MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1,
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct GlobalEconomicLaneRegistryWireV1 {
    registry_version: u16,
    #[serde(deserialize_with = "deserialize_entries")]
    entries: Vec<EconomicLaneRegistryEntryV1>,
}

pub fn encode_global_economic_lane_registry_v1(
    registry: &GlobalEconomicLaneRegistryV1,
) -> Result<Vec<u8>, GlobalSettlementAbiErrorV1> {
    registry.canonical_commitment()?;
    let bytes =
        postcard::to_allocvec(registry).map_err(|_| GlobalSettlementAbiErrorV1::PostcardDecode)?;
    if bytes.len() > MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1 {
        return Err(GlobalSettlementAbiErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1,
        });
    }
    Ok(bytes)
}

pub fn decode_exact_global_economic_lane_registry_v1(
    bytes: &[u8],
) -> Result<GlobalEconomicLaneRegistryV1, GlobalSettlementAbiErrorV1> {
    require_bounded_input(bytes)?;
    let (wire, remainder): (GlobalEconomicLaneRegistryWireV1, &[u8]) =
        postcard::take_from_bytes(bytes).map_err(|_| GlobalSettlementAbiErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(GlobalSettlementAbiErrorV1::TrailingBytes);
    }
    let registry = GlobalEconomicLaneRegistryV1::from_parts(wire.registry_version, wire.entries)?;
    if encode_global_economic_lane_registry_v1(&registry)?.as_slice() != bytes {
        return Err(GlobalSettlementAbiErrorV1::NonCanonicalEncoding);
    }
    Ok(registry)
}

fn deserialize_entries<'de, D>(
    deserializer: D,
) -> Result<Vec<EconomicLaneRegistryEntryV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct EntriesVisitor;

    impl<'de> Visitor<'de> for EntriesVisitor {
        type Value = Vec<EconomicLaneRegistryEntryV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "exactly {ECONOMIC_LANE_COUNT_V1} economic lane entries"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > ECONOMIC_LANE_COUNT_V1 {
                return Err(de::Error::custom("economic lane entry count exceeds bound"));
            }
            let mut entries = Vec::with_capacity(declared);
            while let Some(entry) = sequence.next_element()? {
                if entries.len() == ECONOMIC_LANE_COUNT_V1 {
                    return Err(de::Error::custom("economic lane entry count exceeds bound"));
                }
                entries.push(entry);
            }
            Ok(entries)
        }
    }

    deserializer.deserialize_seq(EntriesVisitor)
}

fn require_bounded_input(bytes: &[u8]) -> Result<(), GlobalSettlementAbiErrorV1> {
    if bytes.is_empty() {
        return Err(GlobalSettlementAbiErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1 {
        return Err(GlobalSettlementAbiErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1,
        });
    }
    Ok(())
}
