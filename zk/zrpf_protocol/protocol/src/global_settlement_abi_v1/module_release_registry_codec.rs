use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer,
};

use super::{
    EconomicLaneIdV1, LaneModuleReleaseRegistryErrorV1, LaneModuleReleaseRegistryV1,
    LaneModuleReleaseV1, MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1,
    MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1,
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LaneModuleReleaseRegistryWireV1 {
    registry_version: u16,
    lane_id: EconomicLaneIdV1,
    #[serde(deserialize_with = "deserialize_releases")]
    releases: Vec<LaneModuleReleaseV1>,
}

pub fn encode_lane_module_release_registry_v1(
    registry: &LaneModuleReleaseRegistryV1,
) -> Result<Vec<u8>, LaneModuleReleaseRegistryErrorV1> {
    registry.canonical_root()?;
    let bytes = postcard::to_allocvec(registry)
        .map_err(|_| LaneModuleReleaseRegistryErrorV1::PostcardEncode)?;
    require_bounded_nonempty(&bytes)?;
    Ok(bytes)
}

pub fn decode_exact_lane_module_release_registry_v1(
    bytes: &[u8],
) -> Result<LaneModuleReleaseRegistryV1, LaneModuleReleaseRegistryErrorV1> {
    require_bounded_nonempty(bytes)?;
    let (wire, remainder): (LaneModuleReleaseRegistryWireV1, &[u8]) =
        postcard::take_from_bytes(bytes)
            .map_err(|_| LaneModuleReleaseRegistryErrorV1::PostcardDecode)?;
    if !remainder.is_empty() {
        return Err(LaneModuleReleaseRegistryErrorV1::TrailingBytes);
    }
    let registry = LaneModuleReleaseRegistryV1::from_parts(
        wire.registry_version,
        wire.lane_id,
        wire.releases,
    )?;
    if encode_lane_module_release_registry_v1(&registry)?.as_slice() != bytes {
        return Err(LaneModuleReleaseRegistryErrorV1::NonCanonicalEncoding);
    }
    Ok(registry)
}

fn deserialize_releases<'de, D>(deserializer: D) -> Result<Vec<LaneModuleReleaseV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct ReleasesVisitor;

    impl<'de> Visitor<'de> for ReleasesVisitor {
        type Value = Vec<LaneModuleReleaseV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "one to {MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1} lane module releases"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1 {
                return Err(de::Error::custom("lane module release count exceeds bound"));
            }
            let mut releases = Vec::with_capacity(declared);
            while let Some(release) = sequence.next_element()? {
                if releases.len() == MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1 {
                    return Err(de::Error::custom("lane module release count exceeds bound"));
                }
                releases.push(release);
            }
            Ok(releases)
        }
    }

    deserializer.deserialize_seq(ReleasesVisitor)
}

fn require_bounded_nonempty(bytes: &[u8]) -> Result<(), LaneModuleReleaseRegistryErrorV1> {
    if bytes.is_empty() {
        return Err(LaneModuleReleaseRegistryErrorV1::EmptyInput);
    }
    if bytes.len() > MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1 {
        return Err(LaneModuleReleaseRegistryErrorV1::InputTooLarge {
            actual: bytes.len(),
            maximum: MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1,
        });
    }
    Ok(())
}
