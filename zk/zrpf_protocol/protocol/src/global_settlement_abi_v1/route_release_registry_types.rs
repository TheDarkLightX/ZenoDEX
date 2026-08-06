use alloc::vec::Vec;
use core::fmt;

use serde::{
    de::{self, SeqAccess, Visitor},
    Deserialize, Deserializer, Serialize,
};

use super::{
    EconomicLaneIdV1, LaneModuleReleaseIdV1, RouteReleaseRegistryErrorV1, RouteReleaseV1,
    MAX_ROUTE_DEPENDENCIES_V1, MAX_ROUTE_RELEASES_PER_REGISTRY_V1,
};
use crate::CommitmentV3;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RouteModuleReleaseSelectionV1 {
    lane_id: EconomicLaneIdV1,
    module_release_id: LaneModuleReleaseIdV1,
}

impl RouteModuleReleaseSelectionV1 {
    pub const fn new(lane_id: EconomicLaneIdV1, module_release_id: LaneModuleReleaseIdV1) -> Self {
        Self {
            lane_id,
            module_release_id,
        }
    }

    pub const fn lane_id(self) -> EconomicLaneIdV1 {
        self.lane_id
    }

    pub const fn module_release_id(self) -> LaneModuleReleaseIdV1 {
        self.module_release_id
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct RouteSelectionKeyV1 {
    command_variant_root: CommitmentV3,
    module_releases: Vec<RouteModuleReleaseSelectionV1>,
}

impl RouteSelectionKeyV1 {
    pub fn new(
        command_variant_root: CommitmentV3,
        module_releases: Vec<RouteModuleReleaseSelectionV1>,
    ) -> Result<Self, RouteReleaseRegistryErrorV1> {
        validate_module_release_selection(&module_releases)?;
        Ok(Self {
            command_variant_root,
            module_releases,
        })
    }

    pub fn from_route(route: &RouteReleaseV1) -> Self {
        let mut module_releases: Vec<_> = route
            .content()
            .dependencies()
            .iter()
            .map(|dependency| {
                RouteModuleReleaseSelectionV1::new(
                    dependency.lane_id(),
                    dependency.module_release_id(),
                )
            })
            .collect();
        module_releases.sort_by_key(|selection| selection.lane_id());
        Self {
            command_variant_root: route.content().command_variant_root(),
            module_releases,
        }
    }

    pub const fn command_variant_root(&self) -> CommitmentV3 {
        self.command_variant_root
    }

    pub fn module_releases(&self) -> &[RouteModuleReleaseSelectionV1] {
        &self.module_releases
    }
}

impl<'de> Deserialize<'de> for RouteSelectionKeyV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            command_variant_root: CommitmentV3,
            #[serde(deserialize_with = "deserialize_module_release_selections")]
            module_releases: Vec<RouteModuleReleaseSelectionV1>,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::new(wire.command_variant_root, wire.module_releases).map_err(de::Error::custom)
    }
}

pub(super) fn deserialize_route_releases<'de, D>(
    deserializer: D,
) -> Result<Vec<RouteReleaseV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct RoutesVisitor;

    impl<'de> Visitor<'de> for RoutesVisitor {
        type Value = Vec<RouteReleaseV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "one to {MAX_ROUTE_RELEASES_PER_REGISTRY_V1} route releases"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_ROUTE_RELEASES_PER_REGISTRY_V1 {
                return Err(de::Error::custom("route release count exceeds bound"));
            }
            let mut routes = Vec::with_capacity(declared);
            while let Some(route) = sequence.next_element()? {
                if routes.len() == MAX_ROUTE_RELEASES_PER_REGISTRY_V1 {
                    return Err(de::Error::custom("route release count exceeds bound"));
                }
                routes.push(route);
            }
            Ok(routes)
        }
    }

    deserializer.deserialize_seq(RoutesVisitor)
}

fn deserialize_module_release_selections<'de, D>(
    deserializer: D,
) -> Result<Vec<RouteModuleReleaseSelectionV1>, D::Error>
where
    D: Deserializer<'de>,
{
    struct SelectionsVisitor;

    impl<'de> Visitor<'de> for SelectionsVisitor {
        type Value = Vec<RouteModuleReleaseSelectionV1>;

        fn expecting(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(
                formatter,
                "one to {MAX_ROUTE_DEPENDENCIES_V1} module release selections"
            )
        }

        fn visit_seq<A>(self, mut sequence: A) -> Result<Self::Value, A::Error>
        where
            A: SeqAccess<'de>,
        {
            let declared = sequence.size_hint().unwrap_or(0);
            if declared > MAX_ROUTE_DEPENDENCIES_V1 {
                return Err(de::Error::custom(
                    "module release selection count exceeds bound",
                ));
            }
            let mut selections = Vec::with_capacity(declared);
            while let Some(selection) = sequence.next_element()? {
                if selections.len() == MAX_ROUTE_DEPENDENCIES_V1 {
                    return Err(de::Error::custom(
                        "module release selection count exceeds bound",
                    ));
                }
                selections.push(selection);
            }
            Ok(selections)
        }
    }

    deserializer.deserialize_seq(SelectionsVisitor)
}

fn validate_module_release_selection(
    module_releases: &[RouteModuleReleaseSelectionV1],
) -> Result<(), RouteReleaseRegistryErrorV1> {
    if module_releases.is_empty() {
        return Err(RouteReleaseRegistryErrorV1::EmptySelectionDependencies);
    }
    if module_releases.len() > MAX_ROUTE_DEPENDENCIES_V1 {
        return Err(RouteReleaseRegistryErrorV1::TooManySelectionDependencies {
            actual: module_releases.len(),
            maximum: MAX_ROUTE_DEPENDENCIES_V1,
        });
    }
    for position in 1..module_releases.len() {
        let previous = module_releases[position - 1];
        let current = module_releases[position];
        if previous.lane_id() == current.lane_id() {
            return Err(RouteReleaseRegistryErrorV1::DuplicateSelectionLane(
                current.lane_id(),
            ));
        }
        if previous.lane_id() > current.lane_id() {
            return Err(RouteReleaseRegistryErrorV1::NonCanonicalSelectionLaneOrder { position });
        }
    }
    Ok(())
}
