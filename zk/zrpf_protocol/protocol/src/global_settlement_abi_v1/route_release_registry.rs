use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};

use super::route_release_registry_types::deserialize_route_releases;
use super::{
    EconomicLaneIdV1, LaneModuleReleaseRegistryV1, RouteReleaseRegistryErrorV1, RouteReleaseV1,
    RouteSelectionKeyV1, MAX_ROUTE_RELEASES_PER_REGISTRY_V1, ROUTE_RELEASE_REGISTRY_VERSION_V1,
};
use crate::CommitmentV3;

const REGISTRY_ROOT_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.route_release_registry.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RouteReleaseRegistryV1 {
    registry_version: u16,
    routes: Vec<RouteReleaseV1>,
}

impl RouteReleaseRegistryV1 {
    pub fn new(routes: Vec<RouteReleaseV1>) -> Result<Self, RouteReleaseRegistryErrorV1> {
        Self::from_parts(ROUTE_RELEASE_REGISTRY_VERSION_V1, routes)
    }

    pub(super) fn from_parts(
        registry_version: u16,
        routes: Vec<RouteReleaseV1>,
    ) -> Result<Self, RouteReleaseRegistryErrorV1> {
        if registry_version != ROUTE_RELEASE_REGISTRY_VERSION_V1 {
            return Err(RouteReleaseRegistryErrorV1::InvalidRegistryVersion(
                registry_version,
            ));
        }
        validate_route_set(&routes)?;
        Ok(Self {
            registry_version,
            routes,
        })
    }

    pub const fn registry_version(&self) -> u16 {
        self.registry_version
    }

    pub fn routes(&self) -> &[RouteReleaseV1] {
        &self.routes
    }

    pub fn resolve(
        &self,
        selection: &RouteSelectionKeyV1,
    ) -> Result<&RouteReleaseV1, RouteReleaseRegistryErrorV1> {
        let position = self
            .routes
            .binary_search_by(|route| RouteSelectionKeyV1::from_route(route).cmp(selection))
            .map_err(|_| RouteReleaseRegistryErrorV1::UnknownRouteSelection)?;
        Ok(&self.routes[position])
    }

    pub fn canonical_root(&self) -> Result<CommitmentV3, RouteReleaseRegistryErrorV1> {
        validate_route_set(&self.routes)?;
        let domain_len = u16::try_from(REGISTRY_ROOT_DOMAIN_V1.len())
            .map_err(|_| RouteReleaseRegistryErrorV1::ArithmeticOverflow("hash_domain_length"))?;
        let count = u16::try_from(self.routes.len())
            .map_err(|_| RouteReleaseRegistryErrorV1::ArithmeticOverflow("route_count"))?;
        let mut hasher = Sha256::new();
        hasher.update(domain_len.to_be_bytes());
        hasher.update(REGISTRY_ROOT_DOMAIN_V1);
        hasher.update(self.registry_version.to_be_bytes());
        hasher.update(count.to_be_bytes());
        for route in &self.routes {
            hasher.update(route.route_release_id().as_bytes());
        }
        CommitmentV3::new(hasher.finalize().into())
            .map_err(|_| RouteReleaseRegistryErrorV1::InvalidDerivedCommitment)
    }

    pub fn bind_module_release_registries(
        &self,
        registries: &[LaneModuleReleaseRegistryV1],
    ) -> Result<(), RouteReleaseRegistryErrorV1> {
        let required_lanes = self.required_lanes();
        if registries.len() != required_lanes.len() {
            return Err(RouteReleaseRegistryErrorV1::ModuleRegistryCountMismatch {
                actual: registries.len(),
                expected: required_lanes.len(),
            });
        }
        for (position, (expected, registry)) in
            required_lanes.iter().copied().zip(registries).enumerate()
        {
            if registry.lane_id() != expected {
                return Err(RouteReleaseRegistryErrorV1::ModuleRegistryLaneMismatch {
                    position,
                    expected,
                    actual: registry.lane_id(),
                });
            }
        }
        for route in &self.routes {
            for dependency in route.content().dependencies() {
                let position = required_lanes
                    .binary_search(&dependency.lane_id())
                    .map_err(|_| {
                        RouteReleaseRegistryErrorV1::MissingRequiredModuleRegistry(
                            dependency.lane_id(),
                        )
                    })?;
                let registry = &registries[position];
                if registry
                    .releases()
                    .binary_search_by_key(
                        &dependency.module_release_id(),
                        super::LaneModuleReleaseV1::release_id,
                    )
                    .is_err()
                {
                    return Err(RouteReleaseRegistryErrorV1::UnknownDependencyRelease {
                        route_id: route.route_release_id(),
                        lane_id: dependency.lane_id(),
                        release_id: dependency.module_release_id(),
                    });
                }
            }
        }
        Ok(())
    }

    fn required_lanes(&self) -> Vec<EconomicLaneIdV1> {
        let mut lanes: Vec<_> = self
            .routes
            .iter()
            .flat_map(|route| route.content().dependencies())
            .map(|dependency| dependency.lane_id())
            .collect();
        lanes.sort_unstable();
        lanes.dedup();
        lanes
    }
}

impl<'de> Deserialize<'de> for RouteReleaseRegistryV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            registry_version: u16,
            #[serde(deserialize_with = "deserialize_route_releases")]
            routes: Vec<RouteReleaseV1>,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::from_parts(wire.registry_version, wire.routes).map_err(de::Error::custom)
    }
}

fn validate_route_set(routes: &[RouteReleaseV1]) -> Result<(), RouteReleaseRegistryErrorV1> {
    if routes.is_empty() {
        return Err(RouteReleaseRegistryErrorV1::EmptyRegistry);
    }
    if routes.len() > MAX_ROUTE_RELEASES_PER_REGISTRY_V1 {
        return Err(RouteReleaseRegistryErrorV1::TooManyRoutes {
            actual: routes.len(),
            maximum: MAX_ROUTE_RELEASES_PER_REGISTRY_V1,
        });
    }
    for (position, route) in routes.iter().enumerate() {
        if routes[..position]
            .iter()
            .any(|earlier| earlier.route_release_id() == route.route_release_id())
        {
            return Err(RouteReleaseRegistryErrorV1::DuplicateRouteReleaseId(
                route.route_release_id(),
            ));
        }
        let selection = RouteSelectionKeyV1::from_route(route);
        if routes[..position]
            .iter()
            .any(|earlier| RouteSelectionKeyV1::from_route(earlier) == selection)
        {
            return Err(RouteReleaseRegistryErrorV1::AmbiguousRouteSelection);
        }
        if position > 0 && RouteSelectionKeyV1::from_route(&routes[position - 1]) > selection {
            return Err(RouteReleaseRegistryErrorV1::NonCanonicalRouteOrder { position });
        }
    }
    Ok(())
}
