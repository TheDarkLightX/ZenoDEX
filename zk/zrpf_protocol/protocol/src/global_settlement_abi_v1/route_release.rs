use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};

use super::{
    LaneModuleReleaseRegistryV1, RouteReleaseContentV1, RouteReleaseErrorV1, RouteReleaseIdV1,
    ROUTE_RELEASE_VERSION_V1,
};

const ROUTE_RELEASE_ID_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.route_release_id.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RouteReleaseV1 {
    route_release_version: u16,
    route_release_id: RouteReleaseIdV1,
    content: RouteReleaseContentV1,
}

impl RouteReleaseV1 {
    pub fn new(content: RouteReleaseContentV1) -> Result<Self, RouteReleaseErrorV1> {
        let route_release_id = derive_route_release_id(&content)?;
        Self::from_parts(ROUTE_RELEASE_VERSION_V1, route_release_id, content)
    }

    pub(super) fn from_parts(
        route_release_version: u16,
        route_release_id: RouteReleaseIdV1,
        content: RouteReleaseContentV1,
    ) -> Result<Self, RouteReleaseErrorV1> {
        if route_release_version != ROUTE_RELEASE_VERSION_V1 {
            return Err(RouteReleaseErrorV1::InvalidRouteReleaseVersion(
                route_release_version,
            ));
        }
        if derive_route_release_id(&content)? != route_release_id {
            return Err(RouteReleaseErrorV1::CounterfeitRouteReleaseId);
        }
        Ok(Self {
            route_release_version,
            route_release_id,
            content,
        })
    }

    pub const fn route_release_version(&self) -> u16 {
        self.route_release_version
    }

    pub const fn route_release_id(&self) -> RouteReleaseIdV1 {
        self.route_release_id
    }

    pub const fn content(&self) -> &RouteReleaseContentV1 {
        &self.content
    }

    pub fn bind_module_release_registries(
        &self,
        registries: &[LaneModuleReleaseRegistryV1],
    ) -> Result<(), RouteReleaseErrorV1> {
        let dependencies = self.content.dependencies();
        if registries.len() != dependencies.len() {
            return Err(RouteReleaseErrorV1::DependencyRegistryCountMismatch {
                actual: registries.len(),
                expected: dependencies.len(),
            });
        }
        for (position, (dependency, registry)) in dependencies.iter().zip(registries).enumerate() {
            if registry.lane_id() != dependency.lane_id() {
                return Err(RouteReleaseErrorV1::DependencyRegistryLaneMismatch {
                    position,
                    expected: dependency.lane_id(),
                    actual: registry.lane_id(),
                });
            }
            if registry
                .releases()
                .binary_search_by_key(
                    &dependency.module_release_id(),
                    super::LaneModuleReleaseV1::release_id,
                )
                .is_err()
            {
                return Err(RouteReleaseErrorV1::UnknownDependencyRelease {
                    position,
                    lane_id: dependency.lane_id(),
                    release_id: dependency.module_release_id(),
                });
            }
        }
        Ok(())
    }
}

impl<'de> Deserialize<'de> for RouteReleaseV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            route_release_version: u16,
            route_release_id: RouteReleaseIdV1,
            content: RouteReleaseContentV1,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::from_parts(
            wire.route_release_version,
            wire.route_release_id,
            wire.content,
        )
        .map_err(de::Error::custom)
    }
}

fn derive_route_release_id(
    content: &RouteReleaseContentV1,
) -> Result<RouteReleaseIdV1, RouteReleaseErrorV1> {
    let domain_len = u16::try_from(ROUTE_RELEASE_ID_DOMAIN_V1.len())
        .map_err(|_| RouteReleaseErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_len.to_be_bytes());
    hasher.update(ROUTE_RELEASE_ID_DOMAIN_V1);
    hasher.update(ROUTE_RELEASE_VERSION_V1.to_be_bytes());
    content.update_hasher(&mut hasher)?;
    RouteReleaseIdV1::new(hasher.finalize().into())
        .map_err(|_| RouteReleaseErrorV1::InvalidDerivedCommitment)
}
