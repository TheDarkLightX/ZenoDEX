use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::{Digest, Sha256};

use super::{
    EconomicLaneCommandStatusV1, EconomicLaneIdV1, EconomicProfileIdV1,
    EconomicProfileSnapshotContentV1, EconomicProfileSnapshotErrorV1,
    EconomicProfileTransitionModeV1, GlobalEconomicLaneRegistryV1, LaneModuleReleaseRegistryV1,
    RouteDependencyRoleV1, RouteReleaseRegistryV1, ECONOMIC_LANE_COUNT_V1,
    ECONOMIC_PROFILE_SNAPSHOT_VERSION_V1,
};

const PROFILE_ID_DOMAIN_V1: &[u8] = b"zenodex.global_settlement.economic_profile_snapshot_id.v1";

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct EconomicProfileSnapshotV1 {
    profile_version: u16,
    profile_id: EconomicProfileIdV1,
    content: EconomicProfileSnapshotContentV1,
}

impl EconomicProfileSnapshotV1 {
    pub fn new(
        content: EconomicProfileSnapshotContentV1,
    ) -> Result<Self, EconomicProfileSnapshotErrorV1> {
        let profile_id = derive_profile_id(&content)?;
        Self::from_parts(ECONOMIC_PROFILE_SNAPSHOT_VERSION_V1, profile_id, content)
    }

    pub(super) fn from_parts(
        profile_version: u16,
        profile_id: EconomicProfileIdV1,
        content: EconomicProfileSnapshotContentV1,
    ) -> Result<Self, EconomicProfileSnapshotErrorV1> {
        if profile_version != ECONOMIC_PROFILE_SNAPSHOT_VERSION_V1 {
            return Err(EconomicProfileSnapshotErrorV1::InvalidProfileVersion(
                profile_version,
            ));
        }
        if derive_profile_id(&content)? != profile_id {
            return Err(EconomicProfileSnapshotErrorV1::CounterfeitProfileId);
        }
        Ok(Self {
            profile_version,
            profile_id,
            content,
        })
    }

    pub const fn profile_version(&self) -> u16 {
        self.profile_version
    }

    pub const fn profile_id(&self) -> EconomicProfileIdV1 {
        self.profile_id
    }

    pub const fn content(&self) -> &EconomicProfileSnapshotContentV1 {
        &self.content
    }

    pub fn validate_successor_of(
        &self,
        previous: &Self,
    ) -> Result<(), EconomicProfileSnapshotErrorV1> {
        if self.content.transition_mode() == EconomicProfileTransitionModeV1::Genesis {
            return Err(EconomicProfileSnapshotErrorV1::GenesisCannotBeSuccessor);
        }
        if self.content.predecessor_profile_id() != Some(previous.profile_id) {
            return Err(EconomicProfileSnapshotErrorV1::PredecessorProfileMismatch);
        }
        if self.content.authority_epoch() <= previous.content.authority_epoch() {
            return Err(EconomicProfileSnapshotErrorV1::AuthorityEpochNotIncreasing);
        }
        if self.content.writer_epoch() <= previous.content.writer_epoch() {
            return Err(EconomicProfileSnapshotErrorV1::WriterEpochNotRotated);
        }
        Ok(())
    }

    pub fn bind_economic_registries(
        &self,
        lane_registry: &GlobalEconomicLaneRegistryV1,
        module_registries: &[LaneModuleReleaseRegistryV1],
        route_registry: &RouteReleaseRegistryV1,
    ) -> Result<(), EconomicProfileSnapshotErrorV1> {
        self.bind_registry_roots(lane_registry, route_registry)?;
        bind_module_registries(lane_registry, module_registries)?;
        bind_route_dependencies(module_registries, route_registry)?;
        validate_primary_route_coverage(lane_registry, route_registry)
    }

    fn bind_registry_roots(
        &self,
        lane_registry: &GlobalEconomicLaneRegistryV1,
        route_registry: &RouteReleaseRegistryV1,
    ) -> Result<(), EconomicProfileSnapshotErrorV1> {
        let roots = self.content.registry_roots();
        let lane_root = lane_registry
            .canonical_commitment()
            .map_err(EconomicProfileSnapshotErrorV1::EconomicLaneRegistryInvalid)?;
        if roots.economic_lane_registry_root() != lane_root {
            return Err(EconomicProfileSnapshotErrorV1::EconomicLaneRegistryRootMismatch);
        }
        let route_root = route_registry
            .canonical_root()
            .map_err(EconomicProfileSnapshotErrorV1::RouteReleaseRegistryInvalid)?;
        if roots.route_release_registry_root() != route_root {
            return Err(EconomicProfileSnapshotErrorV1::RouteReleaseRegistryRootMismatch);
        }
        Ok(())
    }
}

impl<'de> Deserialize<'de> for EconomicProfileSnapshotV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        #[derive(Deserialize)]
        #[serde(deny_unknown_fields)]
        struct Wire {
            profile_version: u16,
            profile_id: EconomicProfileIdV1,
            content: EconomicProfileSnapshotContentV1,
        }

        let wire = Wire::deserialize(deserializer)?;
        Self::from_parts(wire.profile_version, wire.profile_id, wire.content)
            .map_err(de::Error::custom)
    }
}

fn bind_module_registries(
    lane_registry: &GlobalEconomicLaneRegistryV1,
    module_registries: &[LaneModuleReleaseRegistryV1],
) -> Result<(), EconomicProfileSnapshotErrorV1> {
    if module_registries.len() != ECONOMIC_LANE_COUNT_V1 {
        return Err(EconomicProfileSnapshotErrorV1::WrongModuleRegistryCount {
            actual: module_registries.len(),
            expected: ECONOMIC_LANE_COUNT_V1,
        });
    }
    for (position, ((registry, entry), expected)) in module_registries
        .iter()
        .zip(lane_registry.entries())
        .zip(EconomicLaneIdV1::ALL)
        .enumerate()
    {
        if registry.lane_id() != expected {
            return Err(EconomicProfileSnapshotErrorV1::ModuleRegistryLaneMismatch {
                position,
                expected,
                actual: registry.lane_id(),
            });
        }
        registry.bind_global_lane_entry(entry).map_err(|source| {
            EconomicProfileSnapshotErrorV1::ModuleRegistryBinding {
                lane_id: expected,
                source,
            }
        })?;
    }
    Ok(())
}

fn bind_route_dependencies(
    module_registries: &[LaneModuleReleaseRegistryV1],
    route_registry: &RouteReleaseRegistryV1,
) -> Result<(), EconomicProfileSnapshotErrorV1> {
    for route in route_registry.routes() {
        for dependency in route.content().dependencies() {
            let registry = module_registries
                .get(usize::from(dependency.lane_id().code()))
                .ok_or(EconomicProfileSnapshotErrorV1::InvalidDerivedCommitment)?;
            let release = registry
                .releases()
                .binary_search_by_key(
                    &dependency.module_release_id(),
                    super::LaneModuleReleaseV1::release_id,
                )
                .ok()
                .map(|position| &registry.releases()[position])
                .ok_or(EconomicProfileSnapshotErrorV1::UnknownDependencyRelease {
                    route_id: route.route_release_id(),
                    lane_id: dependency.lane_id(),
                    release_id: dependency.module_release_id(),
                })?;
            release
                .admit_existing_object_transition()
                .map_err(
                    |source| EconomicProfileSnapshotErrorV1::DependencyReleaseAdmission {
                        route_id: route.route_release_id(),
                        lane_id: dependency.lane_id(),
                        source,
                    },
                )?;
        }
    }
    Ok(())
}

fn validate_primary_route_coverage(
    lane_registry: &GlobalEconomicLaneRegistryV1,
    route_registry: &RouteReleaseRegistryV1,
) -> Result<(), EconomicProfileSnapshotErrorV1> {
    let mut primary_counts = [0u16; ECONOMIC_LANE_COUNT_V1];
    for route in route_registry.routes() {
        let primary = route
            .content()
            .dependencies()
            .iter()
            .find(|dependency| dependency.roles().contains(RouteDependencyRoleV1::Primary))
            .ok_or(EconomicProfileSnapshotErrorV1::InvalidDerivedCommitment)?;
        let count = primary_counts
            .get_mut(usize::from(primary.lane_id().code()))
            .ok_or(EconomicProfileSnapshotErrorV1::InvalidDerivedCommitment)?;
        *count = count
            .checked_add(1)
            .ok_or(EconomicProfileSnapshotErrorV1::ArithmeticOverflow(
                "primary_route_count",
            ))?;
    }
    for entry in lane_registry.entries() {
        let count = *primary_counts
            .get(usize::from(entry.lane_id().code()))
            .ok_or(EconomicProfileSnapshotErrorV1::InvalidDerivedCommitment)?;
        match (entry.command_status(), count) {
            (EconomicLaneCommandStatusV1::Enabled, 0) => {
                return Err(
                    EconomicProfileSnapshotErrorV1::EnabledLaneHasNoPrimaryRoute(entry.lane_id()),
                );
            }
            (EconomicLaneCommandStatusV1::Disabled, 1..) => {
                return Err(EconomicProfileSnapshotErrorV1::DisabledLaneHasPrimaryRoute(
                    entry.lane_id(),
                ));
            }
            _ => {}
        }
    }
    Ok(())
}

fn derive_profile_id(
    content: &EconomicProfileSnapshotContentV1,
) -> Result<EconomicProfileIdV1, EconomicProfileSnapshotErrorV1> {
    let domain_len = u16::try_from(PROFILE_ID_DOMAIN_V1.len())
        .map_err(|_| EconomicProfileSnapshotErrorV1::ArithmeticOverflow("hash_domain_length"))?;
    let mut hasher = Sha256::new();
    hasher.update(domain_len.to_be_bytes());
    hasher.update(PROFILE_ID_DOMAIN_V1);
    hasher.update(ECONOMIC_PROFILE_SNAPSHOT_VERSION_V1.to_be_bytes());
    content.update_hasher(&mut hasher);
    EconomicProfileIdV1::new(hasher.finalize().into())
        .map_err(|_| EconomicProfileSnapshotErrorV1::InvalidDerivedCommitment)
}
