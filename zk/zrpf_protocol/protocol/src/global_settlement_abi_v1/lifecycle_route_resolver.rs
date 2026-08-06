use super::{
    EconomicCommandOccurrenceV1, EconomicLaneIdV1, GlobalEconomicStateErrorV1,
    LaneModuleReleaseIdV1, RegistryBoundGlobalEconomicStateV1, RouteDependencyLifecyclePurposeV1,
    RouteReleaseV1, ECONOMIC_LANE_COUNT_V1,
};

pub(super) type PinnedReleaseSetV1 = [Option<LaneModuleReleaseIdV1>; ECONOMIC_LANE_COUNT_V1];

pub(super) fn resolve_lifecycle_route_v1<'a>(
    occurrence: &EconomicCommandOccurrenceV1,
    profile_state: &'a RegistryBoundGlobalEconomicStateV1<'a>,
    pinned_releases: &PinnedReleaseSetV1,
) -> Result<&'a RouteReleaseV1, GlobalEconomicStateErrorV1> {
    let command_variant = occurrence
        .content()
        .authorized_action()
        .record()
        .action_type_id();
    let mut resolved = None;
    for route in profile_state.route_registry().routes() {
        if route.content().command_variant_root().as_bytes() != command_variant.as_bytes() {
            continue;
        }
        if !route_matches_lifecycle(route, profile_state, pinned_releases)? {
            continue;
        }
        if resolved.is_some() {
            return Err(GlobalEconomicStateErrorV1::AmbiguousLifecycleRoute);
        }
        resolved = Some(route);
    }
    resolved.ok_or(GlobalEconomicStateErrorV1::NoMatchingLifecycleRoute)
}

fn route_matches_lifecycle(
    route: &RouteReleaseV1,
    profile_state: &RegistryBoundGlobalEconomicStateV1<'_>,
    pinned_releases: &PinnedReleaseSetV1,
) -> Result<bool, GlobalEconomicStateErrorV1> {
    let mut covered_pin_lanes = [false; ECONOMIC_LANE_COUNT_V1];
    for dependency in route.content().dependencies() {
        let lane_position = usize::from(dependency.lane_id().code());
        let pinned_release = pinned_releases[lane_position];
        let matches = match dependency.lifecycle_purpose() {
            RouteDependencyLifecyclePurposeV1::ActiveNewRelease => {
                let registry = &profile_state.module_registries()[lane_position];
                let active = registry.resolve_new_object_release().map_err(|source| {
                    GlobalEconomicStateErrorV1::ActiveNewReleaseResolution {
                        lane_id: dependency.lane_id(),
                        source,
                    }
                })?;
                active.release_id() == dependency.module_release_id()
                    && pinned_release
                        .map(|release_id| release_id == dependency.module_release_id())
                        .unwrap_or(true)
            }
            RouteDependencyLifecyclePurposeV1::PinnedExistingObjects => {
                pinned_release == Some(dependency.module_release_id())
            }
        };
        if !matches {
            return Ok(false);
        }
        covered_pin_lanes[lane_position] = pinned_release.is_some();
    }
    Ok(EconomicLaneIdV1::ALL.into_iter().all(|lane_id| {
        let position = usize::from(lane_id.code());
        pinned_releases[position].is_none() || covered_pin_lanes[position]
    }))
}
