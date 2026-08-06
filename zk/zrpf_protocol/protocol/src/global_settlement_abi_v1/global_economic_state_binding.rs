use super::{
    EconomicCommandOccurrenceV1, EconomicObjectReleasePinProofV1, EconomicProfileSnapshotV1,
    GlobalEconomicLaneRegistryV1, GlobalEconomicStateErrorV1, GlobalEconomicStateV1,
    LaneModuleReleaseRegistryV1, ProfileBoundEconomicCommandOccurrenceV1, RouteReleaseRegistryV1,
    ECONOMIC_LANE_COUNT_V1,
};
use crate::CommitmentV3;

use super::lifecycle_route_resolver::{resolve_lifecycle_route_v1, PinnedReleaseSetV1};

/// A structurally validated global state bound to one exact profile registry view.
///
/// This witness has private fields and no serialization implementation. It is
/// evidence of deterministic in-memory checks only; it is not a receipt,
/// current-head witness, or settlement capability.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::RegistryBoundGlobalEconomicStateV1;
/// let state = unimplemented!();
/// let profile = unimplemented!();
/// let lane_registry = unimplemented!();
/// let module_registries = unimplemented!();
/// let route_registry = unimplemented!();
/// let _ = RegistryBoundGlobalEconomicStateV1 {
///     state,
///     profile,
///     lane_registry,
///     module_registries,
///     route_registry,
/// };
/// ```
///
/// ```compile_fail
/// use serde::Serialize;
/// use zenodex_zrpf_protocol_v3::RegistryBoundGlobalEconomicStateV1;
/// fn require_serializable<T: Serialize>(_: &T) {}
/// let witness: RegistryBoundGlobalEconomicStateV1<'_> = unimplemented!();
/// require_serializable(&witness);
/// ```
#[must_use]
pub struct RegistryBoundGlobalEconomicStateV1<'a> {
    state: &'a GlobalEconomicStateV1,
    profile: &'a EconomicProfileSnapshotV1,
    lane_registry: &'a GlobalEconomicLaneRegistryV1,
    module_registries: &'a [LaneModuleReleaseRegistryV1],
    route_registry: &'a RouteReleaseRegistryV1,
}

impl<'a> RegistryBoundGlobalEconomicStateV1<'a> {
    pub const fn state(&self) -> &'a GlobalEconomicStateV1 {
        self.state
    }

    pub const fn profile(&self) -> &'a EconomicProfileSnapshotV1 {
        self.profile
    }

    pub const fn lane_registry(&self) -> &'a GlobalEconomicLaneRegistryV1 {
        self.lane_registry
    }

    pub const fn module_registries(&self) -> &'a [LaneModuleReleaseRegistryV1] {
        self.module_registries
    }

    pub const fn route_registry(&self) -> &'a RouteReleaseRegistryV1 {
        self.route_registry
    }
}

pub fn bind_global_economic_state_to_profile_v1<'a>(
    state: &'a GlobalEconomicStateV1,
    profile: &'a EconomicProfileSnapshotV1,
    lane_registry: &'a GlobalEconomicLaneRegistryV1,
    module_registries: &'a [LaneModuleReleaseRegistryV1],
    route_registry: &'a RouteReleaseRegistryV1,
) -> Result<RegistryBoundGlobalEconomicStateV1<'a>, GlobalEconomicStateErrorV1> {
    state.validate_self_consistency()?;
    if state.content().profile_id() != profile.profile_id() {
        return Err(GlobalEconomicStateErrorV1::ProfileMismatch);
    }
    if state.content().writer_epoch() != profile.content().writer_epoch() {
        return Err(GlobalEconomicStateErrorV1::WriterEpochMismatch);
    }
    profile
        .bind_economic_registries(lane_registry, module_registries, route_registry)
        .map_err(GlobalEconomicStateErrorV1::EconomicProfileBinding)?;
    Ok(RegistryBoundGlobalEconomicStateV1 {
        state,
        profile,
        lane_registry,
        module_registries,
        route_registry,
    })
}

/// A command occurrence bound to one exact global pre-state and every consumed
/// object's state-root-authenticated creating release.
///
/// The witness cannot be constructed or serialized by callers. Its route is
/// independently derived from governed lifecycle purposes and exact
/// state-authenticated release pins. It still has no proof receipt,
/// current-head authority, or publication capability.
///
/// ```compile_fail
/// use zenodex_zrpf_protocol_v3::StateBoundEconomicCommandOccurrenceV1;
/// let profile_occurrence = unimplemented!();
/// let profile_state = unimplemented!();
/// let object_release_pin_proofs = unimplemented!();
/// let _ = StateBoundEconomicCommandOccurrenceV1 {
///     profile_occurrence,
///     profile_state,
///     object_release_pin_proofs,
/// };
/// ```
///
/// ```compile_fail
/// use serde::Serialize;
/// use zenodex_zrpf_protocol_v3::StateBoundEconomicCommandOccurrenceV1;
/// fn require_serializable<T: Serialize>(_: &T) {}
/// let witness: StateBoundEconomicCommandOccurrenceV1<'_> = unimplemented!();
/// require_serializable(&witness);
/// ```
#[must_use]
pub struct StateBoundEconomicCommandOccurrenceV1<'a> {
    profile_occurrence: ProfileBoundEconomicCommandOccurrenceV1<'a>,
    profile_state: RegistryBoundGlobalEconomicStateV1<'a>,
    object_release_pin_proofs: &'a [EconomicObjectReleasePinProofV1],
}

impl<'a> StateBoundEconomicCommandOccurrenceV1<'a> {
    pub const fn profile_bound_occurrence(&self) -> &ProfileBoundEconomicCommandOccurrenceV1<'a> {
        &self.profile_occurrence
    }

    pub const fn global_state(&self) -> &'a GlobalEconomicStateV1 {
        self.profile_state.state
    }

    pub const fn profile_state(&self) -> &RegistryBoundGlobalEconomicStateV1<'a> {
        &self.profile_state
    }

    pub const fn object_release_pin_proofs(&self) -> &'a [EconomicObjectReleasePinProofV1] {
        self.object_release_pin_proofs
    }
}

pub fn bind_profile_bound_occurrence_to_global_state_v1<'a>(
    profile_occurrence: ProfileBoundEconomicCommandOccurrenceV1<'a>,
    profile_state: RegistryBoundGlobalEconomicStateV1<'a>,
    object_release_pin_proofs: &'a [EconomicObjectReleasePinProofV1],
) -> Result<StateBoundEconomicCommandOccurrenceV1<'a>, GlobalEconomicStateErrorV1> {
    let pinned_releases = validate_occurrence_state_binding(
        profile_occurrence.occurrence(),
        &profile_state,
        object_release_pin_proofs,
    )?;
    let resolved_route = resolve_lifecycle_route_v1(
        profile_occurrence.occurrence(),
        &profile_state,
        &pinned_releases,
    )?;
    let proposed_route_id = profile_occurrence.route_release().route_release_id();
    let resolved_route_id = resolved_route.route_release_id();
    if proposed_route_id != resolved_route_id {
        return Err(GlobalEconomicStateErrorV1::ProposedRouteMismatch {
            expected: resolved_route_id,
            actual: proposed_route_id,
        });
    }
    Ok(StateBoundEconomicCommandOccurrenceV1 {
        profile_occurrence,
        profile_state,
        object_release_pin_proofs,
    })
}

fn validate_occurrence_state_binding(
    occurrence: &EconomicCommandOccurrenceV1,
    profile_state: &RegistryBoundGlobalEconomicStateV1<'_>,
    object_release_pin_proofs: &[EconomicObjectReleasePinProofV1],
) -> Result<PinnedReleaseSetV1, GlobalEconomicStateErrorV1> {
    let occurrence_content = occurrence.content();
    let state = profile_state.state();
    let state_content = state.content();
    if occurrence_content.profile_id() != state_content.profile_id() {
        return Err(GlobalEconomicStateErrorV1::OccurrenceProfileMismatch);
    }
    if occurrence_content.writer_epoch() != state_content.writer_epoch() {
        return Err(GlobalEconomicStateErrorV1::OccurrenceWriterEpochMismatch);
    }
    let record = occurrence_content.authorized_action().record();
    if record.application_id() != state_content.application_id() {
        return Err(GlobalEconomicStateErrorV1::ApplicationMismatch);
    }
    if record.chain_or_domain_id() != state_content.chain_or_domain_id() {
        return Err(GlobalEconomicStateErrorV1::ChainOrDomainMismatch);
    }
    if record.pre_state_root().as_bytes() != state.state_root().as_bytes() {
        return Err(GlobalEconomicStateErrorV1::PreStateRootMismatch);
    }
    let consumed_objects = record.consumed_object_ids();
    if object_release_pin_proofs.len() != consumed_objects.len() {
        return Err(GlobalEconomicStateErrorV1::ObjectPinProofCountMismatch {
            actual: object_release_pin_proofs.len(),
            expected: consumed_objects.len(),
        });
    }
    let expected_registry_root = state_content
        .partition_roots()
        .object_release_registry_root();
    validate_object_release_pins(
        profile_state.module_registries(),
        consumed_objects,
        object_release_pin_proofs,
        expected_registry_root,
    )
}

fn validate_object_release_pins(
    module_registries: &[LaneModuleReleaseRegistryV1],
    consumed_objects: &[CommitmentV3],
    object_release_pin_proofs: &[EconomicObjectReleasePinProofV1],
    expected_registry_root: CommitmentV3,
) -> Result<PinnedReleaseSetV1, GlobalEconomicStateErrorV1> {
    let mut pinned_releases = [None; ECONOMIC_LANE_COUNT_V1];
    for (position, (object_id, proof)) in consumed_objects
        .iter()
        .zip(object_release_pin_proofs)
        .enumerate()
    {
        let pin = proof.pin();
        if pin.object_id() != *object_id {
            return Err(GlobalEconomicStateErrorV1::ObjectPinObjectMismatch { position });
        }
        if proof.derive_registry_root()? != expected_registry_root {
            return Err(GlobalEconomicStateErrorV1::ObjectPinRegistryRootMismatch { position });
        }
        let registry = &module_registries[usize::from(pin.lane_id().code())];
        let release = registry
            .releases()
            .binary_search_by_key(
                &pin.creating_release_id(),
                super::LaneModuleReleaseV1::release_id,
            )
            .ok()
            .map(|release_position| &registry.releases()[release_position])
            .ok_or(GlobalEconomicStateErrorV1::UnknownCreatingRelease {
                lane_id: pin.lane_id(),
                release_id: pin.creating_release_id(),
            })?;
        release
            .admit_existing_object_transition()
            .map_err(
                |source| GlobalEconomicStateErrorV1::CreatingReleaseAdmission {
                    lane_id: pin.lane_id(),
                    source,
                },
            )?;
        let lane_position = usize::from(pin.lane_id().code());
        match pinned_releases[lane_position] {
            Some(existing) if existing != pin.creating_release_id() => {
                return Err(GlobalEconomicStateErrorV1::ConflictingPinnedReleases(
                    pin.lane_id(),
                ));
            }
            Some(_) => {}
            None => pinned_releases[lane_position] = Some(pin.creating_release_id()),
        }
    }
    Ok(pinned_releases)
}
