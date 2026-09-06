//! One governed custody-complete asset-transfer route as ordinary data.
//!
//! Preparing a route validates the exact governed profile, registries, policy
//! registry, occurrence, and coordinator context, requires the reviewed custody
//! semantic bundle root on the selected module, coordinator, and route, and
//! then reuses the custody coordinator preflight plus the existing exact global
//! allocation, route projection, and global effect refinement checks. The wire
//! layout, closed parser, canonical encoding, and byte ceiling are those of the
//! legacy route input; the successor is selected only by specification roots.
//! Nothing here verifies a receipt, names a guest method, pins an image,
//! qualifies or activates a release, or mounts a publisher. A prepared value is
//! ordinary data plus expected image metadata copied from the selected
//! releases; it is not a receipt, image identity, or release approval.

use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_asset_lane_custody_coordinator_risc0_shared::{
    prepare_asset_lane_custody_coordinator_v1, AssetLaneCustodyCoordinatorGuestErrorV1,
    AssetLaneCustodyCoordinatorInputV1, PreparedAssetLaneCustodyCoordinatorV1,
};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, check_asset_transfer_global_allocation_v1, project_route_global_state_v1,
    refine_route_global_economic_state_effects_v1, require_asset_transfer_custody_semantics_v1,
    require_asset_transfer_policy_membership_v1,
    require_governed_asset_transfer_policy_registry_v1, AbiErrorV1,
    AssetTransferGlobalAllocationCandidateV1, AssetTransferPolicyRegistryV1,
    EconomicCommandOccurrenceV1, EconomicPolicyRegistryV1, EconomicProfileSnapshotV1,
    GlobalAllocationBindingRejectCodeV1, GlobalEconomicStateEffectRefinementCandidateV1,
    GlobalEconomicStateEffectRefinementV1, GlobalEconomicStateV1, LaneCoordinatorRegistryV1,
    LaneCoordinatorReleaseV1, LaneIdV1, LaneModuleReleaseV1, LaneRegistryV1, ProfileStatusV1,
    ReleaseStatusV1, RootV1, RouteCompositionJournalV1, RouteGlobalStateProjectionCandidateV1,
    RouteGlobalStateProjectionV1, RouteRegistryV1, RouteReleaseV1, ASSET_TRANSFER_MODULE_SCHEMA_V1,
    GLOBAL_SETTLEMENT_ABI_V1, MAX_JOURNAL_BYTES_V1,
};

/// The unchanged V1 route wire schema. The custody successor is selected by
/// the reviewed specification roots, never by a new schema string.
pub const ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_SCHEMA_V1: &str =
    "zenodex/asset-transfer-route-guest-input/v1";
/// The unchanged V1 route input byte ceiling.
pub const MAX_ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_BYTES_V1: usize = 8 * 1024 * 1024;

/// The unchanged V1 route wire envelope over the custody coordinator input.
/// No coordinator membership field is added to the route wire.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferCustodyRouteInputV1 {
    pub schema: String,
    pub lane_input: AssetLaneCustodyCoordinatorInputV1,
    pub profile: EconomicProfileSnapshotV1,
    pub lanes: LaneRegistryV1,
    pub coordinators: LaneCoordinatorRegistryV1,
    pub routes: RouteRegistryV1,
    pub policy_registry: EconomicPolicyRegistryV1,
    pub asset_policy_registry: AssetTransferPolicyRegistryV1,
    pub occurrence: EconomicCommandOccurrenceV1,
    pub pre_state: GlobalEconomicStateV1,
    pub post_state: GlobalEconomicStateV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssetTransferCustodyRouteErrorV1 {
    Bounds,
    Decode,
    NonCanonical,
    Schema,
    Abi(AbiErrorV1),
    Lane(AssetLaneCustodyCoordinatorGuestErrorV1),
    GlobalBinding(GlobalAllocationBindingRejectCodeV1),
}

impl fmt::Display for AssetTransferCustodyRouteErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "asset transfer custody route rejected: {self:?}")
    }
}

impl std::error::Error for AssetTransferCustodyRouteErrorV1 {}

impl From<AbiErrorV1> for AssetTransferCustodyRouteErrorV1 {
    fn from(value: AbiErrorV1) -> Self {
        Self::Abi(value)
    }
}

/// Ordinary prepared data for one governed custody-complete route.
///
/// The expected image identities are metadata copied from the selected
/// coordinator and route releases. They are not a receipt, a verifier
/// callback, a pinned image constant, or an activation handle.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedAssetTransferCustodyRouteV1 {
    input: AssetTransferCustodyRouteInputV1,
    lane: PreparedAssetLaneCustodyCoordinatorV1,
    route_journal: RouteCompositionJournalV1,
    route_journal_bytes: Vec<u8>,
    projection: RouteGlobalStateProjectionV1,
    projection_root: RootV1,
    refinement: GlobalEconomicStateEffectRefinementV1,
    refinement_root: RootV1,
    expected_coordinator_image_id: RootV1,
    expected_route_image_id: RootV1,
}

impl PreparedAssetTransferCustodyRouteV1 {
    pub fn input(&self) -> &AssetTransferCustodyRouteInputV1 {
        &self.input
    }

    /// The unchanged custody coordinator preflight value for `lane_input`.
    pub fn lane(&self) -> &PreparedAssetLaneCustodyCoordinatorV1 {
        &self.lane
    }

    pub fn module_journal_bytes(&self) -> &[u8] {
        &self.lane.module_journal_bytes
    }

    pub fn lane_journal_bytes(&self) -> &[u8] {
        &self.lane.lane_journal_bytes
    }

    pub fn route_journal(&self) -> &RouteCompositionJournalV1 {
        &self.route_journal
    }

    pub fn route_journal_bytes(&self) -> &[u8] {
        &self.route_journal_bytes
    }

    pub fn projection(&self) -> &RouteGlobalStateProjectionV1 {
        &self.projection
    }

    pub fn projection_root(&self) -> &RootV1 {
        &self.projection_root
    }

    pub fn refinement(&self) -> &GlobalEconomicStateEffectRefinementV1 {
        &self.refinement
    }

    pub fn refinement_root(&self) -> &RootV1 {
        &self.refinement_root
    }

    /// `guest_image_id` of the selected coordinator release, copied as data.
    pub fn expected_coordinator_image_id(&self) -> &RootV1 {
        &self.expected_coordinator_image_id
    }

    /// `guest_image_id` of the governed route release, copied as data.
    pub fn expected_route_image_id(&self) -> &RootV1 {
        &self.expected_route_image_id
    }
}

fn governed_route(
    input: &AssetTransferCustodyRouteInputV1,
) -> Result<&RouteReleaseV1, AssetTransferCustodyRouteErrorV1> {
    let route = input.routes.route_for_command(
        &input.occurrence.command_kind,
        Some(&input.occurrence.route_release_id),
    )?;
    Ok(route)
}

fn selected_module(
    lanes: &LaneRegistryV1,
) -> Result<&LaneModuleReleaseV1, AssetTransferCustodyRouteErrorV1> {
    lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .ok_or(AbiErrorV1::InvalidBinding("custody route module").into())
}

fn selected_coordinator(
    coordinators: &LaneCoordinatorRegistryV1,
) -> Result<&LaneCoordinatorReleaseV1, AssetTransferCustodyRouteErrorV1> {
    coordinators
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .ok_or(AbiErrorV1::InvalidBinding("custody route coordinator").into())
}

fn require_governed_input(
    input: &AssetTransferCustodyRouteInputV1,
) -> Result<(), AssetTransferCustodyRouteErrorV1> {
    if input.schema != ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_SCHEMA_V1 {
        return Err(AssetTransferCustodyRouteErrorV1::Schema);
    }
    input
        .profile
        .validate_registries(&input.lanes, &input.coordinators, &input.routes)?;
    if input.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding("custody route active profile").into());
    }
    require_governed_asset_transfer_policy_registry_v1(
        &input.profile,
        &input.lanes,
        &input.policy_registry,
        &input.occurrence,
        &input.asset_policy_registry,
    )?;
    require_asset_transfer_policy_membership_v1(
        &input.asset_policy_registry,
        &input.lane_input.module_input,
    )?;
    let route = governed_route(input)?;
    let module = selected_module(&input.lanes)?;
    let coordinator = selected_coordinator(&input.coordinators)?;
    if route.ordered_lanes != [LaneIdV1::ASSET_TRANSFER]
        || route.module_release_ids != [module.release_id.clone()]
        || [route.status, module.status, coordinator.status]
            .iter()
            .any(|status| *status != ReleaseStatusV1::ACTIVE_NEW)
        || !route.accepts_new_objects
        || !module.accepts_new_objects
        || !coordinator.accepts_new_objects
    {
        return Err(AbiErrorV1::InvalidBinding("custody route selected release scope").into());
    }
    require_command_context(input, module, coordinator)
}

fn require_command_context(
    input: &AssetTransferCustodyRouteInputV1,
    module: &LaneModuleReleaseV1,
    coordinator: &LaneCoordinatorReleaseV1,
) -> Result<(), AssetTransferCustodyRouteErrorV1> {
    let context = &input.lane_input.coordinator_context;
    let module_input = &input.lane_input.module_input;
    if context.coordinator_release_id != coordinator.coordinator_release_id
        || context.compatible_modules.len() != 1
        || context.compatible_modules[0].module_release_id != module.release_id
        || context.compatible_modules[0].module_schema != ASSET_TRANSFER_MODULE_SCHEMA_V1
        || input.occurrence.profile_root != input.profile.profile_id
        || input.occurrence.command_body_hash != module_input.command.command_body_hash()?
        || input.occurrence.subject_id != module_input.context.subject_id
        || input.occurrence.grant_root != module_input.context.grant_root
    {
        return Err(AbiErrorV1::InvalidBinding("custody route exact command and release").into());
    }
    Ok(())
}

/// The reviewed bundle root must be the specification root of the selected
/// module, coordinator, and single-lane route before any custody recomputation.
fn require_custody_semantics(
    input: &AssetTransferCustodyRouteInputV1,
) -> Result<(), AssetTransferCustodyRouteErrorV1> {
    require_asset_transfer_custody_semantics_v1(
        &input.profile,
        &input.lanes,
        &input.coordinators,
        &input.routes,
        &input.occurrence,
    )?;
    Ok(())
}

fn derive_route_journal(
    input: &AssetTransferCustodyRouteInputV1,
    lane: &PreparedAssetLaneCustodyCoordinatorV1,
) -> Result<RouteCompositionJournalV1, AssetTransferCustodyRouteErrorV1> {
    let journal = &lane.lane_accepted.lane_journal;
    Ok(RouteCompositionJournalV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        chain_id: journal.chain_id.clone(),
        deployment_root: journal.deployment_root.clone(),
        profile_root: journal.profile_root.clone(),
        writer_epoch: journal.writer_epoch,
        route_release_id: input.occurrence.route_release_id.clone(),
        command_occurrence_id: journal.command_occurrence_id.clone(),
        ordered_lane_journal_roots: vec![journal.journal_root()?],
        pre_state_root: input.pre_state.state_root()?,
        post_state_root: input.post_state.state_root()?,
        effect_plan_root: journal.effect_plan_root.clone(),
        terminal_obligations_root: journal.terminal_obligations_root.clone(),
    })
}

fn require_journal_bounds(
    route: &RouteReleaseV1,
    coordinator: &LaneCoordinatorReleaseV1,
    module: &LaneModuleReleaseV1,
    route_bytes: &[u8],
    lane_bytes: &[u8],
    module_bytes: &[u8],
) -> Result<(), AssetTransferCustodyRouteErrorV1> {
    let length =
        u64::try_from(route_bytes.len()).map_err(|_| AssetTransferCustodyRouteErrorV1::Bounds)?;
    let child_length =
        u64::try_from(lane_bytes.len()).map_err(|_| AssetTransferCustodyRouteErrorV1::Bounds)?;
    let module_length =
        u64::try_from(module_bytes.len()).map_err(|_| AssetTransferCustodyRouteErrorV1::Bounds)?;
    if length == 0
        || length > route.max_journal_bytes
        || length > MAX_JOURNAL_BYTES_V1
        || child_length == 0
        || child_length > coordinator.max_journal_bytes
        || child_length > MAX_JOURNAL_BYTES_V1
        || module_length == 0
        || module_length > module.max_journal_bytes
        || module_length > MAX_JOURNAL_BYTES_V1
    {
        return Err(AssetTransferCustodyRouteErrorV1::Bounds);
    }
    Ok(())
}

/// Prepare one governed custody-complete route from typed input.
///
/// Order: exact governed input, reviewed custody semantics, outer input size,
/// custody coordinator preflight, exact global allocation, route journal, route
/// projection, global effect refinement, all three journal bounds. Unknown or mixed specification roots
/// reject before the coordinator runs and before any global check.
pub fn prepare_asset_transfer_custody_route_v1(
    input: AssetTransferCustodyRouteInputV1,
) -> Result<PreparedAssetTransferCustodyRouteV1, AssetTransferCustodyRouteErrorV1> {
    require_governed_input(&input)?;
    require_custody_semantics(&input)?;
    require_size(&canonical_bytes_v1(&input)?)?;
    let lane = prepare_asset_lane_custody_coordinator_v1(input.lane_input.clone())
        .map_err(AssetTransferCustodyRouteErrorV1::Lane)?;
    if let Some(code) =
        check_asset_transfer_global_allocation_v1(AssetTransferGlobalAllocationCandidateV1 {
            accepted: &lane.module_accepted,
            occurrence: &input.occurrence,
            predecessor: &input.pre_state,
            current: &input.post_state,
        })?
    {
        return Err(AssetTransferCustodyRouteErrorV1::GlobalBinding(code));
    }
    let route_journal = derive_route_journal(&input, &lane)?;
    let route = governed_route(&input)?;
    let projection = project_route_global_state_v1(RouteGlobalStateProjectionCandidateV1 {
        profile: &input.profile,
        lanes: &input.lanes,
        coordinators: &input.coordinators,
        routes: &input.routes,
        route,
        lane_journals: std::slice::from_ref(&lane.lane_accepted.lane_journal),
        route_journal: &route_journal,
        pre_state: &input.pre_state,
        post_state: &input.post_state,
    })?;
    let refinement = refine_route_global_economic_state_effects_v1(
        &GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &input.pre_state,
            post_state: &input.post_state,
            effect_plan: &lane.lane_accepted.effects,
            consumed_occurrences: std::slice::from_ref(&input.occurrence),
            route_journals: std::slice::from_ref(&route_journal),
        },
    )?;
    let coordinator = selected_coordinator(&input.coordinators)?;
    let route_journal_bytes = canonical_bytes_v1(&route_journal)?;
    require_journal_bounds(
        route,
        coordinator,
        selected_module(&input.lanes)?,
        &route_journal_bytes,
        &lane.lane_journal_bytes,
        &lane.module_journal_bytes,
    )?;
    Ok(PreparedAssetTransferCustodyRouteV1 {
        projection_root: projection.projection_root()?,
        refinement_root: refinement.refinement_root()?,
        expected_coordinator_image_id: coordinator.guest_image_id.clone(),
        expected_route_image_id: route.guest_image_id.clone(),
        input,
        lane,
        route_journal,
        route_journal_bytes,
        projection,
        refinement,
    })
}

/// Canonical bytes of an input that prepares; unprepared input yields no bytes.
pub fn canonical_asset_transfer_custody_route_input_bytes_v1(
    input: &AssetTransferCustodyRouteInputV1,
) -> Result<Vec<u8>, AssetTransferCustodyRouteErrorV1> {
    prepare_asset_transfer_custody_route_v1(input.clone())?;
    let bytes = canonical_bytes_v1(input)?;
    require_size(&bytes)?;
    Ok(bytes)
}

/// Decode and prepare only an exactly canonical, size-bounded V1 route input.
pub fn prepare_asset_transfer_custody_route_from_bytes_v1(
    bytes: &[u8],
) -> Result<PreparedAssetTransferCustodyRouteV1, AssetTransferCustodyRouteErrorV1> {
    require_size(bytes)?;
    let input: AssetTransferCustodyRouteInputV1 =
        serde_json::from_slice(bytes).map_err(|_| AssetTransferCustodyRouteErrorV1::Decode)?;
    if canonical_bytes_v1(&input)? != bytes {
        return Err(AssetTransferCustodyRouteErrorV1::NonCanonical);
    }
    prepare_asset_transfer_custody_route_v1(input)
}

fn require_size(bytes: &[u8]) -> Result<(), AssetTransferCustodyRouteErrorV1> {
    if bytes.is_empty() || bytes.len() > MAX_ASSET_TRANSFER_CUSTODY_ROUTE_INPUT_BYTES_V1 {
        return Err(AssetTransferCustodyRouteErrorV1::Bounds);
    }
    Ok(())
}
