//! One governed asset-transfer route with explicit full-state refinement.
//! Preparing values does not authenticate snapshots, signatures or publication.

use core::fmt;
use serde::{Deserialize, Serialize};
use zenodex_asset_lane_coordinator_risc0_shared::{
    prepare_asset_lane_coordinator_v1, AssetLaneCoordinatorGuestErrorV1,
    AssetLaneCoordinatorGuestInputV1, PreparedAssetLaneCoordinatorV1,
};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, check_asset_transfer_global_allocation_v1, project_route_global_state_v1,
    refine_route_global_economic_state_effects_v1, require_asset_transfer_policy_membership_v1,
    require_governed_asset_transfer_policy_registry_v1, AbiErrorV1,
    AssetTransferGlobalAllocationCandidateV1, AssetTransferPolicyRegistryV1,
    EconomicCommandOccurrenceV1, EconomicPolicyRegistryV1, EconomicProfileSnapshotV1,
    GlobalAllocationBindingRejectCodeV1, GlobalEconomicStateEffectRefinementCandidateV1,
    GlobalEconomicStateV1, LaneCoordinatorRegistryV1, LaneCoordinatorReleaseV1, LaneIdV1,
    LaneModuleReleaseV1, LaneRegistryV1, ProfileStatusV1, ReleaseStatusV1, RootV1,
    RouteCompositionJournalV1, RouteGlobalStateProjectionCandidateV1, RouteRegistryV1,
    RouteReleaseV1, ASSET_TRANSFER_MODULE_SCHEMA_V1, GLOBAL_SETTLEMENT_ABI_V1,
    MAX_JOURNAL_BYTES_V1,
};

pub const ASSET_TRANSFER_ROUTE_INPUT_SCHEMA_V1: &str =
    "zenodex/asset-transfer-route-guest-input/v1";
pub const MAX_ASSET_TRANSFER_ROUTE_INPUT_BYTES_V1: usize = 8 * 1024 * 1024;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferRouteGuestInputV1 {
    pub schema: String,
    pub lane_input: AssetLaneCoordinatorGuestInputV1,
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

#[derive(Debug)]
pub enum AssetTransferRouteGuestErrorV1 {
    Bounds,
    Decode,
    NonCanonical,
    Schema,
    Abi(AbiErrorV1),
    Lane(AssetLaneCoordinatorGuestErrorV1),
    GlobalBinding(GlobalAllocationBindingRejectCodeV1),
}
impl fmt::Display for AssetTransferRouteGuestErrorV1 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "asset route rejected: {self:?}")
    }
}
impl std::error::Error for AssetTransferRouteGuestErrorV1 {}
impl From<AbiErrorV1> for AssetTransferRouteGuestErrorV1 {
    fn from(value: AbiErrorV1) -> Self {
        Self::Abi(value)
    }
}

#[derive(Clone, Debug)]
pub struct PreparedAssetTransferRouteV1 {
    input: AssetTransferRouteGuestInputV1,
    lane_journal_bytes: Vec<u8>,
    route_journal_bytes: Vec<u8>,
    coordinator_image: [u32; 8],
    route_image: RootV1,
    projection_root: RootV1,
    refinement_root: RootV1,
}
impl PreparedAssetTransferRouteV1 {
    pub fn input(&self) -> &AssetTransferRouteGuestInputV1 {
        &self.input
    }
    pub fn lane_journal_bytes(&self) -> &[u8] {
        &self.lane_journal_bytes
    }
    pub fn route_journal_bytes(&self) -> &[u8] {
        &self.route_journal_bytes
    }
    pub fn coordinator_image(&self) -> [u32; 8] {
        self.coordinator_image
    }
    pub fn route_image(&self) -> &RootV1 {
        &self.route_image
    }
    pub fn projection_root(&self) -> &RootV1 {
        &self.projection_root
    }
    pub fn refinement_root(&self) -> &RootV1 {
        &self.refinement_root
    }
}

fn image_words(root: &RootV1) -> Result<[u32; 8], AssetTransferRouteGuestErrorV1> {
    root.validate("route coordinator image", false)?;
    let bytes =
        hex::decode(&root.as_str()[2..]).map_err(|_| AssetTransferRouteGuestErrorV1::Decode)?;
    let mut words = [0u32; 8];
    for (word, chunk) in words.iter_mut().zip(bytes.chunks_exact(4)) {
        *word = u32::from_le_bytes(
            chunk
                .try_into()
                .map_err(|_| AssetTransferRouteGuestErrorV1::Decode)?,
        );
    }
    Ok(words)
}

fn require_governed_input(
    input: &AssetTransferRouteGuestInputV1,
) -> Result<(), AssetTransferRouteGuestErrorV1> {
    if input.schema != ASSET_TRANSFER_ROUTE_INPUT_SCHEMA_V1 {
        return Err(AssetTransferRouteGuestErrorV1::Schema);
    }
    input
        .profile
        .validate_registries(&input.lanes, &input.coordinators, &input.routes)?;
    if input.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding("asset route active profile").into());
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
    let route = input.routes.route_for_command(
        &input.occurrence.command_kind,
        Some(&input.occurrence.route_release_id),
    )?;
    let module = input
        .lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .ok_or(AbiErrorV1::InvalidBinding("asset route module"))?;
    let coordinator = selected_coordinator(&input.coordinators)?;
    if route.ordered_lanes != [LaneIdV1::ASSET_TRANSFER]
        || route.module_release_ids != [module.release_id.clone()]
        || [route.status, module.status, coordinator.status]
            .iter()
            .any(|s| *s != ReleaseStatusV1::ACTIVE_NEW)
        || !route.accepts_new_objects
        || !module.accepts_new_objects
        || !coordinator.accepts_new_objects
    {
        return Err(AbiErrorV1::InvalidBinding("asset route selected release scope").into());
    }
    require_command_context(input, module, coordinator)
}

fn require_command_context(
    input: &AssetTransferRouteGuestInputV1,
    module: &LaneModuleReleaseV1,
    coordinator: &LaneCoordinatorReleaseV1,
) -> Result<(), AssetTransferRouteGuestErrorV1> {
    let context = &input.lane_input.coordinator_context;
    if context.coordinator_release_id != coordinator.coordinator_release_id
        || context.compatible_modules.len() != 1
        || context.compatible_modules[0].module_release_id != module.release_id
        || context.compatible_modules[0].module_schema != ASSET_TRANSFER_MODULE_SCHEMA_V1
        || input.occurrence.profile_root != input.profile.profile_id
        || input.occurrence.command_body_hash
            != input.lane_input.module_input.command.command_body_hash()?
        || input.occurrence.subject_id != input.lane_input.module_input.context.subject_id
        || input.occurrence.grant_root != input.lane_input.module_input.context.grant_root
    {
        return Err(AbiErrorV1::InvalidBinding("asset route exact command and release").into());
    }
    Ok(())
}

fn selected_coordinator(
    coordinators: &LaneCoordinatorRegistryV1,
) -> Result<&LaneCoordinatorReleaseV1, AssetTransferRouteGuestErrorV1> {
    coordinators
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .ok_or(AbiErrorV1::InvalidBinding("asset route coordinator").into())
}

fn derive_route_journal(
    input: &AssetTransferRouteGuestInputV1,
    lane: &PreparedAssetLaneCoordinatorV1,
) -> Result<RouteCompositionJournalV1, AssetTransferRouteGuestErrorV1> {
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

pub fn prepare_asset_transfer_route_v1(
    input: AssetTransferRouteGuestInputV1,
) -> Result<PreparedAssetTransferRouteV1, AssetTransferRouteGuestErrorV1> {
    require_governed_input(&input)?;
    let lane = prepare_asset_lane_coordinator_v1(input.lane_input.clone())
        .map_err(AssetTransferRouteGuestErrorV1::Lane)?;
    if let Some(code) =
        check_asset_transfer_global_allocation_v1(AssetTransferGlobalAllocationCandidateV1 {
            accepted: &lane.module_accepted,
            occurrence: &input.occurrence,
            predecessor: &input.pre_state,
            current: &input.post_state,
        })?
    {
        return Err(AssetTransferRouteGuestErrorV1::GlobalBinding(code));
    }
    let journal = derive_route_journal(&input, &lane)?;
    let route = input.routes.route_for_command(
        &input.occurrence.command_kind,
        Some(&input.occurrence.route_release_id),
    )?;
    let projection = project_route_global_state_v1(RouteGlobalStateProjectionCandidateV1 {
        profile: &input.profile,
        lanes: &input.lanes,
        coordinators: &input.coordinators,
        routes: &input.routes,
        route,
        lane_journals: std::slice::from_ref(&lane.lane_accepted.lane_journal),
        route_journal: &journal,
        pre_state: &input.pre_state,
        post_state: &input.post_state,
    })?;
    let refinement = refine_route_global_economic_state_effects_v1(
        &GlobalEconomicStateEffectRefinementCandidateV1 {
            pre_state: &input.pre_state,
            post_state: &input.post_state,
            effect_plan: &lane.lane_accepted.effects,
            consumed_occurrences: std::slice::from_ref(&input.occurrence),
            route_journals: std::slice::from_ref(&journal),
        },
    )?;
    let coordinator = selected_coordinator(&input.coordinators)?;
    let route_journal_bytes = canonical_bytes_v1(&journal)?;
    require_journal_bounds(
        route,
        coordinator,
        &route_journal_bytes,
        &lane.lane_journal_bytes,
    )?;
    Ok(PreparedAssetTransferRouteV1 {
        coordinator_image: image_words(&coordinator.guest_image_id)?,
        route_image: route.guest_image_id.clone(),
        projection_root: projection.projection_root()?,
        refinement_root: refinement.refinement_root()?,
        input,
        lane_journal_bytes: lane.lane_journal_bytes,
        route_journal_bytes,
    })
}

fn require_journal_bounds(
    route: &RouteReleaseV1,
    coordinator: &LaneCoordinatorReleaseV1,
    route_bytes: &[u8],
    lane_bytes: &[u8],
) -> Result<(), AssetTransferRouteGuestErrorV1> {
    let length =
        u64::try_from(route_bytes.len()).map_err(|_| AssetTransferRouteGuestErrorV1::Bounds)?;
    let child_length =
        u64::try_from(lane_bytes.len()).map_err(|_| AssetTransferRouteGuestErrorV1::Bounds)?;
    if length == 0
        || length > route.max_journal_bytes
        || length > MAX_JOURNAL_BYTES_V1
        || child_length == 0
        || child_length > coordinator.max_journal_bytes
        || child_length > MAX_JOURNAL_BYTES_V1
    {
        return Err(AssetTransferRouteGuestErrorV1::Bounds);
    }
    Ok(())
}

pub fn canonical_asset_transfer_route_input_bytes_v1(
    input: &AssetTransferRouteGuestInputV1,
) -> Result<Vec<u8>, AssetTransferRouteGuestErrorV1> {
    prepare_asset_transfer_route_v1(input.clone())?;
    let bytes = canonical_bytes_v1(input)?;
    require_size(&bytes)?;
    Ok(bytes)
}

pub fn prepare_asset_transfer_route_from_bytes_v1(
    bytes: &[u8],
) -> Result<PreparedAssetTransferRouteV1, AssetTransferRouteGuestErrorV1> {
    require_size(bytes)?;
    let input: AssetTransferRouteGuestInputV1 =
        serde_json::from_slice(bytes).map_err(|_| AssetTransferRouteGuestErrorV1::Decode)?;
    if canonical_bytes_v1(&input)? != bytes {
        return Err(AssetTransferRouteGuestErrorV1::NonCanonical);
    }
    prepare_asset_transfer_route_v1(input)
}

fn require_size(bytes: &[u8]) -> Result<(), AssetTransferRouteGuestErrorV1> {
    if bytes.is_empty() || bytes.len() > MAX_ASSET_TRANSFER_ROUTE_INPUT_BYTES_V1 {
        return Err(AssetTransferRouteGuestErrorV1::Bounds);
    }
    Ok(())
}
