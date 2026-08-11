use serde::Serialize;

use crate::asset_transfer_lane_module::{
    AssetTransferLaneModuleAcceptedV1, AssetTransferLaneModuleInputV1,
};
use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::managed_asset_lifecycle_lane_module::{
    ManagedAssetLifecycleLaneModuleAcceptedV1, ManagedAssetLifecycleLaneModuleInputV1,
};
use crate::proof::{EconomicCommandOccurrenceV1, LaneModuleTransitionJournalV1};
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneIdV1, LaneRegistryV1,
    ProfileStatusV1, RouteRegistryV1,
};

pub const RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1: &str =
    "zenodex/release-route-bound-lane-transition/v1";

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReleaseRouteBoundLaneTransitionV1 {
    profile_id: RootV1,
    route_release_id: RootV1,
    lane_id: LaneIdV1,
    module_release_id: RootV1,
    command_occurrence_id: RootV1,
    module_journal_root: RootV1,
    statement_root: RootV1,
    producer_module_schema: String,
    route_lane_index: usize,
    port_schema_root: RootV1,
}

#[derive(Serialize)]
struct ReleaseRouteBoundLaneTransitionContentV1<'a> {
    schema: &'static str,
    profile_id: &'a RootV1,
    route_release_id: &'a RootV1,
    lane_id: LaneIdV1,
    module_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    module_journal_root: &'a RootV1,
    statement_root: &'a RootV1,
    producer_module_schema: &'a str,
    route_lane_index: usize,
    port_schema_root: &'a RootV1,
}

impl ReleaseRouteBoundLaneTransitionV1 {
    pub fn profile_id(&self) -> &RootV1 {
        &self.profile_id
    }

    pub fn route_release_id(&self) -> &RootV1 {
        &self.route_release_id
    }

    pub fn lane_id(&self) -> LaneIdV1 {
        self.lane_id
    }

    pub fn module_release_id(&self) -> &RootV1 {
        &self.module_release_id
    }

    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.command_occurrence_id
    }

    pub fn module_journal_root(&self) -> &RootV1 {
        &self.module_journal_root
    }

    pub fn statement_root(&self) -> &RootV1 {
        &self.statement_root
    }

    pub fn producer_module_schema(&self) -> &str {
        &self.producer_module_schema
    }

    pub fn route_lane_index(&self) -> usize {
        self.route_lane_index
    }

    pub fn port_schema_root(&self) -> &RootV1 {
        &self.port_schema_root
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "release-route-bound-lane-transition-v1",
            &ReleaseRouteBoundLaneTransitionContentV1 {
                schema: RELEASE_ROUTE_BOUND_LANE_TRANSITION_SCHEMA_V1,
                profile_id: &self.profile_id,
                route_release_id: &self.route_release_id,
                lane_id: self.lane_id,
                module_release_id: &self.module_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                module_journal_root: &self.module_journal_root,
                statement_root: &self.statement_root,
                producer_module_schema: &self.producer_module_schema,
                route_lane_index: self.route_lane_index,
                port_schema_root: &self.port_schema_root,
            },
        )
    }
}

struct ModuleContextBindingV1<'a> {
    chain_id: &'a str,
    deployment_root: &'a RootV1,
    profile_root: &'a RootV1,
    writer_epoch: u64,
    module_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    subject_id: &'a str,
    grant_root: &'a RootV1,
}

struct BindingCandidateV1<'a> {
    actual_command_kind: &'a str,
    statement_root: &'a RootV1,
    producer_module_schema: &'a str,
    context: ModuleContextBindingV1<'a>,
    module_journal: &'a LaneModuleTransitionJournalV1,
}

fn require_context_binding(
    profile: &EconomicProfileSnapshotV1,
    occurrence: &EconomicCommandOccurrenceV1,
    context: &ModuleContextBindingV1<'_>,
) -> AbiResultV1<()> {
    if context.subject_id != occurrence.subject_id {
        return Err(AbiErrorV1::InvalidBinding("lane module subject"));
    }
    if context.grant_root != &occurrence.grant_root {
        return Err(AbiErrorV1::InvalidBinding("lane module grant root"));
    }
    if context.chain_id != occurrence.chain_id {
        return Err(AbiErrorV1::InvalidBinding("lane module chain id"));
    }
    if context.deployment_root != &occurrence.deployment_root {
        return Err(AbiErrorV1::InvalidBinding("lane module deployment root"));
    }
    if context.profile_root != &profile.profile_id {
        return Err(AbiErrorV1::InvalidBinding("lane module profile root"));
    }
    if context.command_occurrence_id != &occurrence.occurrence_id()? {
        return Err(AbiErrorV1::InvalidBinding("lane module occurrence"));
    }
    if context.writer_epoch != profile.authority_epoch {
        return Err(AbiErrorV1::InvalidBinding("lane module writer epoch"));
    }
    Ok(())
}

fn require_journal_binding(
    profile: &EconomicProfileSnapshotV1,
    occurrence: &EconomicCommandOccurrenceV1,
    journal: &LaneModuleTransitionJournalV1,
) -> AbiResultV1<()> {
    if journal.chain_id != occurrence.chain_id {
        return Err(AbiErrorV1::InvalidBinding("module journal chain id"));
    }
    if journal.deployment_root != occurrence.deployment_root {
        return Err(AbiErrorV1::InvalidBinding("module journal deployment root"));
    }
    if journal.profile_root != profile.profile_id {
        return Err(AbiErrorV1::InvalidBinding("module journal profile root"));
    }
    if journal.command_occurrence_id != occurrence.occurrence_id()? {
        return Err(AbiErrorV1::InvalidBinding("module journal occurrence"));
    }
    if journal.writer_epoch != profile.authority_epoch {
        return Err(AbiErrorV1::InvalidBinding("module journal writer epoch"));
    }
    Ok(())
}

fn bind_candidate_v1(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    candidate: BindingCandidateV1<'_>,
) -> AbiResultV1<ReleaseRouteBoundLaneTransitionV1> {
    profile.validate()?;
    if profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding("economic profile is not active"));
    }
    profile.validate_registries(lanes, coordinators, routes)?;
    occurrence.validate()?;
    candidate.module_journal.validate()?;
    let route =
        routes.route_for_command(&occurrence.command_kind, Some(&occurrence.route_release_id))?;
    if candidate.actual_command_kind != occurrence.command_kind {
        return Err(AbiErrorV1::InvalidBinding("lane module command kind"));
    }
    require_context_binding(profile, occurrence, &candidate.context)?;
    require_journal_binding(profile, occurrence, candidate.module_journal)?;

    let route_lane_index = route
        .ordered_lanes
        .iter()
        .position(|lane| lane == &candidate.module_journal.lane_id)
        .ok_or(AbiErrorV1::InvalidBinding("lane module route lane"))?;
    let release = lanes
        .release_for(candidate.module_journal.lane_id)
        .ok_or(AbiErrorV1::InvalidBinding("lane module release lane"))?;
    if candidate.module_journal.module_release_id != release.release_id
        || route.module_release_ids[route_lane_index] != release.release_id
        || candidate.context.module_release_id != &release.release_id
    {
        return Err(AbiErrorV1::InvalidBinding("lane module release mismatch"));
    }
    if !release
        .command_variants
        .iter()
        .any(|command| command == candidate.actual_command_kind)
    {
        return Err(AbiErrorV1::InvalidBinding(
            "lane module command absent from release",
        ));
    }

    Ok(ReleaseRouteBoundLaneTransitionV1 {
        profile_id: profile.profile_id.clone(),
        route_release_id: route.route_release_id.clone(),
        lane_id: candidate.module_journal.lane_id,
        module_release_id: release.release_id.clone(),
        command_occurrence_id: occurrence.occurrence_id()?,
        module_journal_root: candidate.module_journal.journal_root()?,
        statement_root: candidate.statement_root.clone(),
        producer_module_schema: candidate.producer_module_schema.to_owned(),
        route_lane_index,
        port_schema_root: route.port_schema_roots[route_lane_index].clone(),
    })
}

pub fn bind_asset_transfer_lane_output_to_release_route_v1(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    module_input: &AssetTransferLaneModuleInputV1,
    accepted: &AssetTransferLaneModuleAcceptedV1,
) -> AbiResultV1<ReleaseRouteBoundLaneTransitionV1> {
    module_input.validate()?;
    accepted.validate()?;
    let statement_root = module_input.statement_root()?;
    if accepted.statement_root != statement_root {
        return Err(AbiErrorV1::InvalidBinding(
            "asset transfer accepted statement",
        ));
    }
    bind_candidate_v1(
        profile,
        lanes,
        coordinators,
        routes,
        occurrence,
        BindingCandidateV1 {
            actual_command_kind: &module_input.command.command_kind,
            statement_root: &accepted.statement_root,
            producer_module_schema: &accepted.private_port.producer_module_schema,
            context: ModuleContextBindingV1 {
                chain_id: &module_input.context.chain_id,
                deployment_root: &module_input.context.deployment_root,
                profile_root: &module_input.context.profile_root,
                writer_epoch: module_input.context.writer_epoch,
                module_release_id: &module_input.context.module_release_id,
                command_occurrence_id: &module_input.context.command_occurrence_id,
                subject_id: &module_input.context.subject_id,
                grant_root: &module_input.context.grant_root,
            },
            module_journal: &accepted.module_journal,
        },
    )
}

pub fn bind_managed_asset_lifecycle_lane_output_to_release_route_v1(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
    module_input: &ManagedAssetLifecycleLaneModuleInputV1,
    accepted: &ManagedAssetLifecycleLaneModuleAcceptedV1,
) -> AbiResultV1<ReleaseRouteBoundLaneTransitionV1> {
    module_input.validate()?;
    accepted.validate()?;
    let statement_root = module_input.statement_root()?;
    if accepted.statement_root != statement_root {
        return Err(AbiErrorV1::InvalidBinding(
            "managed asset accepted statement",
        ));
    }
    bind_candidate_v1(
        profile,
        lanes,
        coordinators,
        routes,
        occurrence,
        BindingCandidateV1 {
            actual_command_kind: &module_input.command.command_kind,
            statement_root: &accepted.statement_root,
            producer_module_schema: &accepted.private_port.producer_module_schema,
            context: ModuleContextBindingV1 {
                chain_id: &module_input.context.chain_id,
                deployment_root: &module_input.context.deployment_root,
                profile_root: &module_input.context.profile_root,
                writer_epoch: module_input.context.writer_epoch,
                module_release_id: &module_input.context.module_release_id,
                command_occurrence_id: &module_input.context.command_occurrence_id,
                subject_id: &module_input.context.subject_id,
                grant_root: &module_input.context.grant_root,
            },
            module_journal: &accepted.module_journal,
        },
    )
}
