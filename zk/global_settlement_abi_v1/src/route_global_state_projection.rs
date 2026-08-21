//! Deterministic full-state projection for one profile-selected route.
//!
//! This checker closes the structural relation between monolithic global
//! state roots and lane-composition journals. It verifies no receipt, applies
//! no economic effects, and grants no settlement or publication authority.

use serde::Serialize;

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::{LaneCompositionJournalV1, RouteCompositionJournalV1};
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneIdV1, LaneRegistryV1,
    ProfileStatusV1, RouteRegistryV1, RouteReleaseV1, ALL_LANE_IDS_V1,
};
use crate::state::{GlobalEconomicStateV1, LaneStateRootV1};
use crate::GLOBAL_SETTLEMENT_ABI_V1;

pub const ROUTE_GLOBAL_STATE_PROJECTION_SCHEMA_V1: &str =
    "zenodex/route-global-state-projection/v1";

#[derive(Clone, Copy, Debug)]
pub struct RouteGlobalStateProjectionCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub route: &'a RouteReleaseV1,
    pub lane_journals: &'a [LaneCompositionJournalV1],
    pub route_journal: &'a RouteCompositionJournalV1,
    pub pre_state: &'a GlobalEconomicStateV1,
    pub post_state: &'a GlobalEconomicStateV1,
}

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct RouteGlobalLaneProjectionV1 {
    lane_id: LaneIdV1,
    module_release_id: RootV1,
    lane_journal_root: RootV1,
    pre_lane_root: RootV1,
    post_lane_root: RootV1,
}

#[derive(Serialize)]
struct UnselectedLaneRootsContentV1<'a> {
    schema: &'static str,
    lane_roots: &'a [LaneStateRootV1],
}

#[derive(Serialize)]
struct RouteGlobalStateProjectionContentV1<'a> {
    schema: &'static str,
    chain_id: &'a str,
    deployment_root: &'a RootV1,
    profile_id: &'a RootV1,
    writer_epoch: u64,
    route_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    route_journal_root: &'a RootV1,
    pre_state_root: &'a RootV1,
    post_state_root: &'a RootV1,
    ordered_lanes: &'a [RouteGlobalLaneProjectionV1],
    unselected_lane_roots_root: &'a RootV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RouteGlobalStateProjectionV1 {
    chain_id: String,
    deployment_root: RootV1,
    profile_id: RootV1,
    writer_epoch: u64,
    route_release_id: RootV1,
    command_occurrence_id: RootV1,
    route_journal_root: RootV1,
    pre_state_root: RootV1,
    post_state_root: RootV1,
    ordered_lanes: Vec<RouteGlobalLaneProjectionV1>,
    unselected_lane_roots_root: RootV1,
}

impl RouteGlobalStateProjectionV1 {
    pub fn ordered_lane_ids(&self) -> Vec<LaneIdV1> {
        self.ordered_lanes.iter().map(|row| row.lane_id).collect()
    }

    pub fn pre_state_root(&self) -> &RootV1 {
        &self.pre_state_root
    }

    pub fn post_state_root(&self) -> &RootV1 {
        &self.post_state_root
    }

    pub fn projection_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "route-global-state-projection-v1",
            &RouteGlobalStateProjectionContentV1 {
                schema: ROUTE_GLOBAL_STATE_PROJECTION_SCHEMA_V1,
                chain_id: &self.chain_id,
                deployment_root: &self.deployment_root,
                profile_id: &self.profile_id,
                writer_epoch: self.writer_epoch,
                route_release_id: &self.route_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                route_journal_root: &self.route_journal_root,
                pre_state_root: &self.pre_state_root,
                post_state_root: &self.post_state_root,
                ordered_lanes: &self.ordered_lanes,
                unselected_lane_roots_root: &self.unselected_lane_roots_root,
            },
        )
    }
}

fn require_profile_route_v1(
    candidate: &RouteGlobalStateProjectionCandidateV1<'_>,
) -> AbiResultV1<()> {
    candidate.profile.validate_registries(
        candidate.lanes,
        candidate.coordinators,
        candidate.routes,
    )?;
    if candidate.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding(
            "route global projection active profile",
        ));
    }
    let governed = candidate.routes.route_for_command(
        &candidate.route.command_kind,
        Some(&candidate.route.route_release_id),
    )?;
    if governed != candidate.route {
        return Err(AbiErrorV1::InvalidBinding(
            "route global projection governed route",
        ));
    }
    Ok(())
}

fn require_global_state_context_v1(
    candidate: &RouteGlobalStateProjectionCandidateV1<'_>,
) -> AbiResultV1<(RootV1, RootV1)> {
    candidate
        .pre_state
        .validate_profile_registry(candidate.profile, candidate.lanes)?;
    candidate
        .post_state
        .validate_profile_registry(candidate.profile, candidate.lanes)?;
    let pre_root = candidate.pre_state.state_root()?;
    let post_root = candidate.post_state.state_root()?;
    let journal = candidate.route_journal;
    if candidate.post_state.chain_id != candidate.pre_state.chain_id {
        return Err(AbiErrorV1::InvalidBinding(
            "route global projection post-state chain",
        ));
    }
    if candidate.post_state.deployment_root != candidate.pre_state.deployment_root {
        return Err(AbiErrorV1::InvalidBinding(
            "route global projection post-state deployment",
        ));
    }
    if candidate.post_state.writer_epoch != candidate.pre_state.writer_epoch {
        return Err(AbiErrorV1::InvalidBinding(
            "route global projection post-state writer epoch",
        ));
    }
    if journal.chain_id != candidate.pre_state.chain_id
        || journal.deployment_root != candidate.pre_state.deployment_root
        || journal.profile_root != candidate.profile.profile_id
        || journal.route_release_id != candidate.route.route_release_id
        || journal.writer_epoch != candidate.profile.authority_epoch
        || journal.pre_state_root != pre_root
        || journal.post_state_root != post_root
    {
        return Err(AbiErrorV1::InvalidBinding(
            "route global projection exact global context",
        ));
    }
    Ok((pre_root, post_root))
}

fn require_lane_journal_context_v1(
    candidate: &RouteGlobalStateProjectionCandidateV1<'_>,
) -> AbiResultV1<()> {
    let journals = candidate.lane_journals;
    if journals.len() != candidate.route.ordered_lanes.len() {
        return Err(AbiErrorV1::InvalidBinding(
            "route global projection lane journal count",
        ));
    }
    if journals.iter().map(|journal| journal.lane_id).ne(candidate
        .route
        .ordered_lanes
        .iter()
        .copied())
    {
        return Err(AbiErrorV1::InvalidOrder(
            "route global projection lane journals",
        ));
    }
    let journal_roots = journals
        .iter()
        .map(LaneCompositionJournalV1::journal_root)
        .collect::<AbiResultV1<Vec<_>>>()?;
    if journal_roots != candidate.route_journal.ordered_lane_journal_roots {
        return Err(AbiErrorV1::InvalidBinding(
            "route global projection route lane journal roots",
        ));
    }
    for journal in journals {
        journal.validate()?;
        let coordinator = candidate.coordinators.release_for(journal.lane_id).ok_or(
            AbiErrorV1::InvalidBinding("route global projection coordinator release"),
        )?;
        if journal.chain_id != candidate.route_journal.chain_id
            || journal.deployment_root != candidate.route_journal.deployment_root
            || journal.profile_root != candidate.route_journal.profile_root
            || journal.writer_epoch != candidate.route_journal.writer_epoch
            || journal.command_occurrence_id != candidate.route_journal.command_occurrence_id
            || journal.coordinator_release_id != coordinator.coordinator_release_id
        {
            return Err(AbiErrorV1::InvalidBinding(
                "route global projection exact lane journal context",
            ));
        }
    }
    Ok(())
}

fn project_lane_roots_v1(
    candidate: &RouteGlobalStateProjectionCandidateV1<'_>,
) -> AbiResultV1<(Vec<RouteGlobalLaneProjectionV1>, Vec<LaneStateRootV1>)> {
    let mut rows = Vec::with_capacity(candidate.route.ordered_lanes.len());
    for (lane_id, journal) in candidate
        .route
        .ordered_lanes
        .iter()
        .zip(candidate.lane_journals)
    {
        let index = ALL_LANE_IDS_V1
            .iter()
            .position(|candidate_lane| candidate_lane == lane_id)
            .ok_or(AbiErrorV1::InvalidBinding(
                "route global projection selected lane",
            ))?;
        let pre_lane = &candidate.pre_state.lane_roots[index];
        let post_lane = &candidate.post_state.lane_roots[index];
        if pre_lane.state_root != journal.pre_lane_root
            || post_lane.state_root != journal.post_lane_root
        {
            return Err(AbiErrorV1::InvalidBinding(
                "route global projection selected lane root",
            ));
        }
        rows.push(RouteGlobalLaneProjectionV1 {
            lane_id: *lane_id,
            module_release_id: pre_lane.module_release_id.clone(),
            lane_journal_root: journal.journal_root()?,
            pre_lane_root: pre_lane.state_root.clone(),
            post_lane_root: post_lane.state_root.clone(),
        });
    }
    let mut unchanged =
        Vec::with_capacity(ALL_LANE_IDS_V1.len() - candidate.route.ordered_lanes.len());
    for (pre_lane, post_lane) in candidate
        .pre_state
        .lane_roots
        .iter()
        .zip(&candidate.post_state.lane_roots)
    {
        if candidate.route.ordered_lanes.contains(&pre_lane.lane_id) {
            continue;
        }
        if pre_lane != post_lane {
            return Err(AbiErrorV1::InvalidBinding(
                "route global projection unselected lane changed",
            ));
        }
        unchanged.push(pre_lane.clone());
    }
    Ok((rows, unchanged))
}

pub fn project_route_global_state_v1(
    candidate: RouteGlobalStateProjectionCandidateV1<'_>,
) -> AbiResultV1<RouteGlobalStateProjectionV1> {
    require_profile_route_v1(&candidate)?;
    candidate.route_journal.validate()?;
    let (pre_state_root, post_state_root) = require_global_state_context_v1(&candidate)?;
    require_lane_journal_context_v1(&candidate)?;
    let (ordered_lanes, unchanged) = project_lane_roots_v1(&candidate)?;
    let unselected_lane_roots_root = hash_global_v1(
        "route-global-unselected-lane-roots-v1",
        &UnselectedLaneRootsContentV1 {
            schema: GLOBAL_SETTLEMENT_ABI_V1,
            lane_roots: &unchanged,
        },
    )?;
    Ok(RouteGlobalStateProjectionV1 {
        chain_id: candidate.pre_state.chain_id.clone(),
        deployment_root: candidate.pre_state.deployment_root.clone(),
        profile_id: candidate.profile.profile_id.clone(),
        writer_epoch: candidate.profile.authority_epoch,
        route_release_id: candidate.route.route_release_id.clone(),
        command_occurrence_id: candidate.route_journal.command_occurrence_id.clone(),
        route_journal_root: candidate.route_journal.journal_root()?,
        pre_state_root,
        post_state_root,
        ordered_lanes,
        unselected_lane_roots_root,
    })
}
