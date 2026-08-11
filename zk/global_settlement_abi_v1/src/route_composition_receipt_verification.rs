use serde::Serialize;

use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::lane_composition_receipt_verification::VerifiedLaneCompositionV1;
use crate::proof::{
    EconomicCommandOccurrenceV1, LaneCompositionJournalV1, ReceiptKindV1, RouteCompositionJournalV1,
};
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneIdV1, LaneRegistryV1,
    ProfileStatusV1, RouteRegistryV1, RouteReleaseV1,
};

pub const VERIFIED_ROUTE_COMPOSITION_SCHEMA_V1: &str = "zenodex/verified-route-composition/v1";
pub const ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1: &str = "zenodex/route-composition-assumption/v1";

/// Cryptographic verifier port selected by the governed route release.
pub trait RouteCompositionSuccinctReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()>;
}

#[derive(Clone, Copy, Debug)]
pub struct RouteCompositionReceiptEnvelopeV1<'a> {
    pub receipt_kind: ReceiptKindV1,
    pub receipt_bytes: &'a [u8],
}

#[derive(Clone, Copy, Debug)]
pub struct RouteCompositionReceiptCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub lane_journals: &'a [LaneCompositionJournalV1],
    pub verified_lanes: &'a [VerifiedLaneCompositionV1],
    pub route_journal: &'a RouteCompositionJournalV1,
    pub receipt: RouteCompositionReceiptEnvelopeV1<'a>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedRouteCompositionV1 {
    profile_id: RootV1,
    route_release_id: RootV1,
    command_occurrence_id: RootV1,
    writer_epoch: u64,
    ordered_lane_ids: Vec<LaneIdV1>,
    ordered_lane_binding_roots: Vec<RootV1>,
    ordered_lane_journal_roots: Vec<RootV1>,
    route_journal_root: RootV1,
    route_journal_digest: RootV1,
    expected_image_id: RootV1,
    receipt_digest: RootV1,
    receipt_kind: ReceiptKindV1,
}

#[derive(Serialize)]
struct VerifiedRouteCompositionContentV1<'a> {
    schema: &'static str,
    profile_id: &'a RootV1,
    route_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    writer_epoch: u64,
    ordered_lane_ids: &'a [LaneIdV1],
    ordered_lane_binding_roots: &'a [RootV1],
    ordered_lane_journal_roots: &'a [RootV1],
    route_journal_root: &'a RootV1,
    route_journal_digest: &'a RootV1,
    expected_image_id: &'a RootV1,
    receipt_digest: &'a RootV1,
    receipt_kind: ReceiptKindV1,
}

#[derive(Serialize)]
struct RouteCompositionAssumptionContentV1<'a> {
    schema: &'static str,
    profile_id: &'a RootV1,
    route_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    writer_epoch: u64,
    route_journal_root: &'a RootV1,
    route_journal_digest: &'a RootV1,
    expected_image_id: &'a RootV1,
}

pub fn derive_route_composition_assumption_root_v1(
    profile_id: &RootV1,
    route_release_id: &RootV1,
    command_occurrence_id: &RootV1,
    writer_epoch: u64,
    route_journal_root: &RootV1,
    route_journal_digest: &RootV1,
    expected_image_id: &RootV1,
) -> AbiResultV1<RootV1> {
    for root in [
        profile_id,
        route_release_id,
        command_occurrence_id,
        route_journal_root,
        route_journal_digest,
        expected_image_id,
    ] {
        root.validate("route composition assumption root", false)?;
    }
    hash_global_v1(
        "route-composition-assumption-v1",
        &RouteCompositionAssumptionContentV1 {
            schema: ROUTE_COMPOSITION_ASSUMPTION_SCHEMA_V1,
            profile_id,
            route_release_id,
            command_occurrence_id,
            writer_epoch,
            route_journal_root,
            route_journal_digest,
            expected_image_id,
        },
    )
}

impl VerifiedRouteCompositionV1 {
    pub fn profile_id(&self) -> &RootV1 {
        &self.profile_id
    }

    pub fn route_release_id(&self) -> &RootV1 {
        &self.route_release_id
    }

    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.command_occurrence_id
    }

    pub fn writer_epoch(&self) -> u64 {
        self.writer_epoch
    }

    pub fn ordered_lane_ids(&self) -> &[LaneIdV1] {
        &self.ordered_lane_ids
    }

    pub fn ordered_lane_binding_roots(&self) -> &[RootV1] {
        &self.ordered_lane_binding_roots
    }

    pub fn ordered_lane_journal_roots(&self) -> &[RootV1] {
        &self.ordered_lane_journal_roots
    }

    pub fn route_journal_root(&self) -> &RootV1 {
        &self.route_journal_root
    }

    pub fn route_journal_digest(&self) -> &RootV1 {
        &self.route_journal_digest
    }

    pub fn expected_image_id(&self) -> &RootV1 {
        &self.expected_image_id
    }

    pub fn receipt_digest(&self) -> &RootV1 {
        &self.receipt_digest
    }

    pub fn receipt_kind(&self) -> ReceiptKindV1 {
        self.receipt_kind
    }

    pub fn assumption_root(&self) -> AbiResultV1<RootV1> {
        derive_route_composition_assumption_root_v1(
            &self.profile_id,
            &self.route_release_id,
            &self.command_occurrence_id,
            self.writer_epoch,
            &self.route_journal_root,
            &self.route_journal_digest,
            &self.expected_image_id,
        )
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "verified-route-composition-v1",
            &VerifiedRouteCompositionContentV1 {
                schema: VERIFIED_ROUTE_COMPOSITION_SCHEMA_V1,
                profile_id: &self.profile_id,
                route_release_id: &self.route_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                writer_epoch: self.writer_epoch,
                ordered_lane_ids: &self.ordered_lane_ids,
                ordered_lane_binding_roots: &self.ordered_lane_binding_roots,
                ordered_lane_journal_roots: &self.ordered_lane_journal_roots,
                route_journal_root: &self.route_journal_root,
                route_journal_digest: &self.route_journal_digest,
                expected_image_id: &self.expected_image_id,
                receipt_digest: &self.receipt_digest,
                receipt_kind: self.receipt_kind,
            },
        )
    }
}

fn sha256_root_v1(bytes: &[u8], field: &'static str) -> AbiResultV1<RootV1> {
    RootV1::parse(format!("0x{}", hash_bytes_sha256_v1(bytes)), field, false)
}

fn require_route_shape_v1(
    candidate: &RouteCompositionReceiptCandidateV1<'_>,
    route: &RouteReleaseV1,
) -> AbiResultV1<()> {
    if candidate.lane_journals.len() != route.ordered_lanes.len() {
        return Err(AbiErrorV1::InvalidBinding(
            "route composition lane journal count",
        ));
    }
    if candidate.verified_lanes.len() != route.ordered_lanes.len() {
        return Err(AbiErrorV1::InvalidBinding(
            "route composition lane witness count",
        ));
    }
    if candidate
        .lane_journals
        .iter()
        .map(|journal| journal.lane_id)
        .ne(route.ordered_lanes.iter().copied())
    {
        return Err(AbiErrorV1::InvalidOrder("route composition lane journals"));
    }
    if candidate
        .verified_lanes
        .iter()
        .map(VerifiedLaneCompositionV1::lane_id)
        .ne(route.ordered_lanes.iter().copied())
    {
        return Err(AbiErrorV1::InvalidOrder("route composition lane witnesses"));
    }
    Ok(())
}

fn require_route_journal_binding_v1(
    candidate: &RouteCompositionReceiptCandidateV1<'_>,
    route: &RouteReleaseV1,
) -> AbiResultV1<()> {
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let journal = candidate.route_journal;
    let lane_roots = candidate
        .lane_journals
        .iter()
        .map(LaneCompositionJournalV1::journal_root)
        .collect::<AbiResultV1<Vec<_>>>()?;
    if candidate.occurrence.profile_root != candidate.profile.profile_id
        || journal.chain_id != candidate.occurrence.chain_id
        || journal.deployment_root != candidate.occurrence.deployment_root
        || journal.profile_root != candidate.profile.profile_id
        || journal.route_release_id != route.route_release_id
        || journal.command_occurrence_id != occurrence_id
        || journal.ordered_lane_journal_roots != lane_roots
        || journal.pre_state_root != candidate.occurrence.pre_state_root
        || journal.writer_epoch != candidate.profile.authority_epoch
    {
        return Err(AbiErrorV1::InvalidBinding(
            "route composition exact route journal",
        ));
    }
    if candidate.lane_journals.len() == 1 {
        let lane = &candidate.lane_journals[0];
        if journal.effect_plan_root != lane.effect_plan_root
            || journal.terminal_obligations_root != lane.terminal_obligations_root
        {
            return Err(AbiErrorV1::InvalidBinding(
                "route composition single lane outputs",
            ));
        }
    }
    Ok(())
}

fn require_verified_lane_bindings_v1(
    candidate: &RouteCompositionReceiptCandidateV1<'_>,
    route: &RouteReleaseV1,
) -> AbiResultV1<()> {
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    for ((lane_id, lane_journal), verified_lane) in route
        .ordered_lanes
        .iter()
        .zip(candidate.lane_journals)
        .zip(candidate.verified_lanes)
    {
        let coordinator =
            candidate
                .coordinators
                .release_for(*lane_id)
                .ok_or(AbiErrorV1::InvalidBinding(
                    "route composition coordinator release",
                ))?;
        let lane_journal_bytes = canonical_bytes_v1(lane_journal)?;
        let lane_journal_digest = sha256_root_v1(&lane_journal_bytes, "route lane journal digest")?;
        if verified_lane.profile_id() != &candidate.profile.profile_id
            || verified_lane.route_release_id() != &route.route_release_id
            || verified_lane.lane_id() != *lane_id
            || verified_lane.coordinator_release_id() != &coordinator.coordinator_release_id
            || verified_lane.command_occurrence_id() != &occurrence_id
            || verified_lane.writer_epoch() != candidate.profile.authority_epoch
            || verified_lane.lane_journal_root() != &lane_journal.journal_root()?
            || verified_lane.lane_journal_digest() != &lane_journal_digest
            || verified_lane.expected_image_id() != &coordinator.guest_image_id
            || verified_lane.receipt_kind() != ReceiptKindV1::SUCCINCT
        {
            return Err(AbiErrorV1::InvalidBinding(
                "route composition exact lane witness",
            ));
        }
    }
    Ok(())
}

fn require_exact_route_composition_binding_v1<'a>(
    candidate: &'a RouteCompositionReceiptCandidateV1<'a>,
) -> AbiResultV1<&'a RouteReleaseV1> {
    candidate.profile.validate_registries(
        candidate.lanes,
        candidate.coordinators,
        candidate.routes,
    )?;
    candidate.occurrence.validate()?;
    candidate.route_journal.validate()?;
    for lane_journal in candidate.lane_journals {
        lane_journal.validate()?;
    }
    if candidate.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding(
            "route composition active profile",
        ));
    }
    let route = candidate.routes.route_for_command(
        &candidate.occurrence.command_kind,
        Some(&candidate.occurrence.route_release_id),
    )?;
    require_route_shape_v1(candidate, route)?;
    require_route_journal_binding_v1(candidate, route)?;
    require_verified_lane_bindings_v1(candidate, route)?;
    Ok(route)
}

pub fn verify_route_composition_receipt_v1(
    candidate: RouteCompositionReceiptCandidateV1<'_>,
    receipt_verifier: &dyn RouteCompositionSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedRouteCompositionV1> {
    let route = require_exact_route_composition_binding_v1(&candidate)?;
    if candidate.receipt.receipt_kind != ReceiptKindV1::SUCCINCT {
        return Err(AbiErrorV1::InvalidBinding("route composition receipt kind"));
    }
    if candidate.receipt.receipt_bytes.is_empty() {
        return Err(AbiErrorV1::InvalidBounds("route composition receipt bytes"));
    }
    let journal_bytes = canonical_bytes_v1(candidate.route_journal)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("route composition canonical journal bytes"))?;
    if journal_len > route.max_journal_bytes {
        return Err(AbiErrorV1::InvalidBounds(
            "route composition canonical journal bytes",
        ));
    }
    let route_journal_digest =
        sha256_root_v1(&journal_bytes, "route composition canonical journal digest")?;
    let receipt_digest = sha256_root_v1(
        candidate.receipt.receipt_bytes,
        "route composition receipt digest",
    )?;
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt.receipt_bytes,
        &route.guest_image_id,
        &journal_bytes,
    )?;

    Ok(VerifiedRouteCompositionV1 {
        profile_id: candidate.profile.profile_id.clone(),
        route_release_id: route.route_release_id.clone(),
        command_occurrence_id: candidate.occurrence.occurrence_id()?,
        writer_epoch: candidate.profile.authority_epoch,
        ordered_lane_ids: route.ordered_lanes.clone(),
        ordered_lane_binding_roots: candidate
            .verified_lanes
            .iter()
            .map(VerifiedLaneCompositionV1::binding_root)
            .collect::<AbiResultV1<Vec<_>>>()?,
        ordered_lane_journal_roots: candidate
            .lane_journals
            .iter()
            .map(LaneCompositionJournalV1::journal_root)
            .collect::<AbiResultV1<Vec<_>>>()?,
        route_journal_root: candidate.route_journal.journal_root()?,
        route_journal_digest,
        expected_image_id: route.guest_image_id.clone(),
        receipt_digest,
        receipt_kind: candidate.receipt.receipt_kind,
    })
}
