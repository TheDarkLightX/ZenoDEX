use serde::Serialize;

use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::proof::{EconomicCommandOccurrenceV1, LaneCompositionJournalV1, ReceiptKindV1};
use crate::receipt_backed_asset_lane_composition::ReceiptBackedAssetLaneCompositionV1;
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneCoordinatorReleaseV1, LaneIdV1,
    LaneRegistryV1, ProfileStatusV1, ReleaseStatusV1, RouteRegistryV1,
};

pub const VERIFIED_LANE_COMPOSITION_SCHEMA_V1: &str = "zenodex/verified-lane-composition/v1";

/// Cryptographic verifier port selected by the settlement shell.
///
/// The ABI supplies the profile-selected coordinator image and exact canonical
/// lane journal bytes. The implementation must reject invalid receipts.
pub trait LaneCompositionSuccinctReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()>;
}

#[derive(Clone, Copy, Debug)]
pub struct LaneCompositionReceiptEnvelopeV1<'a> {
    pub receipt_kind: ReceiptKindV1,
    pub receipt_bytes: &'a [u8],
}

#[derive(Clone, Copy, Debug)]
pub struct LaneCompositionReceiptCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub structural_composition: &'a ReceiptBackedAssetLaneCompositionV1,
    pub lane_journal: &'a LaneCompositionJournalV1,
    pub receipt: LaneCompositionReceiptEnvelopeV1<'a>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedLaneCompositionV1 {
    profile_id: RootV1,
    route_release_id: RootV1,
    lane_id: LaneIdV1,
    coordinator_release_id: RootV1,
    command_occurrence_id: RootV1,
    writer_epoch: u64,
    structural_composition_root: RootV1,
    lane_journal_root: RootV1,
    lane_journal_digest: RootV1,
    expected_image_id: RootV1,
    receipt_digest: RootV1,
    receipt_kind: ReceiptKindV1,
}

#[derive(Serialize)]
struct VerifiedLaneCompositionContentV1<'a> {
    schema: &'static str,
    profile_id: &'a RootV1,
    route_release_id: &'a RootV1,
    lane_id: LaneIdV1,
    coordinator_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    writer_epoch: u64,
    structural_composition_root: &'a RootV1,
    lane_journal_root: &'a RootV1,
    lane_journal_digest: &'a RootV1,
    expected_image_id: &'a RootV1,
    receipt_digest: &'a RootV1,
    receipt_kind: ReceiptKindV1,
}

impl VerifiedLaneCompositionV1 {
    pub fn profile_id(&self) -> &RootV1 {
        &self.profile_id
    }

    pub fn route_release_id(&self) -> &RootV1 {
        &self.route_release_id
    }

    pub fn lane_id(&self) -> LaneIdV1 {
        self.lane_id
    }

    pub fn coordinator_release_id(&self) -> &RootV1 {
        &self.coordinator_release_id
    }

    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.command_occurrence_id
    }

    pub fn writer_epoch(&self) -> u64 {
        self.writer_epoch
    }

    pub fn structural_composition_root(&self) -> &RootV1 {
        &self.structural_composition_root
    }

    pub fn lane_journal_root(&self) -> &RootV1 {
        &self.lane_journal_root
    }

    pub fn lane_journal_digest(&self) -> &RootV1 {
        &self.lane_journal_digest
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

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "verified-lane-composition-v1",
            &VerifiedLaneCompositionContentV1 {
                schema: VERIFIED_LANE_COMPOSITION_SCHEMA_V1,
                profile_id: &self.profile_id,
                route_release_id: &self.route_release_id,
                lane_id: self.lane_id,
                coordinator_release_id: &self.coordinator_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                writer_epoch: self.writer_epoch,
                structural_composition_root: &self.structural_composition_root,
                lane_journal_root: &self.lane_journal_root,
                lane_journal_digest: &self.lane_journal_digest,
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

fn require_exact_lane_composition_binding_v1<'a>(
    candidate: &'a LaneCompositionReceiptCandidateV1<'a>,
) -> AbiResultV1<&'a LaneCoordinatorReleaseV1> {
    candidate.profile.validate_registries(
        candidate.lanes,
        candidate.coordinators,
        candidate.routes,
    )?;
    candidate.occurrence.validate()?;
    candidate.lane_journal.validate()?;
    if candidate.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding(
            "lane composition active profile",
        ));
    }
    let route = candidate.routes.route_for_command(
        &candidate.occurrence.command_kind,
        Some(&candidate.occurrence.route_release_id),
    )?;
    if route.ordered_lanes.as_slice() != [LaneIdV1::ASSET_TRANSFER] {
        return Err(AbiErrorV1::InvalidBinding(
            "lane composition single asset route",
        ));
    }
    let coordinator = candidate
        .coordinators
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .ok_or(AbiErrorV1::InvalidBinding(
            "lane composition coordinator registry",
        ))?;
    if coordinator.status != ReleaseStatusV1::ACTIVE_NEW || !coordinator.accepts_new_objects {
        return Err(AbiErrorV1::InvalidBinding(
            "lane composition selected coordinator active",
        ));
    }
    require_exact_lane_journal_bindings_v1(candidate, coordinator, &route.route_release_id)?;
    Ok(coordinator)
}

fn require_exact_lane_journal_bindings_v1(
    candidate: &LaneCompositionReceiptCandidateV1<'_>,
    coordinator: &LaneCoordinatorReleaseV1,
    route_release_id: &RootV1,
) -> AbiResultV1<()> {
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let structural = candidate.structural_composition;
    let journal = candidate.lane_journal;
    if candidate.occurrence.profile_root != candidate.profile.profile_id
        || structural.profile_id() != &candidate.profile.profile_id
        || structural.route_release_id() != route_release_id
        || structural.lane_id() != LaneIdV1::ASSET_TRANSFER
        || structural.declared_coordinator_release_id() != &coordinator.coordinator_release_id
        || structural.command_occurrence_id() != &occurrence_id
        || journal.chain_id != candidate.occurrence.chain_id
        || journal.deployment_root != candidate.occurrence.deployment_root
        || journal.profile_root != candidate.profile.profile_id
        || journal.lane_id != LaneIdV1::ASSET_TRANSFER
        || journal.coordinator_release_id != coordinator.coordinator_release_id
        || journal.command_occurrence_id != occurrence_id
        || journal.journal_root()? != *structural.lane_journal_root()
        || journal.pre_lane_root != *structural.pre_lane_root()
        || journal.post_lane_root != *structural.post_lane_root()
        || journal.effect_plan_root != *structural.effect_plan_root()
        || journal.terminal_obligations_root != *structural.terminal_obligations_root()
        || journal.writer_epoch != candidate.profile.authority_epoch
    {
        return Err(AbiErrorV1::InvalidBinding(
            "lane composition exact journal bindings",
        ));
    }
    Ok(())
}

pub fn verify_asset_lane_composition_receipt_v1(
    candidate: LaneCompositionReceiptCandidateV1<'_>,
    receipt_verifier: &dyn LaneCompositionSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedLaneCompositionV1> {
    let coordinator = require_exact_lane_composition_binding_v1(&candidate)?;
    if candidate.receipt.receipt_kind != ReceiptKindV1::SUCCINCT {
        return Err(AbiErrorV1::InvalidBinding("lane composition receipt kind"));
    }
    if candidate.receipt.receipt_bytes.is_empty() {
        return Err(AbiErrorV1::InvalidBounds("lane composition receipt bytes"));
    }
    let journal_bytes = canonical_bytes_v1(candidate.lane_journal)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("lane composition canonical journal bytes"))?;
    if journal_len > coordinator.max_journal_bytes {
        return Err(AbiErrorV1::InvalidBounds(
            "lane composition canonical journal bytes",
        ));
    }
    let lane_journal_digest =
        sha256_root_v1(&journal_bytes, "lane composition canonical journal digest")?;
    let receipt_digest = sha256_root_v1(
        candidate.receipt.receipt_bytes,
        "lane composition receipt digest",
    )?;
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt.receipt_bytes,
        &coordinator.guest_image_id,
        &journal_bytes,
    )?;

    Ok(VerifiedLaneCompositionV1 {
        profile_id: candidate.profile.profile_id.clone(),
        route_release_id: candidate.structural_composition.route_release_id().clone(),
        lane_id: LaneIdV1::ASSET_TRANSFER,
        coordinator_release_id: coordinator.coordinator_release_id.clone(),
        command_occurrence_id: candidate.occurrence.occurrence_id()?,
        writer_epoch: candidate.profile.authority_epoch,
        structural_composition_root: candidate.structural_composition.binding_root()?,
        lane_journal_root: candidate.lane_journal.journal_root()?,
        lane_journal_digest,
        expected_image_id: coordinator.guest_image_id.clone(),
        receipt_digest,
        receipt_kind: candidate.receipt.receipt_kind,
    })
}
