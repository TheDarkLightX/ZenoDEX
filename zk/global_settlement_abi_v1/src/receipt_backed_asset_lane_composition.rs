use serde::Serialize;

use crate::asset_lane_coordinator::compose_asset_lane_single_v1;
use crate::asset_lane_projection::{
    AssetLaneCompositionResultV1, AssetLaneCoordinatorContextV1, AssetLanePrivatePortV1,
};
use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::lane_module_receipt_verification::VerifiedLaneModuleTransitionV1;
use crate::proof::{EconomicCommandOccurrenceV1, LaneModuleTransitionJournalV1, ReceiptKindV1};
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneIdV1, LaneRegistryV1,
    ProfileStatusV1, ReleaseStatusV1, RouteRegistryV1,
};

pub const RECEIPT_BACKED_ASSET_LANE_COMPOSITION_SCHEMA_V1: &str =
    "zenodex/receipt-backed-asset-lane-composition/v1";

#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum LaneCompositionAuthorityLevelV1 {
    RECEIPT_BACKED_STRUCTURAL_ONLY,
}

#[derive(Clone, Copy, Debug)]
pub struct ReceiptBackedAssetLaneCompositionCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub coordinator_context: &'a AssetLaneCoordinatorContextV1,
    pub module_journal: &'a LaneModuleTransitionJournalV1,
    pub private_port: &'a AssetLanePrivatePortV1,
    pub module_effects: &'a GlobalEconomicEffectPlanV1,
    pub verified_module: &'a VerifiedLaneModuleTransitionV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReceiptBackedAssetLaneCompositionV1 {
    authority_level: LaneCompositionAuthorityLevelV1,
    profile_id: RootV1,
    route_release_id: RootV1,
    lane_id: LaneIdV1,
    declared_coordinator_release_id: RootV1,
    command_occurrence_id: RootV1,
    verified_module_binding_root: RootV1,
    module_receipt_digest: RootV1,
    module_journal_digest: RootV1,
    lane_journal_root: RootV1,
    pre_lane_root: RootV1,
    post_lane_root: RootV1,
    effect_plan_root: RootV1,
    terminal_obligations_root: RootV1,
}

#[derive(Serialize)]
struct ReceiptBackedAssetLaneCompositionContentV1<'a> {
    schema: &'static str,
    authority_level: LaneCompositionAuthorityLevelV1,
    profile_id: &'a RootV1,
    route_release_id: &'a RootV1,
    lane_id: LaneIdV1,
    declared_coordinator_release_id: &'a RootV1,
    command_occurrence_id: &'a RootV1,
    verified_module_binding_root: &'a RootV1,
    module_receipt_digest: &'a RootV1,
    module_journal_digest: &'a RootV1,
    lane_journal_root: &'a RootV1,
    pre_lane_root: &'a RootV1,
    post_lane_root: &'a RootV1,
    effect_plan_root: &'a RootV1,
    terminal_obligations_root: &'a RootV1,
}

impl ReceiptBackedAssetLaneCompositionV1 {
    pub fn authority_level(&self) -> LaneCompositionAuthorityLevelV1 {
        self.authority_level
    }

    pub fn profile_id(&self) -> &RootV1 {
        &self.profile_id
    }

    pub fn route_release_id(&self) -> &RootV1 {
        &self.route_release_id
    }

    pub fn lane_id(&self) -> LaneIdV1 {
        self.lane_id
    }

    pub fn declared_coordinator_release_id(&self) -> &RootV1 {
        &self.declared_coordinator_release_id
    }

    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.command_occurrence_id
    }

    pub fn verified_module_binding_root(&self) -> &RootV1 {
        &self.verified_module_binding_root
    }

    pub fn module_receipt_digest(&self) -> &RootV1 {
        &self.module_receipt_digest
    }

    pub fn module_journal_digest(&self) -> &RootV1 {
        &self.module_journal_digest
    }

    pub fn lane_journal_root(&self) -> &RootV1 {
        &self.lane_journal_root
    }

    pub fn pre_lane_root(&self) -> &RootV1 {
        &self.pre_lane_root
    }

    pub fn post_lane_root(&self) -> &RootV1 {
        &self.post_lane_root
    }

    pub fn effect_plan_root(&self) -> &RootV1 {
        &self.effect_plan_root
    }

    pub fn terminal_obligations_root(&self) -> &RootV1 {
        &self.terminal_obligations_root
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        hash_global_v1(
            "receipt-backed-asset-lane-composition-v1",
            &ReceiptBackedAssetLaneCompositionContentV1 {
                schema: RECEIPT_BACKED_ASSET_LANE_COMPOSITION_SCHEMA_V1,
                authority_level: self.authority_level,
                profile_id: &self.profile_id,
                route_release_id: &self.route_release_id,
                lane_id: self.lane_id,
                declared_coordinator_release_id: &self.declared_coordinator_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                verified_module_binding_root: &self.verified_module_binding_root,
                module_receipt_digest: &self.module_receipt_digest,
                module_journal_digest: &self.module_journal_digest,
                lane_journal_root: &self.lane_journal_root,
                pre_lane_root: &self.pre_lane_root,
                post_lane_root: &self.post_lane_root,
                effect_plan_root: &self.effect_plan_root,
                terminal_obligations_root: &self.terminal_obligations_root,
            },
        )
    }
}

fn sha256_root_v1(bytes: &[u8]) -> AbiResultV1<RootV1> {
    RootV1::parse(
        format!("0x{}", hash_bytes_sha256_v1(bytes)),
        "receipt-backed module journal digest",
        false,
    )
}

fn require_profile_route_bindings_v1<'a>(
    candidate: &'a ReceiptBackedAssetLaneCompositionCandidateV1<'a>,
) -> AbiResultV1<&'a crate::release::RouteReleaseV1> {
    candidate.profile.validate_registries(
        candidate.lanes,
        candidate.coordinators,
        candidate.routes,
    )?;
    candidate.occurrence.validate()?;
    candidate.coordinator_context.validate()?;
    candidate.module_journal.validate()?;
    candidate.private_port.validate()?;
    candidate.module_effects.validate()?;
    if candidate.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed lane active profile",
        ));
    }
    let route = candidate.routes.route_for_command(
        &candidate.occurrence.command_kind,
        Some(&candidate.occurrence.route_release_id),
    )?;
    if route.ordered_lanes.as_slice() != [LaneIdV1::ASSET_TRANSFER] {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed single asset lane route",
        ));
    }
    let context = candidate.coordinator_context;
    let coordinator = candidate
        .coordinators
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .ok_or(AbiErrorV1::InvalidBinding(
            "receipt-backed lane coordinator registry",
        ))?;
    if coordinator.status != ReleaseStatusV1::ACTIVE_NEW || !coordinator.accepts_new_objects {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed lane selected coordinator active",
        ));
    }
    if context.coordinator_release_id != coordinator.coordinator_release_id {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed lane selected coordinator release",
        ));
    }
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let journal = candidate.module_journal;
    if candidate.occurrence.profile_root != candidate.profile.profile_id
        || context.profile_root != candidate.profile.profile_id
        || context.chain_id != candidate.occurrence.chain_id
        || context.deployment_root != candidate.occurrence.deployment_root
        || context.command_occurrence_id != occurrence_id
        || journal.chain_id != candidate.occurrence.chain_id
        || journal.deployment_root != candidate.occurrence.deployment_root
        || journal.profile_root != candidate.profile.profile_id
        || journal.command_occurrence_id != occurrence_id
        || journal.module_release_id != route.module_release_ids[0]
        || context.writer_epoch != candidate.profile.authority_epoch
        || journal.writer_epoch != candidate.profile.authority_epoch
    {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed lane domain bindings",
        ));
    }
    if context.compatible_modules.len() != 1
        || context.compatible_modules[0].module_release_id != route.module_release_ids[0]
        || context.compatible_modules[0].module_schema
            != candidate.private_port.producer_module_schema
    {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed lane compatible module set",
        ));
    }
    Ok(route)
}

fn require_verified_module_binding_v1(
    candidate: &ReceiptBackedAssetLaneCompositionCandidateV1<'_>,
) -> AbiResultV1<()> {
    let verified = candidate.verified_module;
    if verified.receipt_kind() != ReceiptKindV1::SUCCINCT {
        return Err(AbiErrorV1::InvalidBinding("verified module receipt kind"));
    }
    if verified.command_occurrence_id() != &candidate.occurrence.occurrence_id()? {
        return Err(AbiErrorV1::InvalidBinding("verified module occurrence"));
    }
    if verified.module_journal_root() != &candidate.module_journal.journal_root()? {
        return Err(AbiErrorV1::InvalidBinding("verified module journal root"));
    }
    let journal_bytes = canonical_bytes_v1(candidate.module_journal)?;
    if verified.module_journal_digest() != &sha256_root_v1(&journal_bytes)? {
        return Err(AbiErrorV1::InvalidBinding("verified module journal digest"));
    }
    let release = candidate
        .lanes
        .release_for(LaneIdV1::ASSET_TRANSFER)
        .ok_or(AbiErrorV1::InvalidBinding("verified module lane release"))?;
    if verified.expected_image_id() != &release.guest_image_id {
        return Err(AbiErrorV1::InvalidBinding("verified module image"));
    }
    Ok(())
}

pub fn compose_receipt_backed_asset_lane_single_v1(
    candidate: ReceiptBackedAssetLaneCompositionCandidateV1<'_>,
) -> AbiResultV1<ReceiptBackedAssetLaneCompositionV1> {
    let route = require_profile_route_bindings_v1(&candidate)?;
    require_verified_module_binding_v1(&candidate)?;
    let result = compose_asset_lane_single_v1(
        candidate.coordinator_context,
        candidate.module_journal,
        candidate.private_port,
        candidate.module_effects,
    )?;
    let accepted = match result {
        AssetLaneCompositionResultV1::Accepted(accepted) => accepted,
        AssetLaneCompositionResultV1::Rejected(rejected) => {
            return Err(AbiErrorV1::InvalidBinding(rejected.code.binding_label()));
        }
    };
    if accepted.lane_journal.ordered_module_journal_roots
        != [candidate.verified_module.module_journal_root().clone()]
    {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed lane ordered module roots",
        ));
    }

    Ok(ReceiptBackedAssetLaneCompositionV1 {
        authority_level: LaneCompositionAuthorityLevelV1::RECEIPT_BACKED_STRUCTURAL_ONLY,
        profile_id: candidate.profile.profile_id.clone(),
        route_release_id: route.route_release_id.clone(),
        lane_id: LaneIdV1::ASSET_TRANSFER,
        declared_coordinator_release_id: candidate
            .coordinator_context
            .coordinator_release_id
            .clone(),
        command_occurrence_id: candidate.occurrence.occurrence_id()?,
        verified_module_binding_root: candidate.verified_module.binding_root()?,
        module_receipt_digest: candidate.verified_module.receipt_digest().clone(),
        module_journal_digest: candidate.verified_module.module_journal_digest().clone(),
        lane_journal_root: accepted.lane_journal.journal_root()?,
        pre_lane_root: accepted.lane_journal.pre_lane_root.clone(),
        post_lane_root: accepted.lane_journal.post_lane_root.clone(),
        effect_plan_root: accepted.lane_journal.effect_plan_root.clone(),
        terminal_obligations_root: accepted.lane_journal.terminal_obligations_root.clone(),
    })
}
