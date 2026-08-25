use serde::Serialize;

use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::lane_module_receipt_verification::VerifiedLaneModuleTransitionV1;
use crate::perps_margin_lane_coordinator::{
    compose_perps_margin_lane_single_v1, PerpsMarginLaneCompositionCandidateV1,
    PerpsMarginLaneCompositionResultV1, PerpsMarginLaneCoordinatorContextV1,
    PerpsMarginLaneProjectionV1,
};
use crate::perps_margin_types::PerpsMarginPrivatePortV1;
use crate::proof::{EconomicCommandOccurrenceV1, LaneModuleTransitionJournalV1, ReceiptKindV1};
use crate::receipt_backed_asset_lane_composition::LaneCompositionAuthorityLevelV1;
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneIdV1, LaneRegistryV1,
    ProfileStatusV1, ReleaseStatusV1, RouteRegistryV1,
};

pub const RECEIPT_BACKED_PERPS_MARGIN_LANE_COMPOSITION_SCHEMA_V1: &str =
    "zenodex/receipt-backed-perps-margin-lane-composition/v1";

#[derive(Clone, Copy, Debug)]
pub struct ReceiptBackedPerpsMarginLaneCompositionCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub coordinator_context: &'a PerpsMarginLaneCoordinatorContextV1,
    pub module_journal: &'a LaneModuleTransitionJournalV1,
    pub private_port: &'a PerpsMarginPrivatePortV1,
    pub pre_state: &'a PerpsMarginLaneProjectionV1,
    pub post_state: &'a PerpsMarginLaneProjectionV1,
    pub module_effects: &'a GlobalEconomicEffectPlanV1,
    pub verified_module: &'a VerifiedLaneModuleTransitionV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ReceiptBackedPerpsMarginLaneCompositionV1 {
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
struct ReceiptBackedPerpsMarginLaneCompositionContentV1<'a> {
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

impl ReceiptBackedPerpsMarginLaneCompositionV1 {
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
            "receipt-backed-perps-margin-lane-composition-v1",
            &ReceiptBackedPerpsMarginLaneCompositionContentV1 {
                schema: RECEIPT_BACKED_PERPS_MARGIN_LANE_COMPOSITION_SCHEMA_V1,
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
        "receipt-backed perps module journal digest",
        false,
    )
}

fn validate_candidate_surfaces_v1(
    candidate: &ReceiptBackedPerpsMarginLaneCompositionCandidateV1<'_>,
) -> AbiResultV1<()> {
    candidate.profile.validate_registries(
        candidate.lanes,
        candidate.coordinators,
        candidate.routes,
    )?;
    candidate.occurrence.validate()?;
    candidate.coordinator_context.validate()?;
    candidate.module_journal.validate()?;
    candidate.private_port.validate()?;
    candidate.pre_state.validate()?;
    candidate.post_state.validate()?;
    candidate.module_effects.validate()?;
    Ok(())
}

fn require_domain_bindings_v1(
    candidate: &ReceiptBackedPerpsMarginLaneCompositionCandidateV1<'_>,
    route: &crate::release::RouteReleaseV1,
    coordinator: &crate::release::LaneCoordinatorReleaseV1,
) -> AbiResultV1<()> {
    let context = candidate.coordinator_context;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let journal = candidate.module_journal;
    if context.coordinator_release_id != coordinator.coordinator_release_id
        || candidate.occurrence.profile_root != candidate.profile.profile_id
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
            "receipt-backed perps domain bindings",
        ));
    }
    Ok(())
}

fn require_compatible_module_v1(
    candidate: &ReceiptBackedPerpsMarginLaneCompositionCandidateV1<'_>,
    route: &crate::release::RouteReleaseV1,
) -> AbiResultV1<()> {
    let compatible_modules = &candidate.coordinator_context.compatible_modules;
    if compatible_modules.len() != 1
        || compatible_modules[0].module_release_id != route.module_release_ids[0]
        || compatible_modules[0].module_schema != candidate.private_port.producer_module_schema
    {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps compatible module set",
        ));
    }
    Ok(())
}

fn require_profile_route_bindings_v1<'a>(
    candidate: &'a ReceiptBackedPerpsMarginLaneCompositionCandidateV1<'a>,
) -> AbiResultV1<&'a crate::release::RouteReleaseV1> {
    validate_candidate_surfaces_v1(candidate)?;
    if candidate.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps active profile",
        ));
    }
    let route = candidate.routes.route_for_command(
        &candidate.occurrence.command_kind,
        Some(&candidate.occurrence.route_release_id),
    )?;
    if route.ordered_lanes.as_slice() != [LaneIdV1::PERPS_MARKET]
        || route.module_release_ids.len() != 1
    {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps single lane route",
        ));
    }
    let coordinator = candidate
        .coordinators
        .release_for(LaneIdV1::PERPS_MARKET)
        .ok_or(AbiErrorV1::InvalidBinding(
            "receipt-backed perps coordinator registry",
        ))?;
    if coordinator.status != ReleaseStatusV1::ACTIVE_NEW || !coordinator.accepts_new_objects {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps selected coordinator active",
        ));
    }
    require_domain_bindings_v1(candidate, route, coordinator)?;
    require_compatible_module_v1(candidate, route)?;
    Ok(route)
}

fn require_verified_module_binding_v1(
    candidate: &ReceiptBackedPerpsMarginLaneCompositionCandidateV1<'_>,
) -> AbiResultV1<()> {
    let verified = candidate.verified_module;
    if verified.receipt_kind() != ReceiptKindV1::SUCCINCT {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps module receipt kind",
        ));
    }
    if verified.command_occurrence_id() != &candidate.occurrence.occurrence_id()? {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps module occurrence",
        ));
    }
    if verified.module_journal_root() != &candidate.module_journal.journal_root()? {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps module journal root",
        ));
    }
    let journal_bytes = canonical_bytes_v1(candidate.module_journal)?;
    if verified.module_journal_digest() != &sha256_root_v1(&journal_bytes)? {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps module journal digest",
        ));
    }
    let release =
        candidate
            .lanes
            .release_for(LaneIdV1::PERPS_MARKET)
            .ok_or(AbiErrorV1::InvalidBinding(
                "receipt-backed perps module release",
            ))?;
    if verified.expected_image_id() != &release.guest_image_id {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps module image",
        ));
    }
    Ok(())
}

pub fn compose_receipt_backed_perps_margin_lane_single_v1(
    candidate: ReceiptBackedPerpsMarginLaneCompositionCandidateV1<'_>,
) -> AbiResultV1<ReceiptBackedPerpsMarginLaneCompositionV1> {
    let route = require_profile_route_bindings_v1(&candidate)?;
    require_verified_module_binding_v1(&candidate)?;
    let composition_candidate = PerpsMarginLaneCompositionCandidateV1 {
        context: candidate.coordinator_context.clone(),
        module_journal: candidate.module_journal.clone(),
        private_port: candidate.private_port.clone(),
        pre_state: candidate.pre_state.clone(),
        post_state: candidate.post_state.clone(),
        module_effects: candidate.module_effects.clone(),
    };
    let result = compose_perps_margin_lane_single_v1(&composition_candidate)?;
    let accepted = match result {
        PerpsMarginLaneCompositionResultV1::Accepted(value) => value,
        PerpsMarginLaneCompositionResultV1::Rejected(_) => {
            return Err(AbiErrorV1::InvalidBinding(
                "receipt-backed perps lane composition rejected",
            ));
        }
    };
    if accepted.lane_journal.ordered_module_journal_roots
        != [candidate.verified_module.module_journal_root().clone()]
    {
        return Err(AbiErrorV1::InvalidBinding(
            "receipt-backed perps ordered module roots",
        ));
    }

    Ok(ReceiptBackedPerpsMarginLaneCompositionV1 {
        authority_level: LaneCompositionAuthorityLevelV1::RECEIPT_BACKED_STRUCTURAL_ONLY,
        profile_id: candidate.profile.profile_id.clone(),
        route_release_id: route.route_release_id.clone(),
        lane_id: LaneIdV1::PERPS_MARKET,
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
