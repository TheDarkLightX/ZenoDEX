use crate::canonical::{AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneCoordinatorReleaseV1, LaneIdV1,
    LaneModuleReleaseV1, LaneRegistryV1, ProfileStatusV1, ReleaseStatusV1, RouteRegistryV1,
    RouteReleaseV1,
};
use crate::zdex_purchase_burn_receipt_verification::{
    VerifiedZDEXBurnV1, ZDEXLaneReceiptEnvelopeV1, ZDEXLaneSuccinctReceiptVerifierV1,
    ZDEXVerifiedLaneExpectationV1,
};
use crate::zdex_purchase_burn_types::{
    zdex_amm_purchase_port_schema_root_v1, zdex_burn_port_schema_root_v1,
    AMM_PURCHASE_OUTPUT_ROLE_V1, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1, ZDEX_BURN_INPUT_ROLE_V1,
};
use crate::zdex_tokenomics_lane_coordinator::{
    compose_zdex_tokenomics_burn_lane_v1, ZDEXTokenomicsBurnLaneCandidateV1,
};
use crate::zdex_tokenomics_lane_receipt_common::{
    verify_and_construct_zdex_tokenomics_lane_v1, VerifiedZDEXTokenomicsLaneV1,
    ZDEXTokenomicsCoordinatorReceiptExpectationV1, ZDEXTokenomicsLaneBindingV1,
};
use crate::zdex_tokenomics_lane_types::ZDEXTokenomicsLaneCompositionResultV1;

pub struct ZDEXTokenomicsLaneReceiptCandidateV1<'a> {
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub lane_candidate: ZDEXTokenomicsBurnLaneCandidateV1<'a>,
    pub verified_burn: &'a VerifiedZDEXBurnV1,
    pub receipt: &'a ZDEXLaneReceiptEnvelopeV1,
}

pub struct ZDEXTokenomicsProfileRegistriesV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
}

pub struct GovernedZDEXTokenomicsProfileV1<'a> {
    profile: &'a EconomicProfileSnapshotV1,
    route_release: &'a RouteReleaseV1,
    module_release: &'a LaneModuleReleaseV1,
    coordinator_release: &'a LaneCoordinatorReleaseV1,
}

fn registered_buyback_route_v1(routes: &RouteRegistryV1) -> AbiResultV1<&RouteReleaseV1> {
    routes
        .routes
        .iter()
        .find(|route| route.command_kind == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1)
        .ok_or(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics governed buyback route absent",
        ))
}

fn require_release_shapes_v1(governed: &GovernedZDEXTokenomicsProfileV1<'_>) -> AbiResultV1<()> {
    let route = governed.route_release;
    let module = governed.module_release;
    let coordinator = governed.coordinator_release;
    route.validate()?;
    module.validate()?;
    coordinator.validate()?;
    if route.status != ReleaseStatusV1::SHADOW
        || route.accepts_new_objects
        || route.ordered_lanes != [LaneIdV1::SPOT_LIQUIDITY, LaneIdV1::ZDEX_TOKENOMICS]
        || route.module_release_ids.get(1) != Some(&module.release_id)
        || route.dependency_roles
            != [
                AMM_PURCHASE_OUTPUT_ROLE_V1.to_owned(),
                ZDEX_BURN_INPUT_ROLE_V1.to_owned(),
            ]
        || route.port_schema_roots
            != [
                zdex_amm_purchase_port_schema_root_v1()?,
                zdex_burn_port_schema_root_v1()?,
            ]
    {
        return Err(AbiErrorV1::InvalidBinding("ZDEX tokenomics route shape"));
    }
    if module.status != ReleaseStatusV1::SHADOW
        || module.accepts_new_objects
        || module.lane_id != LaneIdV1::ZDEX_TOKENOMICS
        || !module
            .command_variants
            .iter()
            .any(|command| command == PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1)
    {
        return Err(AbiErrorV1::InvalidBinding("ZDEX tokenomics module release"));
    }
    if coordinator.status != ReleaseStatusV1::SHADOW
        || coordinator.accepts_new_objects
        || coordinator.lane_id != LaneIdV1::ZDEX_TOKENOMICS
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics coordinator release",
        ));
    }
    Ok(())
}

pub fn bind_zdex_tokenomics_shadow_profile_v1<'a>(
    expected_profile_id: &RootV1,
    expected_authority_epoch: u64,
    registries: ZDEXTokenomicsProfileRegistriesV1<'a>,
) -> AbiResultV1<GovernedZDEXTokenomicsProfileV1<'a>> {
    let ZDEXTokenomicsProfileRegistriesV1 {
        profile,
        lanes,
        coordinators,
        routes,
    } = registries;
    profile.validate()?;
    if &profile.profile_id != expected_profile_id {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics expected profile",
        ));
    }
    if profile.authority_epoch != expected_authority_epoch {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics expected authority epoch",
        ));
    }
    if profile.status != ProfileStatusV1::SHADOW {
        return Err(AbiErrorV1::InvalidBinding("ZDEX tokenomics profile status"));
    }
    profile.validate_registries(lanes, coordinators, routes)?;
    let governed = GovernedZDEXTokenomicsProfileV1 {
        profile,
        route_release: registered_buyback_route_v1(routes)?,
        module_release: lanes.release_for(LaneIdV1::ZDEX_TOKENOMICS).ok_or(
            AbiErrorV1::InvalidBinding("ZDEX tokenomics module release absent"),
        )?,
        coordinator_release: coordinators.release_for(LaneIdV1::ZDEX_TOKENOMICS).ok_or(
            AbiErrorV1::InvalidBinding("ZDEX tokenomics coordinator release absent"),
        )?,
    };
    require_release_shapes_v1(&governed)?;
    Ok(governed)
}

fn require_candidate_bindings_v1(
    candidate: &ZDEXTokenomicsLaneReceiptCandidateV1<'_>,
    governed: &GovernedZDEXTokenomicsProfileV1<'_>,
) -> AbiResultV1<RootV1> {
    candidate.occurrence.validate()?;
    candidate.lane_candidate.validate()?;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let context = candidate.lane_candidate.context;
    let burn = candidate.lane_candidate.burn_journal;
    let burn_matches = candidate.verified_burn.matches_route_input(
        burn,
        ZDEXVerifiedLaneExpectationV1 {
            route_release_id: &governed.route_release.route_release_id,
            occurrence_id: &occurrence_id,
            profile_root: &governed.profile.profile_id,
            writer_epoch: governed.profile.authority_epoch,
            journal_root: &burn.journal_root()?,
            effect_plan_root: &candidate.lane_candidate.module_effects.effect_plan_root()?,
        },
    )?;
    // Route admission owns the occurrence's global pre-root. The exact
    // coordinator receipt binds this lane's pre/post roots.
    if candidate.occurrence.profile_root != governed.profile.profile_id
        || candidate.occurrence.command_kind != governed.route_release.command_kind
        || candidate.occurrence.route_release_id != governed.route_release.route_release_id
        || context.chain_id != candidate.occurrence.chain_id
        || context.deployment_root != candidate.occurrence.deployment_root
        || context.profile_root != governed.profile.profile_id
        || context.writer_epoch != governed.profile.authority_epoch
        || context.coordinator_release_id != governed.coordinator_release.coordinator_release_id
        || context.route_release_id != governed.route_release.route_release_id
        || context.tokenomics_module_release_id != governed.module_release.release_id
        || context.command_occurrence_id != occurrence_id
        || context.issue_burn_policy_root != governed.route_release.issue_burn_policy_root
        || candidate.verified_burn.module_release_id() != &governed.module_release.release_id
        || candidate.verified_burn.expected_image_id() != &governed.module_release.guest_image_id
        || !burn_matches
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics governed candidate",
        ));
    }
    Ok(occurrence_id)
}

/// Run reference shadow admission through the supplied verifier port.
///
/// The returned marker carries no settlement authority. An authoritative shell
/// must pin the concrete verifier implementation instead of accepting a
/// caller-selected implementation of the verifier trait.
pub fn verify_zdex_tokenomics_lane_receipt_v1(
    candidate: ZDEXTokenomicsLaneReceiptCandidateV1<'_>,
    governed: &GovernedZDEXTokenomicsProfileV1<'_>,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedZDEXTokenomicsLaneV1> {
    let occurrence_id = require_candidate_bindings_v1(&candidate, governed)?;
    let module_journal_root = candidate.lane_candidate.module_journal.journal_root()?;
    let result = compose_zdex_tokenomics_burn_lane_v1(candidate.lane_candidate)?;
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(accepted) = result else {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics lane composition rejected",
        ));
    };
    verify_and_construct_zdex_tokenomics_lane_v1(
        candidate.receipt,
        &accepted.lane_journal,
        ZDEXTokenomicsCoordinatorReceiptExpectationV1 {
            route_release: governed.route_release,
            coordinator_release: governed.coordinator_release,
        },
        ZDEXTokenomicsLaneBindingV1 {
            profile_root: governed.profile.profile_id.clone(),
            route_release_id: governed.route_release.route_release_id.clone(),
            module_release_id: governed.module_release.release_id.clone(),
            command_occurrence_id: occurrence_id,
            writer_epoch: governed.profile.authority_epoch,
            module_journal_root,
            module_image_id: governed.module_release.guest_image_id.clone(),
        },
        verifier,
    )
}
