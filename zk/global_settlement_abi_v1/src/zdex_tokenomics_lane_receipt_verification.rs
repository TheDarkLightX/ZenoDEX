use serde::Serialize;

use crate::canonical::{canonical_bytes_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::{EconomicCommandOccurrenceV1, ReceiptKindV1};
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneCoordinatorReleaseV1, LaneIdV1,
    LaneModuleReleaseV1, LaneRegistryV1, ProfileStatusV1, ReleaseStatusV1, RouteRegistryV1,
    RouteReleaseV1,
};
use crate::zdex_purchase_burn_receipt_verification::{
    digest_root_v1, VerifiedZDEXBurnV1, ZDEXLaneReceiptEnvelopeV1,
    ZDEXLaneSuccinctReceiptVerifierV1, ZDEXVerifiedLaneExpectationV1,
};
use crate::zdex_purchase_burn_types::{
    zdex_amm_purchase_port_schema_root_v1, zdex_burn_port_schema_root_v1,
    AMM_PURCHASE_OUTPUT_ROLE_V1, PROTOCOL_BUY_AND_BURN_COMMAND_KIND_V1, ZDEX_BURN_INPUT_ROLE_V1,
};
use crate::zdex_tokenomics_lane_coordinator::{
    compose_zdex_tokenomics_burn_lane_v1, ZDEXTokenomicsBurnLaneCandidateV1,
};
use crate::zdex_tokenomics_lane_types::ZDEXTokenomicsLaneCompositionResultV1;

pub const VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1: &str =
    "zenodex/verified-zdex-tokenomics-lane/v1";

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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedZDEXTokenomicsLaneV1 {
    profile_root: RootV1,
    route_release_id: RootV1,
    module_release_id: RootV1,
    coordinator_release_id: RootV1,
    command_occurrence_id: RootV1,
    writer_epoch: u64,
    module_journal_root: RootV1,
    lane_journal_root: RootV1,
    lane_journal_digest: RootV1,
    pre_lane_root: RootV1,
    post_lane_root: RootV1,
    effect_plan_root: RootV1,
    module_image_id: RootV1,
    expected_image_id: RootV1,
    receipt_digest: RootV1,
    receipt_kind: ReceiptKindV1,
}

impl VerifiedZDEXTokenomicsLaneV1 {
    pub fn profile_root(&self) -> &RootV1 {
        &self.profile_root
    }
    pub fn route_release_id(&self) -> &RootV1 {
        &self.route_release_id
    }
    pub fn module_release_id(&self) -> &RootV1 {
        &self.module_release_id
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
    pub fn module_journal_root(&self) -> &RootV1 {
        &self.module_journal_root
    }
    pub fn lane_journal_root(&self) -> &RootV1 {
        &self.lane_journal_root
    }
    pub fn lane_journal_digest(&self) -> &RootV1 {
        &self.lane_journal_digest
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
    pub fn module_image_id(&self) -> &RootV1 {
        &self.module_image_id
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
        #[derive(Serialize)]
        struct Binding<'a> {
            schema: &'static str,
            profile_root: &'a RootV1,
            route_release_id: &'a RootV1,
            module_release_id: &'a RootV1,
            coordinator_release_id: &'a RootV1,
            command_occurrence_id: &'a RootV1,
            writer_epoch: u64,
            module_journal_root: &'a RootV1,
            lane_journal_root: &'a RootV1,
            lane_journal_digest: &'a RootV1,
            pre_lane_root: &'a RootV1,
            post_lane_root: &'a RootV1,
            effect_plan_root: &'a RootV1,
            module_image_id: &'a RootV1,
            expected_image_id: &'a RootV1,
            receipt_digest: &'a RootV1,
            receipt_kind: ReceiptKindV1,
        }
        hash_global_v1(
            "verified-zdex-tokenomics-lane-v1",
            &Binding {
                schema: VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1,
                profile_root: &self.profile_root,
                route_release_id: &self.route_release_id,
                module_release_id: &self.module_release_id,
                coordinator_release_id: &self.coordinator_release_id,
                command_occurrence_id: &self.command_occurrence_id,
                writer_epoch: self.writer_epoch,
                module_journal_root: &self.module_journal_root,
                lane_journal_root: &self.lane_journal_root,
                lane_journal_digest: &self.lane_journal_digest,
                pre_lane_root: &self.pre_lane_root,
                post_lane_root: &self.post_lane_root,
                effect_plan_root: &self.effect_plan_root,
                module_image_id: &self.module_image_id,
                expected_image_id: &self.expected_image_id,
                receipt_digest: &self.receipt_digest,
                receipt_kind: self.receipt_kind,
            },
        )
    }
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
    if candidate.occurrence.profile_root != governed.profile.profile_id
        || candidate.occurrence.command_kind != governed.route_release.command_kind
        || candidate.occurrence.route_release_id != governed.route_release.route_release_id
        || candidate.occurrence.pre_state_root != candidate.lane_candidate.pre_state.state_root()?
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

fn verify_coordinator_receipt_v1(
    receipt: &ZDEXLaneReceiptEnvelopeV1,
    journal: &crate::proof::LaneCompositionJournalV1,
    governed: &GovernedZDEXTokenomicsProfileV1<'_>,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<(RootV1, RootV1)> {
    if receipt.receipt_kind != ReceiptKindV1::SUCCINCT || receipt.receipt_bytes.is_empty() {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics succinct receipt",
        ));
    }
    let journal_bytes = canonical_bytes_v1(journal)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX tokenomics journal byte width"))?;
    if journal_len
        > governed
            .route_release
            .max_journal_bytes
            .min(governed.coordinator_release.max_journal_bytes)
    {
        return Err(AbiErrorV1::InvalidBounds(
            "ZDEX tokenomics journal byte ceiling",
        ));
    }
    verifier.verify_succinct_receipt(
        &receipt.receipt_bytes,
        &governed.coordinator_release.guest_image_id,
        &journal_bytes,
    )?;
    Ok((
        digest_root_v1(&journal_bytes, "ZDEX tokenomics lane journal digest")?,
        digest_root_v1(
            &receipt.receipt_bytes,
            "ZDEX tokenomics lane receipt digest",
        )?,
    ))
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
    let (lane_journal_digest, receipt_digest) = verify_coordinator_receipt_v1(
        candidate.receipt,
        &accepted.lane_journal,
        governed,
        verifier,
    )?;
    Ok(VerifiedZDEXTokenomicsLaneV1 {
        profile_root: governed.profile.profile_id.clone(),
        route_release_id: governed.route_release.route_release_id.clone(),
        module_release_id: governed.module_release.release_id.clone(),
        coordinator_release_id: governed.coordinator_release.coordinator_release_id.clone(),
        command_occurrence_id: occurrence_id,
        writer_epoch: governed.profile.authority_epoch,
        module_journal_root,
        lane_journal_root: accepted.lane_journal.journal_root()?,
        lane_journal_digest,
        pre_lane_root: accepted.lane_journal.pre_lane_root.clone(),
        post_lane_root: accepted.lane_journal.post_lane_root.clone(),
        effect_plan_root: accepted.effects.effect_plan_root()?,
        module_image_id: governed.module_release.guest_image_id.clone(),
        expected_image_id: governed.coordinator_release.guest_image_id.clone(),
        receipt_digest,
        receipt_kind: candidate.receipt.receipt_kind,
    })
}
