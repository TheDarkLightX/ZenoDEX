use std::collections::BTreeSet;

use serde::Serialize;

use crate::canonical::{
    canonical_bytes_v1, hash_bytes_sha256_v1, hash_global_v1, validate_token_v1, AbiErrorV1,
    AbiResultV1, RootV1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::epoch_effect_composition::compose_asset_lane_epoch_effect_plans_v1;
use crate::proof::{
    EconomicCommandOccurrenceV1, GlobalEconomicEpochCertificateV1, ReceiptKindV1,
    RouteCompositionJournalV1,
};
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneIdV1, LaneRegistryV1,
    ProfileStatusV1, RouteRegistryV1,
};
use crate::route_composition_receipt_verification::VerifiedRouteCompositionV1;

pub const VERIFIED_ECONOMIC_EPOCH_SCHEMA_V1: &str = "zenodex/verified-economic-epoch/v1";

/// Cryptographic verifier port selected by the active economic profile.
pub trait EconomicEpochSuccinctReceiptVerifierV1 {
    fn verify_succinct_receipt(
        &self,
        receipt_bytes: &[u8],
        expected_image_id: &RootV1,
        expected_journal_bytes: &[u8],
    ) -> AbiResultV1<()>;
}

#[derive(Clone, Copy, Debug)]
pub struct EconomicEpochReceiptCandidateV1<'a> {
    pub profile: &'a EconomicProfileSnapshotV1,
    pub lanes: &'a LaneRegistryV1,
    pub coordinators: &'a LaneCoordinatorRegistryV1,
    pub routes: &'a RouteRegistryV1,
    pub certificate: &'a GlobalEconomicEpochCertificateV1,
    pub command_occurrences: &'a [EconomicCommandOccurrenceV1],
    pub route_journals: &'a [RouteCompositionJournalV1],
    pub verified_routes: &'a [VerifiedRouteCompositionV1],
    pub route_effect_plans: &'a [GlobalEconomicEffectPlanV1],
    pub effect_plan: &'a GlobalEconomicEffectPlanV1,
    pub receipt_bytes: &'a [u8],
    pub expected_chain_id: &'a str,
    pub expected_deployment_root: &'a RootV1,
    pub expected_pre_state_root: &'a RootV1,
    pub expected_body_commitment: &'a RootV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedEconomicEpochV1 {
    certificate: GlobalEconomicEpochCertificateV1,
    effect_plan: GlobalEconomicEffectPlanV1,
    ordered_route_binding_roots: Vec<RootV1>,
    receipt_digest: RootV1,
}

#[derive(Serialize)]
struct VerifiedEconomicEpochCommitContentV1<'a> {
    certificate_root: &'a RootV1,
    ordered_route_binding_roots: &'a [RootV1],
    receipt_digest: &'a RootV1,
}

impl VerifiedEconomicEpochV1 {
    pub fn certificate(&self) -> &GlobalEconomicEpochCertificateV1 {
        &self.certificate
    }

    pub fn effect_plan(&self) -> &GlobalEconomicEffectPlanV1 {
        &self.effect_plan
    }

    pub fn ordered_route_binding_roots(&self) -> &[RootV1] {
        &self.ordered_route_binding_roots
    }

    pub fn receipt_digest(&self) -> &RootV1 {
        &self.receipt_digest
    }

    pub fn commit_id(&self) -> AbiResultV1<RootV1> {
        derive_verified_economic_epoch_commit_id_v1(
            &self.certificate.certificate_root()?,
            &self.ordered_route_binding_roots,
            &self.receipt_digest,
        )
    }
}

pub fn derive_verified_economic_epoch_commit_id_v1(
    certificate_root: &RootV1,
    ordered_route_binding_roots: &[RootV1],
    receipt_digest: &RootV1,
) -> AbiResultV1<RootV1> {
    certificate_root.validate("verified epoch certificate root", false)?;
    receipt_digest.validate("verified epoch receipt digest", false)?;
    if ordered_route_binding_roots.is_empty() {
        return Err(AbiErrorV1::InvalidBounds(
            "verified epoch route binding roots",
        ));
    }
    for root in ordered_route_binding_roots {
        root.validate("verified epoch route binding root", false)?;
    }
    if ordered_route_binding_roots
        .iter()
        .collect::<BTreeSet<_>>()
        .len()
        != ordered_route_binding_roots.len()
    {
        return Err(AbiErrorV1::InvalidOrder(
            "verified epoch route binding roots",
        ));
    }
    hash_global_v1(
        "verified-economic-epoch-commit-v1",
        &VerifiedEconomicEpochCommitContentV1 {
            certificate_root,
            ordered_route_binding_roots,
            receipt_digest,
        },
    )
}

fn sha256_root_v1(bytes: &[u8], field: &'static str) -> AbiResultV1<RootV1> {
    RootV1::parse(format!("0x{}", hash_bytes_sha256_v1(bytes)), field, false)
}

fn require_profile_and_certificate_bindings_v1(
    candidate: &EconomicEpochReceiptCandidateV1<'_>,
) -> AbiResultV1<()> {
    candidate.profile.validate_registries(
        candidate.lanes,
        candidate.coordinators,
        candidate.routes,
    )?;
    candidate.certificate.validate()?;
    candidate.effect_plan.validate()?;
    validate_token_v1(candidate.expected_chain_id, "expected epoch chain id")?;
    candidate
        .expected_deployment_root
        .validate("expected epoch deployment root", false)?;
    candidate
        .expected_pre_state_root
        .validate("expected epoch pre-state root", false)?;
    candidate
        .expected_body_commitment
        .validate("expected epoch body commitment", false)?;
    if candidate.profile.status != ProfileStatusV1::ACTIVE {
        return Err(AbiErrorV1::InvalidBinding("economic epoch active profile"));
    }
    if candidate.certificate.receipt_kind != ReceiptKindV1::SUCCINCT {
        return Err(AbiErrorV1::InvalidBinding("economic epoch receipt kind"));
    }
    if candidate.certificate.chain_id != candidate.expected_chain_id
        || candidate.certificate.deployment_root != *candidate.expected_deployment_root
        || candidate.certificate.profile_root != candidate.profile.profile_id
        || candidate.certificate.writer_epoch != candidate.profile.authority_epoch
        || candidate.certificate.pre_state_root != *candidate.expected_pre_state_root
        || candidate.certificate.body_commitment != *candidate.expected_body_commitment
        || candidate.certificate.root_image_id != candidate.profile.root_image_id
        || candidate.certificate.effect_plan_root != candidate.effect_plan.effect_plan_root()?
    {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch profile and certificate",
        ));
    }
    Ok(())
}

fn require_occurrence_set_v1(
    certificate: &GlobalEconomicEpochCertificateV1,
    occurrences: &[EconomicCommandOccurrenceV1],
) -> AbiResultV1<()> {
    if occurrences.len() != certificate.ordered_occurrence_ids.len() {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch occurrence count",
        ));
    }
    let mut positions = Vec::with_capacity(occurrences.len());
    let mut replay_keys = BTreeSet::new();
    let mut consumed_objects = BTreeSet::new();
    for (index, occurrence) in occurrences.iter().enumerate() {
        occurrence.validate()?;
        if occurrence.occurrence_id()? != certificate.ordered_occurrence_ids[index] {
            return Err(AbiErrorV1::InvalidOrder(
                "economic epoch command occurrences",
            ));
        }
        positions.push((occurrence.height, occurrence.tx_index, occurrence.op_index));
        if !replay_keys.insert((occurrence.subject_id.as_str(), occurrence.nonce)) {
            return Err(AbiErrorV1::InvalidBinding(
                "economic epoch subject nonce replay",
            ));
        }
        for object_id in &occurrence.consumed_object_ids {
            if !consumed_objects.insert(object_id.as_str()) {
                return Err(AbiErrorV1::InvalidBinding(
                    "economic epoch duplicate object consumption",
                ));
            }
        }
    }
    if positions.windows(2).any(|pair| pair[0] >= pair[1]) {
        return Err(AbiErrorV1::InvalidOrder(
            "economic epoch command occurrences",
        ));
    }
    Ok(())
}

fn require_route_journal_chain_v1(
    candidate: &EconomicEpochReceiptCandidateV1<'_>,
) -> AbiResultV1<()> {
    if candidate.route_journals.len() != candidate.command_occurrences.len() {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch route journal count",
        ));
    }
    let mut current_root = candidate.certificate.pre_state_root.clone();
    for (index, (occurrence, journal)) in candidate
        .command_occurrences
        .iter()
        .zip(candidate.route_journals)
        .enumerate()
    {
        journal.validate()?;
        if journal.journal_root()? != candidate.certificate.ordered_route_journal_roots[index]
            || journal.command_occurrence_id != candidate.certificate.ordered_occurrence_ids[index]
        {
            return Err(AbiErrorV1::InvalidOrder("economic epoch route journals"));
        }
        let route = candidate
            .routes
            .route_for_command(&occurrence.command_kind, Some(&occurrence.route_release_id))?;
        if journal.route_release_id != route.route_release_id
            || journal.route_release_id != occurrence.route_release_id
            || journal.ordered_lane_journal_roots.len() != route.ordered_lanes.len()
            || journal.chain_id != candidate.certificate.chain_id
            || journal.deployment_root != candidate.certificate.deployment_root
            || journal.profile_root != candidate.certificate.profile_root
            || journal.writer_epoch != candidate.certificate.writer_epoch
            || journal.pre_state_root != current_root
            || occurrence.chain_id != candidate.certificate.chain_id
            || occurrence.deployment_root != candidate.certificate.deployment_root
            || occurrence.profile_root != candidate.certificate.profile_root
            || occurrence.pre_state_root != journal.pre_state_root
            || occurrence.height != candidate.certificate.height
        {
            return Err(AbiErrorV1::InvalidBinding(
                "economic epoch exact route journal",
            ));
        }
        current_root = journal.post_state_root.clone();
    }
    if current_root != candidate.certificate.post_state_root {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch route post-state chain",
        ));
    }
    Ok(())
}

fn require_verified_route_bindings_v1(
    candidate: &EconomicEpochReceiptCandidateV1<'_>,
) -> AbiResultV1<Vec<RootV1>> {
    if candidate.verified_routes.len() != candidate.route_journals.len() {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch route witness count",
        ));
    }
    let mut binding_roots = Vec::with_capacity(candidate.verified_routes.len());
    let mut assumption_roots = Vec::with_capacity(candidate.verified_routes.len());
    for ((occurrence, journal), verified_route) in candidate
        .command_occurrences
        .iter()
        .zip(candidate.route_journals)
        .zip(candidate.verified_routes)
    {
        let route = candidate
            .routes
            .route_for_command(&occurrence.command_kind, Some(&occurrence.route_release_id))?;
        let journal_bytes = canonical_bytes_v1(journal)?;
        let journal_digest = sha256_root_v1(&journal_bytes, "economic epoch route journal digest")?;
        if verified_route.profile_id() != &candidate.profile.profile_id
            || verified_route.route_release_id() != &route.route_release_id
            || verified_route.command_occurrence_id() != &occurrence.occurrence_id()?
            || verified_route.writer_epoch() != candidate.profile.authority_epoch
            || verified_route.ordered_lane_ids() != route.ordered_lanes.as_slice()
            || verified_route.ordered_lane_journal_roots()
                != journal.ordered_lane_journal_roots.as_slice()
            || verified_route.route_journal_root() != &journal.journal_root()?
            || verified_route.route_journal_digest() != &journal_digest
            || verified_route.expected_image_id() != &route.guest_image_id
            || verified_route.receipt_kind() != ReceiptKindV1::SUCCINCT
        {
            return Err(AbiErrorV1::InvalidBinding(
                "economic epoch exact route witness",
            ));
        }
        binding_roots.push(verified_route.binding_root()?);
        assumption_roots.push(verified_route.assumption_root()?);
    }
    let unique = binding_roots.iter().collect::<BTreeSet<_>>();
    if unique.len() != binding_roots.len() {
        return Err(AbiErrorV1::InvalidOrder(
            "economic epoch route witness bindings",
        ));
    }
    if assumption_roots != candidate.certificate.ordered_route_assumption_roots {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch route assumption roots",
        ));
    }
    Ok(binding_roots)
}

fn require_route_effect_bindings_v1(
    candidate: &EconomicEpochReceiptCandidateV1<'_>,
) -> AbiResultV1<()> {
    if candidate.route_effect_plans.len() != candidate.route_journals.len() {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch route effect plan count",
        ));
    }
    for ((occurrence, journal), effect_plan) in candidate
        .command_occurrences
        .iter()
        .zip(candidate.route_journals)
        .zip(candidate.route_effect_plans)
    {
        let route = candidate
            .routes
            .route_for_command(&occurrence.command_kind, Some(&occurrence.route_release_id))?;
        if route.ordered_lanes.as_slice() != [LaneIdV1::ASSET_TRANSFER] {
            return Err(AbiErrorV1::InvalidBinding(
                "economic epoch route effect projection",
            ));
        }
        if effect_plan.effect_plan_root()? != journal.effect_plan_root {
            return Err(AbiErrorV1::InvalidBinding(
                "economic epoch route effect plan root",
            ));
        }
        if effect_plan.occurrence_consumptions != [occurrence.occurrence_id()?] {
            return Err(AbiErrorV1::InvalidBinding(
                "economic epoch route effect occurrence",
            ));
        }
        if !journal.terminal_obligations_root.is_zero() {
            return Err(AbiErrorV1::InvalidBinding(
                "economic epoch route terminal composition",
            ));
        }
    }
    if !candidate.certificate.terminal_obligations_root.is_zero() {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch terminal composition",
        ));
    }
    let composed = compose_asset_lane_epoch_effect_plans_v1(candidate.route_effect_plans)?;
    if composed != *candidate.effect_plan {
        return Err(AbiErrorV1::InvalidBinding(
            "economic epoch route effect plan aggregation",
        ));
    }
    Ok(())
}

pub fn verify_economic_epoch_receipt_v1(
    candidate: EconomicEpochReceiptCandidateV1<'_>,
    receipt_verifier: &dyn EconomicEpochSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedEconomicEpochV1> {
    require_profile_and_certificate_bindings_v1(&candidate)?;
    require_occurrence_set_v1(candidate.certificate, candidate.command_occurrences)?;
    require_route_journal_chain_v1(&candidate)?;
    let ordered_route_binding_roots = require_verified_route_bindings_v1(&candidate)?;
    require_route_effect_bindings_v1(&candidate)?;
    if candidate.receipt_bytes.is_empty() {
        return Err(AbiErrorV1::InvalidBounds("economic epoch receipt bytes"));
    }
    let receipt_digest = sha256_root_v1(candidate.receipt_bytes, "economic epoch receipt digest")?;
    if receipt_digest != candidate.certificate.receipt_root {
        return Err(AbiErrorV1::InvalidBinding("economic epoch receipt root"));
    }
    let journal_bytes = candidate.certificate.canonical_journal_bytes()?;
    receipt_verifier.verify_succinct_receipt(
        candidate.receipt_bytes,
        &candidate.profile.root_image_id,
        &journal_bytes,
    )?;

    Ok(VerifiedEconomicEpochV1 {
        certificate: candidate.certificate.clone(),
        effect_plan: candidate.effect_plan.clone(),
        ordered_route_binding_roots,
        receipt_digest,
    })
}
