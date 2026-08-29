use crate::canonical::{AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::zdex_fee_allocation_profile_binding::GovernedZDEXFeeAllocationProfileV1;
use crate::zdex_fee_allocation_receipt_verification::VerifiedZDEXFeeAllocationV1;
use crate::zdex_fee_allocation_types::PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1;
use crate::zdex_purchase_burn_receipt_verification::{
    ZDEXLaneReceiptEnvelopeV1, ZDEXLaneSuccinctReceiptVerifierV1,
};
use crate::zdex_tokenomics_fee_lane_coordinator::{
    compose_zdex_tokenomics_fee_allocation_lane_v1, ZDEXTokenomicsFeeAllocationLaneCandidateV1,
};
use crate::zdex_tokenomics_lane_receipt_common::{
    verify_and_construct_zdex_tokenomics_lane_v1, VerifiedZDEXTokenomicsLaneV1,
    ZDEXTokenomicsCoordinatorReceiptExpectationV1, ZDEXTokenomicsLaneBindingV1,
};
use crate::zdex_tokenomics_lane_types::ZDEXTokenomicsLaneCompositionResultV1;

pub struct ZDEXTokenomicsFeeLaneReceiptCandidateV1<'a> {
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub lane_candidate: ZDEXTokenomicsFeeAllocationLaneCandidateV1<'a>,
    pub verified_allocation: &'a VerifiedZDEXFeeAllocationV1,
    pub receipt: &'a ZDEXLaneReceiptEnvelopeV1,
}

fn require_candidate_bindings_v1(
    candidate: &ZDEXTokenomicsFeeLaneReceiptCandidateV1<'_>,
    governed: &GovernedZDEXFeeAllocationProfileV1<'_>,
) -> AbiResultV1<RootV1> {
    candidate.occurrence.validate()?;
    candidate.lane_candidate.validate()?;
    let occurrence_id = candidate.occurrence.occurrence_id()?;
    let lane = &candidate.lane_candidate;
    let allocation = lane.allocation;
    let journal = &allocation.occurrence;
    let context = lane.context;
    let profile = governed.profile();
    let allocation_route = governed.allocation_route();
    let buyback_route = governed.buyback_route();
    let module = governed.module_release();
    let coordinator = governed.coordinator_release();
    let policy_binding = governed.policy_binding();
    let verified_matches = candidate
        .verified_allocation
        .matches_route_input(&buyback_route.route_release_id, journal)?;
    // Route admission owns the occurrence's global pre-root. The exact
    // coordinator receipt below binds this complete lane's pre/post roots.
    if candidate.occurrence.profile_root != profile.profile_id
        || candidate.occurrence.command_kind != PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1
        || candidate.occurrence.route_release_id != allocation_route.route_release_id
        || occurrence_id != journal.command_occurrence_id
        || context.chain_id != candidate.occurrence.chain_id
        || context.deployment_root != candidate.occurrence.deployment_root
        || context.profile_root != profile.profile_id
        || context.writer_epoch != profile.authority_epoch
        || context.coordinator_release_id != coordinator.coordinator_release_id
        || context.allocation_route_release_id != allocation_route.route_release_id
        || context.authorized_buyback_route_release_id != buyback_route.route_release_id
        || context.tokenomics_module_release_id != module.release_id
        || context.command_occurrence_id != occurrence_id
        || context.policy_root != policy_binding.policy_root
        || lane.policy.policy_root()? != policy_binding.policy_root
        || lane.module_journal.module_release_id != module.release_id
        || candidate.verified_allocation.expected_image_id() != &module.guest_image_id
        || candidate.verified_allocation.fee_ingress_atoms()
            != allocation.pre_state.fee_ingress_atoms
        || !verified_matches
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics governed fee-lane candidate",
        ));
    }
    Ok(occurrence_id)
}

/// Run SHADOW fee-lane admission through the supplied verifier port.
///
/// The returned marker is process-local and carries no settlement authority.
pub fn verify_zdex_tokenomics_fee_lane_receipt_v1(
    candidate: ZDEXTokenomicsFeeLaneReceiptCandidateV1<'_>,
    governed: &GovernedZDEXFeeAllocationProfileV1<'_>,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedZDEXTokenomicsLaneV1> {
    let occurrence_id = require_candidate_bindings_v1(&candidate, governed)?;
    let module_journal_root = candidate.lane_candidate.module_journal.journal_root()?;
    let result = compose_zdex_tokenomics_fee_allocation_lane_v1(candidate.lane_candidate)?;
    let ZDEXTokenomicsLaneCompositionResultV1::Accepted(accepted) = result else {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics fee-lane composition rejected",
        ));
    };
    let coordinator = governed.coordinator_release();
    verify_and_construct_zdex_tokenomics_lane_v1(
        candidate.receipt,
        &accepted.lane_journal,
        ZDEXTokenomicsCoordinatorReceiptExpectationV1 {
            route_release: governed.allocation_route(),
            coordinator_release: coordinator,
        },
        ZDEXTokenomicsLaneBindingV1 {
            profile_root: governed.profile().profile_id.clone(),
            route_release_id: governed.allocation_route().route_release_id.clone(),
            module_release_id: governed.module_release().release_id.clone(),
            command_occurrence_id: occurrence_id,
            writer_epoch: governed.profile().authority_epoch,
            module_journal_root,
            module_image_id: governed.module_release().guest_image_id.clone(),
        },
        verifier,
    )
}
