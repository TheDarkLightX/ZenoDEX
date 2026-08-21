use serde::Serialize;

use crate::canonical::{canonical_bytes_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::proof::{EconomicCommandOccurrenceV1, ReceiptKindV1};
use crate::release::{LaneIdV1, ReleaseStatusV1};
use crate::zdex_fee_allocation::transition_zdex_fee_allocation_v1;
use crate::zdex_fee_allocation_profile_binding::GovernedZDEXFeeAllocationProfileV1;
use crate::zdex_fee_allocation_types::{
    candidate_zdex_fee_allocation_policy_v1, ZDEXFeeAllocationCommandV1,
    ZDEXFeeAllocationContextV1, ZDEXFeeAllocationOccurrenceV1, ZDEXFeeAllocationPolicyV1,
    ZDEXFeeAllocationResultV1, ZDEXFeeStateV1, PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
};
use crate::zdex_purchase_burn_receipt_verification::{
    digest_root_v1, verify_receipt_v1, ZDEXLaneReceiptEnvelopeV1, ZDEXLaneSuccinctReceiptVerifierV1,
};

pub const VERIFIED_ZDEX_FEE_ALLOCATION_SCHEMA_V1: &str = "zenodex/verified-zdex-fee-allocation/v1";

pub struct ZDEXFeeAllocationReceiptCandidateV1<'a> {
    pub occurrence: &'a EconomicCommandOccurrenceV1,
    pub policy: &'a ZDEXFeeAllocationPolicyV1,
    pub pre_state: &'a ZDEXFeeStateV1,
    pub post_state: &'a ZDEXFeeStateV1,
    pub journal: &'a ZDEXFeeAllocationOccurrenceV1,
    pub effects: &'a GlobalEconomicEffectPlanV1,
    pub receipt: &'a ZDEXLaneReceiptEnvelopeV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct VerifiedZDEXFeeAllocationFieldsV1 {
    allocation_route_release_id: RootV1,
    authorized_buyback_route_release_id: RootV1,
    module_release_id: RootV1,
    command_occurrence_id: RootV1,
    profile_root: RootV1,
    writer_epoch: u64,
    journal_root: RootV1,
    journal_digest: RootV1,
    effect_plan_root: RootV1,
    expected_image_id: RootV1,
    receipt_digest: RootV1,
    receipt_kind: ReceiptKindV1,
    policy_root: RootV1,
    fee_asset_id: RootV1,
    buyback_quote_atoms: u128,
    pre_lane_root: RootV1,
    post_lane_root: RootV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct VerifiedZDEXFeeAllocationV1(VerifiedZDEXFeeAllocationFieldsV1);

impl VerifiedZDEXFeeAllocationV1 {
    pub fn allocation_route_release_id(&self) -> &RootV1 {
        &self.0.allocation_route_release_id
    }
    pub fn authorized_buyback_route_release_id(&self) -> &RootV1 {
        &self.0.authorized_buyback_route_release_id
    }
    pub fn module_release_id(&self) -> &RootV1 {
        &self.0.module_release_id
    }
    pub fn command_occurrence_id(&self) -> &RootV1 {
        &self.0.command_occurrence_id
    }
    pub fn profile_root(&self) -> &RootV1 {
        &self.0.profile_root
    }
    pub fn writer_epoch(&self) -> u64 {
        self.0.writer_epoch
    }
    pub fn journal_root(&self) -> &RootV1 {
        &self.0.journal_root
    }
    pub fn journal_digest(&self) -> &RootV1 {
        &self.0.journal_digest
    }
    pub fn effect_plan_root(&self) -> &RootV1 {
        &self.0.effect_plan_root
    }
    pub fn expected_image_id(&self) -> &RootV1 {
        &self.0.expected_image_id
    }
    pub fn receipt_digest(&self) -> &RootV1 {
        &self.0.receipt_digest
    }
    pub fn receipt_kind(&self) -> ReceiptKindV1 {
        self.0.receipt_kind
    }
    pub fn policy_root(&self) -> &RootV1 {
        &self.0.policy_root
    }
    pub fn fee_asset_id(&self) -> &RootV1 {
        &self.0.fee_asset_id
    }
    pub fn buyback_quote_atoms(&self) -> u128 {
        self.0.buyback_quote_atoms
    }
    pub fn pre_lane_root(&self) -> &RootV1 {
        &self.0.pre_lane_root
    }
    pub fn post_lane_root(&self) -> &RootV1 {
        &self.0.post_lane_root
    }

    pub fn binding_root(&self) -> AbiResultV1<RootV1> {
        #[derive(Serialize)]
        struct Binding<'a> {
            schema: &'static str,
            allocation_route_release_id: &'a RootV1,
            authorized_buyback_route_release_id: &'a RootV1,
            module_release_id: &'a RootV1,
            command_occurrence_id: &'a RootV1,
            profile_root: &'a RootV1,
            writer_epoch: u64,
            journal_root: &'a RootV1,
            journal_digest: &'a RootV1,
            effect_plan_root: &'a RootV1,
            expected_image_id: &'a RootV1,
            receipt_digest: &'a RootV1,
            receipt_kind: ReceiptKindV1,
            policy_root: &'a RootV1,
            fee_asset_id: &'a RootV1,
            buyback_quote_atoms: u128,
            pre_lane_root: &'a RootV1,
            post_lane_root: &'a RootV1,
        }
        hash_global_v1(
            "verified-zdex-fee-allocation-v1",
            &Binding {
                schema: VERIFIED_ZDEX_FEE_ALLOCATION_SCHEMA_V1,
                allocation_route_release_id: &self.0.allocation_route_release_id,
                authorized_buyback_route_release_id: &self.0.authorized_buyback_route_release_id,
                module_release_id: &self.0.module_release_id,
                command_occurrence_id: &self.0.command_occurrence_id,
                profile_root: &self.0.profile_root,
                writer_epoch: self.0.writer_epoch,
                journal_root: &self.0.journal_root,
                journal_digest: &self.0.journal_digest,
                effect_plan_root: &self.0.effect_plan_root,
                expected_image_id: &self.0.expected_image_id,
                receipt_digest: &self.0.receipt_digest,
                receipt_kind: self.0.receipt_kind,
                policy_root: &self.0.policy_root,
                fee_asset_id: &self.0.fee_asset_id,
                buyback_quote_atoms: self.0.buyback_quote_atoms,
                pre_lane_root: &self.0.pre_lane_root,
                post_lane_root: &self.0.post_lane_root,
            },
        )
    }

    pub(crate) fn matches_route_input(
        &self,
        route_release_id: &RootV1,
        journal: &ZDEXFeeAllocationOccurrenceV1,
    ) -> AbiResultV1<bool> {
        let journal_digest = digest_root_v1(
            &canonical_bytes_v1(journal)?,
            "ZDEX fee-allocation journal digest",
        )?;
        Ok(
            self.authorized_buyback_route_release_id() == route_release_id
                && self.allocation_route_release_id() == &journal.allocation_route_release_id
                && self.module_release_id() == &journal.tokenomics_module_release_id
                && self.command_occurrence_id() == &journal.command_occurrence_id
                && self.profile_root() == &journal.profile_root
                && self.writer_epoch() == journal.writer_epoch
                && self.journal_root() == &journal.occurrence_root()?
                && self.journal_digest() == &journal_digest
                && self.effect_plan_root() == &journal.effect_plan_root
                && self.policy_root() == &journal.policy_root
                && self.fee_asset_id() == &journal.fee_asset_id
                && self.buyback_quote_atoms() == journal.buyback_quote_atoms()
                && self.pre_lane_root() == &journal.pre_lane_root
                && self.post_lane_root() == &journal.post_lane_root
                && self.receipt_kind() == ReceiptKindV1::SUCCINCT,
        )
    }
}

fn validate_candidate_v1(
    candidate: &ZDEXFeeAllocationReceiptCandidateV1<'_>,
    governed: &GovernedZDEXFeeAllocationProfileV1<'_>,
) -> AbiResultV1<RootV1> {
    governed.module_release.validate()?;
    candidate.occurrence.validate()?;
    candidate.policy.validate()?;
    candidate.pre_state.validate()?;
    candidate.post_state.validate()?;
    candidate.journal.validate()?;
    candidate.effects.validate()?;
    // The occurrence pre-root belongs to the route/global state domain. The
    // recomputed allocation journal binds this module's fee substate roots.
    if candidate.occurrence.profile_root != governed.profile.profile_id
        || candidate.journal.profile_root != governed.profile.profile_id
        || candidate.journal.writer_epoch != governed.profile.authority_epoch
        || candidate.policy.policy_root()? != governed.policy_binding.policy_root
        || governed.module_release.status != ReleaseStatusV1::SHADOW
        || governed.module_release.lane_id != LaneIdV1::ZDEX_TOKENOMICS
        || !governed
            .module_release
            .command_variants
            .iter()
            .any(|command| command == PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1)
        || candidate.occurrence.command_kind != PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1
        || candidate.occurrence.route_release_id != governed.allocation_route.route_release_id
        || candidate.policy != &candidate_zdex_fee_allocation_policy_v1()
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation release occurrence or policy",
        ));
    }
    candidate.occurrence.occurrence_id()
}

fn recompute_candidate_v1(
    candidate: &ZDEXFeeAllocationReceiptCandidateV1<'_>,
    governed: &GovernedZDEXFeeAllocationProfileV1<'_>,
    occurrence_id: &RootV1,
) -> AbiResultV1<()> {
    let context = ZDEXFeeAllocationContextV1 {
        chain_id: candidate.occurrence.chain_id.clone(),
        deployment_root: candidate.occurrence.deployment_root.clone(),
        profile_root: candidate.occurrence.profile_root.clone(),
        writer_epoch: candidate.journal.writer_epoch,
        allocation_route_release_id: governed.allocation_route.route_release_id.clone(),
        authorized_buyback_route_release_id: governed.buyback_route.route_release_id.clone(),
        tokenomics_module_release_id: governed.module_release.release_id.clone(),
        command_occurrence_id: occurrence_id.clone(),
        policy_root: candidate.policy.policy_root()?,
    };
    let recomputed = transition_zdex_fee_allocation_v1(
        &context,
        candidate.pre_state,
        candidate.policy,
        &ZDEXFeeAllocationCommandV1 {
            fee_charged_atoms: candidate.journal.fee_charged_atoms,
        },
    )?;
    let ZDEXFeeAllocationResultV1::Accepted(accepted) = recomputed else {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation transition rejected",
        ));
    };
    if accepted.post_state != *candidate.post_state
        || accepted.occurrence != *candidate.journal
        || accepted.effects != *candidate.effects
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX fee-allocation journal or effects",
        ));
    }
    Ok(())
}

fn construct_verified_v1(
    candidate: &ZDEXFeeAllocationReceiptCandidateV1<'_>,
    governed: &GovernedZDEXFeeAllocationProfileV1<'_>,
    occurrence_id: RootV1,
    journal_digest: RootV1,
    receipt_digest: RootV1,
) -> AbiResultV1<VerifiedZDEXFeeAllocationV1> {
    Ok(VerifiedZDEXFeeAllocationV1(
        VerifiedZDEXFeeAllocationFieldsV1 {
            allocation_route_release_id: governed.allocation_route.route_release_id.clone(),
            authorized_buyback_route_release_id: governed.buyback_route.route_release_id.clone(),
            module_release_id: governed.module_release.release_id.clone(),
            command_occurrence_id: occurrence_id,
            profile_root: candidate.occurrence.profile_root.clone(),
            writer_epoch: candidate.journal.writer_epoch,
            journal_root: candidate.journal.occurrence_root()?,
            journal_digest,
            effect_plan_root: candidate.effects.effect_plan_root()?,
            expected_image_id: governed.module_release.guest_image_id.clone(),
            receipt_digest,
            receipt_kind: candidate.receipt.receipt_kind,
            policy_root: candidate.policy.policy_root()?,
            fee_asset_id: candidate.journal.fee_asset_id.clone(),
            buyback_quote_atoms: candidate.journal.buyback_quote_atoms(),
            pre_lane_root: candidate.journal.pre_lane_root.clone(),
            post_lane_root: candidate.journal.post_lane_root.clone(),
        },
    ))
}

pub fn verify_zdex_fee_allocation_receipt_v1(
    candidate: ZDEXFeeAllocationReceiptCandidateV1<'_>,
    governed: &GovernedZDEXFeeAllocationProfileV1<'_>,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedZDEXFeeAllocationV1> {
    let occurrence_id = validate_candidate_v1(&candidate, governed)?;
    recompute_candidate_v1(&candidate, governed, &occurrence_id)?;
    let journal_bytes = canonical_bytes_v1(candidate.journal)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX fee-allocation journal width"))?;
    if journal_len > governed.allocation_route.max_journal_bytes {
        return Err(AbiErrorV1::InvalidBounds(
            "ZDEX fee-allocation route journal ceiling",
        ));
    }
    let (journal_digest, receipt_digest) = verify_receipt_v1(
        candidate.receipt,
        &journal_bytes,
        governed.module_release,
        verifier,
    )?;
    construct_verified_v1(
        &candidate,
        governed,
        occurrence_id,
        journal_digest,
        receipt_digest,
    )
}
