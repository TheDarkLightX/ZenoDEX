use serde::Serialize;

use crate::canonical::{canonical_bytes_v1, hash_global_v1, AbiErrorV1, AbiResultV1, RootV1};
use crate::proof::{LaneCompositionJournalV1, ReceiptKindV1};
use crate::release::{LaneCoordinatorReleaseV1, LaneIdV1, RouteReleaseV1};
use crate::zdex_purchase_burn_receipt_verification::{
    digest_root_v1, ZDEXLaneReceiptEnvelopeV1, ZDEXLaneSuccinctReceiptVerifierV1,
};

pub const VERIFIED_ZDEX_TOKENOMICS_LANE_SCHEMA_V1: &str =
    "zenodex/verified-zdex-tokenomics-lane/v1";

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

pub(crate) struct ZDEXTokenomicsLaneBindingV1 {
    pub(crate) profile_root: RootV1,
    pub(crate) route_release_id: RootV1,
    pub(crate) module_release_id: RootV1,
    pub(crate) command_occurrence_id: RootV1,
    pub(crate) writer_epoch: u64,
    pub(crate) module_journal_root: RootV1,
    pub(crate) module_image_id: RootV1,
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

pub(crate) struct ZDEXTokenomicsCoordinatorReceiptExpectationV1<'a> {
    pub(crate) route_release: &'a RouteReleaseV1,
    pub(crate) coordinator_release: &'a LaneCoordinatorReleaseV1,
}

pub(crate) fn verify_and_construct_zdex_tokenomics_lane_v1(
    receipt: &ZDEXLaneReceiptEnvelopeV1,
    journal: &LaneCompositionJournalV1,
    expectation: ZDEXTokenomicsCoordinatorReceiptExpectationV1<'_>,
    binding: ZDEXTokenomicsLaneBindingV1,
    verifier: &impl ZDEXLaneSuccinctReceiptVerifierV1,
) -> AbiResultV1<VerifiedZDEXTokenomicsLaneV1> {
    if journal.profile_root != binding.profile_root
        || journal.writer_epoch != binding.writer_epoch
        || journal.lane_id != LaneIdV1::ZDEX_TOKENOMICS
        || journal.coordinator_release_id != expectation.coordinator_release.coordinator_release_id
        || journal.command_occurrence_id != binding.command_occurrence_id
        || journal.ordered_module_journal_roots != [binding.module_journal_root.clone()]
        || expectation.route_release.route_release_id != binding.route_release_id
    {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics verified-lane binding",
        ));
    }
    if receipt.receipt_kind != ReceiptKindV1::SUCCINCT || receipt.receipt_bytes.is_empty() {
        return Err(AbiErrorV1::InvalidBinding(
            "ZDEX tokenomics succinct receipt",
        ));
    }
    let journal_bytes = canonical_bytes_v1(journal)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| AbiErrorV1::InvalidBounds("ZDEX tokenomics journal byte width"))?;
    if journal_len
        > expectation
            .route_release
            .max_journal_bytes
            .min(expectation.coordinator_release.max_journal_bytes)
    {
        return Err(AbiErrorV1::InvalidBounds(
            "ZDEX tokenomics journal byte ceiling",
        ));
    }
    verifier.verify_succinct_receipt(
        &receipt.receipt_bytes,
        &expectation.coordinator_release.guest_image_id,
        &journal_bytes,
    )?;
    Ok(VerifiedZDEXTokenomicsLaneV1 {
        profile_root: binding.profile_root,
        route_release_id: binding.route_release_id,
        module_release_id: binding.module_release_id,
        coordinator_release_id: expectation
            .coordinator_release
            .coordinator_release_id
            .clone(),
        command_occurrence_id: binding.command_occurrence_id,
        writer_epoch: binding.writer_epoch,
        module_journal_root: binding.module_journal_root,
        lane_journal_root: journal.journal_root()?,
        lane_journal_digest: digest_root_v1(&journal_bytes, "ZDEX tokenomics lane journal digest")?,
        pre_lane_root: journal.pre_lane_root.clone(),
        post_lane_root: journal.post_lane_root.clone(),
        effect_plan_root: journal.effect_plan_root.clone(),
        module_image_id: binding.module_image_id,
        expected_image_id: expectation.coordinator_release.guest_image_id.clone(),
        receipt_digest: digest_root_v1(
            &receipt.receipt_bytes,
            "ZDEX tokenomics lane receipt digest",
        )?,
        receipt_kind: receipt.receipt_kind,
    })
}
