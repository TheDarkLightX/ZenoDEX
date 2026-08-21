use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, compose_zdex_tokenomics_fee_allocation_lane_v1, LaneCompositionJournalV1,
    LaneModuleReleaseV1, LaneModuleTransitionJournalV1, ZDEXFeeAllocationAcceptedV1,
    ZDEXFeeAllocationPolicyV1, ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    ZDEXTokenomicsFeeAllocationLaneCandidateV1, ZDEXTokenomicsFeeAllocationPrivatePortV1,
    ZDEXTokenomicsLaneCompositionAcceptedV1, ZDEXTokenomicsLaneCompositionResultV1,
    ZDEXTokenomicsLaneStateV1, MAX_JOURNAL_BYTES_V1, PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1,
};

use crate::{
    validate_input_size_v1, validate_lane_journal_size_v1, validate_module_release_command_v1,
    ZDEXTokenomicsLaneCoordinatorGuestErrorV1,
};

pub const ZDEX_TOKENOMICS_FEE_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/zdex-tokenomics-fee-lane-coordinator-guest-input/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1 {
    pub schema: String,
    pub module_release: LaneModuleReleaseV1,
    pub context: ZDEXTokenomicsFeeAllocationCoordinatorContextV1,
    pub module_journal: LaneModuleTransitionJournalV1,
    pub private_port: ZDEXTokenomicsFeeAllocationPrivatePortV1,
    pub pre_state: ZDEXTokenomicsLaneStateV1,
    pub post_state: ZDEXTokenomicsLaneStateV1,
    pub allocation: ZDEXFeeAllocationAcceptedV1,
    pub policy: ZDEXFeeAllocationPolicyV1,
}

impl ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1 {
    pub fn validate(&self) -> Result<(), ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
        if self.schema != ZDEX_TOKENOMICS_FEE_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1 {
            return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Schema);
        }
        self.module_release
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.context
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.module_journal
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.private_port
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.pre_state
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.post_state
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.allocation
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        self.policy
            .validate()
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
        validate_fee_module_release_v1(self)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedZDEXTokenomicsFeeLaneCoordinatorV1 {
    pub input: ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1,
    pub accepted: ZDEXTokenomicsLaneCompositionAcceptedV1,
    pub child_journal_bytes: Vec<u8>,
    pub lane_journal_bytes: Vec<u8>,
}

impl PreparedZDEXTokenomicsFeeLaneCoordinatorV1 {
    pub fn lane_journal(&self) -> &LaneCompositionJournalV1 {
        &self.accepted.lane_journal
    }
}

pub fn canonical_zdex_tokenomics_fee_lane_coordinator_guest_input_bytes_v1(
    input: &ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1,
) -> Result<Vec<u8>, ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    input.validate()?;
    let bytes =
        canonical_bytes_v1(input).map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_zdex_tokenomics_fee_lane_coordinator_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedZDEXTokenomicsFeeLaneCoordinatorV1, ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1 =
        serde_json::from_slice(input_bytes)
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Decode)?;
    let canonical =
        canonical_bytes_v1(&input).map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::NonCanonicalInput);
    }
    prepare_zdex_tokenomics_fee_lane_coordinator_v1(input)
}

pub fn prepare_zdex_tokenomics_fee_lane_coordinator_v1(
    input: ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1,
) -> Result<PreparedZDEXTokenomicsFeeLaneCoordinatorV1, ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    input.validate()?;
    let input_bytes =
        canonical_bytes_v1(&input).map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    validate_input_size_v1(&input_bytes)?;

    let result = compose_zdex_tokenomics_fee_allocation_lane_v1(
        ZDEXTokenomicsFeeAllocationLaneCandidateV1 {
            context: &input.context,
            module_journal: &input.module_journal,
            private_port: &input.private_port,
            pre_state: &input.pre_state,
            post_state: &input.post_state,
            allocation: &input.allocation,
            policy: &input.policy,
        },
    )
    .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    let accepted = match result {
        ZDEXTokenomicsLaneCompositionResultV1::Accepted(accepted) => accepted,
        ZDEXTokenomicsLaneCompositionResultV1::Rejected(rejected) => {
            return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Rejected(
                rejected.code,
            ));
        }
    };
    accepted
        .validate()
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;

    let child_journal_bytes = canonical_bytes_v1(&input.allocation.occurrence)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    validate_fee_journal_size_v1(&input.module_release, &child_journal_bytes)?;
    let lane_journal_bytes = canonical_bytes_v1(&accepted.lane_journal)
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Abi)?;
    validate_lane_journal_size_v1(&lane_journal_bytes)?;

    Ok(PreparedZDEXTokenomicsFeeLaneCoordinatorV1 {
        input,
        accepted: *accepted,
        child_journal_bytes,
        lane_journal_bytes,
    })
}

fn validate_fee_module_release_v1(
    input: &ZDEXTokenomicsFeeLaneCoordinatorGuestInputV1,
) -> Result<(), ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    let release = &input.module_release;
    validate_module_release_command_v1(release, PROTOCOL_FEE_ALLOCATION_COMMAND_KIND_V1)?;
    if input.context.tokenomics_module_release_id != release.release_id
        || input.module_journal.module_release_id != release.release_id
        || input.private_port.module_release_id != release.release_id
        || input.allocation.occurrence.tokenomics_module_release_id != release.release_id
    {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::ModuleReleaseBinding);
    }
    Ok(())
}

fn validate_fee_journal_size_v1(
    release: &LaneModuleReleaseV1,
    bytes: &[u8],
) -> Result<(), ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    let length = u64::try_from(bytes.len())
        .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::FeeJournalTooLarge)?;
    if length == 0 || length > release.max_journal_bytes.min(MAX_JOURNAL_BYTES_V1) {
        return Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::FeeJournalTooLarge);
    }
    Ok(())
}
