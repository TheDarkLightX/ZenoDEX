use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, compose_perps_margin_lane_single_v1,
    transition_perps_margin_lane_module_v1, PerpsMarginAcceptedV1,
    PerpsMarginLaneCompositionAcceptedV1, PerpsMarginLaneCompositionCandidateV1,
    PerpsMarginLaneCompositionResultV1, PerpsMarginLaneCoordinatorContextV1,
    PerpsMarginLaneCoordinatorRejectCodeV1, PerpsMarginLaneModuleInputV1,
    PerpsMarginLaneProjectionV1, PerpsMarginRejectCodeV1, PerpsMarginResultV1,
    MAX_JOURNAL_BYTES_V1,
};

pub const PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/perps-margin-lane-coordinator-guest-input/v1";
pub const MAX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1: usize = 1_048_576;
pub const MAX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1: u32 = 1_048_576;
pub const PERPS_MARGIN_MODULE_IMAGE_ID_V1: [u32; 8] = [
    695_572_787,
    3_504_753_096,
    3_337_513_134,
    2_865_730_872,
    3_839_057_979,
    1_870_156_240,
    2_829_371_707,
    1_610_587_060,
];

const _: () = assert!(
    PERPS_MARGIN_MODULE_IMAGE_ID_V1[0] != 0
        || PERPS_MARGIN_MODULE_IMAGE_ID_V1[1] != 0
        || PERPS_MARGIN_MODULE_IMAGE_ID_V1[2] != 0
        || PERPS_MARGIN_MODULE_IMAGE_ID_V1[3] != 0
        || PERPS_MARGIN_MODULE_IMAGE_ID_V1[4] != 0
        || PERPS_MARGIN_MODULE_IMAGE_ID_V1[5] != 0
        || PERPS_MARGIN_MODULE_IMAGE_ID_V1[6] != 0
        || PERPS_MARGIN_MODULE_IMAGE_ID_V1[7] != 0
);

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct PerpsMarginLaneCoordinatorGuestInputV1 {
    pub schema: String,
    pub module_input: PerpsMarginLaneModuleInputV1,
    pub coordinator_context: PerpsMarginLaneCoordinatorContextV1,
    pub pre_state: PerpsMarginLaneProjectionV1,
    pub post_state: PerpsMarginLaneProjectionV1,
}

impl PerpsMarginLaneCoordinatorGuestInputV1 {
    pub fn validate(&self) -> Result<(), PerpsMarginLaneCoordinatorGuestErrorV1> {
        if self.schema != PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1 {
            return Err(PerpsMarginLaneCoordinatorGuestErrorV1::Schema);
        }
        self.module_input
            .validate()
            .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
        self.coordinator_context
            .validate()
            .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
        self.pre_state
            .validate()
            .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
        self.post_state
            .validate()
            .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PerpsMarginLaneCoordinatorGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Schema,
    Abi,
    ModuleRejected(PerpsMarginRejectCodeV1),
    CoordinatorRejected(PerpsMarginLaneCoordinatorRejectCodeV1),
    ModuleJournalTooLarge,
    LaneJournalTooLarge,
}

impl PerpsMarginLaneCoordinatorGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "perps margin coordinator input is empty",
            Self::InputTooLarge => "perps margin coordinator input exceeds release bound",
            Self::Decode => "perps margin coordinator input decode failed",
            Self::NonCanonicalInput => "perps margin coordinator input is noncanonical",
            Self::Schema => "perps margin coordinator input schema rejected",
            Self::Abi => "perps margin coordinator ABI validation failed",
            Self::ModuleRejected(_) => "perps margin coordinator module transition rejected",
            Self::CoordinatorRejected(_) => "perps margin coordinator transition rejected",
            Self::ModuleJournalTooLarge => "perps margin child module journal exceeds ABI bound",
            Self::LaneJournalTooLarge => "perps margin lane journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for PerpsMarginLaneCoordinatorGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "perps margin coordinator guest rejected: {self:?}"
        )
    }
}

impl std::error::Error for PerpsMarginLaneCoordinatorGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedPerpsMarginLaneCoordinatorV1 {
    pub input: PerpsMarginLaneCoordinatorGuestInputV1,
    pub module_accepted: PerpsMarginAcceptedV1,
    pub lane_accepted: PerpsMarginLaneCompositionAcceptedV1,
    pub module_journal_bytes: Vec<u8>,
    pub lane_journal_bytes: Vec<u8>,
}

pub fn canonical_perps_margin_lane_coordinator_guest_input_bytes_v1(
    input: &PerpsMarginLaneCoordinatorGuestInputV1,
) -> Result<Vec<u8>, PerpsMarginLaneCoordinatorGuestErrorV1> {
    input.validate()?;
    let bytes =
        canonical_bytes_v1(input).map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedPerpsMarginLaneCoordinatorV1, PerpsMarginLaneCoordinatorGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: PerpsMarginLaneCoordinatorGuestInputV1 = serde_json::from_slice(input_bytes)
        .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Decode)?;
    let canonical =
        canonical_bytes_v1(&input).map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(PerpsMarginLaneCoordinatorGuestErrorV1::NonCanonicalInput);
    }
    prepare_perps_margin_lane_coordinator_v1(input)
}

pub fn prepare_perps_margin_lane_coordinator_v1(
    input: PerpsMarginLaneCoordinatorGuestInputV1,
) -> Result<PreparedPerpsMarginLaneCoordinatorV1, PerpsMarginLaneCoordinatorGuestErrorV1> {
    input.validate()?;
    let module_result = transition_perps_margin_lane_module_v1(&input.module_input)
        .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
    let module_accepted = match module_result {
        PerpsMarginResultV1::Accepted(accepted) => *accepted,
        PerpsMarginResultV1::Rejected(rejected) => {
            return Err(PerpsMarginLaneCoordinatorGuestErrorV1::ModuleRejected(
                rejected.code,
            ));
        }
    };
    module_accepted
        .validate()
        .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;

    let lane_result = compose_perps_margin_lane_single_v1(&PerpsMarginLaneCompositionCandidateV1 {
        context: input.coordinator_context.clone(),
        module_journal: module_accepted.module_journal.clone(),
        private_port: module_accepted.private_port.clone(),
        pre_state: input.pre_state.clone(),
        post_state: input.post_state.clone(),
        module_effects: module_accepted.effects.clone(),
    })
    .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
    let lane_accepted = match lane_result {
        PerpsMarginLaneCompositionResultV1::Accepted(accepted) => *accepted,
        PerpsMarginLaneCompositionResultV1::Rejected(rejected) => {
            return Err(PerpsMarginLaneCoordinatorGuestErrorV1::CoordinatorRejected(
                rejected.code,
            ));
        }
    };
    lane_accepted
        .validate()
        .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;

    let module_journal_bytes = canonical_bytes_v1(&module_accepted.module_journal)
        .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
    validate_journal_size_v1(
        &module_journal_bytes,
        PerpsMarginLaneCoordinatorGuestErrorV1::ModuleJournalTooLarge,
    )?;
    let lane_journal_bytes = canonical_bytes_v1(&lane_accepted.lane_journal)
        .map_err(|_| PerpsMarginLaneCoordinatorGuestErrorV1::Abi)?;
    validate_journal_size_v1(
        &lane_journal_bytes,
        PerpsMarginLaneCoordinatorGuestErrorV1::LaneJournalTooLarge,
    )?;
    Ok(PreparedPerpsMarginLaneCoordinatorV1 {
        input,
        module_accepted,
        lane_accepted,
        module_journal_bytes,
        lane_journal_bytes,
    })
}

fn validate_input_size_v1(
    input_bytes: &[u8],
) -> Result<(), PerpsMarginLaneCoordinatorGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(PerpsMarginLaneCoordinatorGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1 {
        return Err(PerpsMarginLaneCoordinatorGuestErrorV1::InputTooLarge);
    }
    Ok(())
}

fn validate_journal_size_v1(
    journal_bytes: &[u8],
    error: PerpsMarginLaneCoordinatorGuestErrorV1,
) -> Result<(), PerpsMarginLaneCoordinatorGuestErrorV1> {
    let journal_len = u64::try_from(journal_bytes.len()).map_err(|_| error)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(error);
    }
    Ok(())
}
