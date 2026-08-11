use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, compose_asset_lane_single_v1, transition_asset_transfer_lane_module_v1,
    AssetLaneCompositionAcceptedV1, AssetLaneCompositionResultV1, AssetLaneCoordinatorContextV1,
    AssetLaneCoordinatorRejectCodeV1, AssetTransferLaneModuleAcceptedV1,
    AssetTransferLaneModuleInputV1, AssetTransferLaneModuleResultV1, AssetTransferRejectCodeV1,
    MAX_JOURNAL_BYTES_V1,
};

pub const ASSET_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/asset-lane-coordinator-guest-input/v1";
pub const MAX_ASSET_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1: usize = 1_048_576;
pub const MAX_ASSET_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1: u32 = 1_048_576;

/// The exact module image admitted by this coordinator image.
///
/// Changing this constant changes the coordinator statement and requires a new
/// coordinator image plus replacement composition evidence.
pub const ASSET_TRANSFER_MODULE_IMAGE_ID_V1: [u32; 8] = [
    3_494_995_490,
    1_275_137_722,
    1_377_448_836,
    1_356_757_021,
    2_581_487_242,
    1_957_138_521,
    501_643_869,
    607_044_243,
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneCoordinatorGuestInputV1 {
    pub schema: String,
    pub module_input: AssetTransferLaneModuleInputV1,
    pub coordinator_context: AssetLaneCoordinatorContextV1,
}

impl AssetLaneCoordinatorGuestInputV1 {
    pub fn validate(&self) -> Result<(), AssetLaneCoordinatorGuestErrorV1> {
        if self.schema != ASSET_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1 {
            return Err(AssetLaneCoordinatorGuestErrorV1::Schema);
        }
        self.module_input
            .validate()
            .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;
        self.coordinator_context
            .validate()
            .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;
        if ASSET_TRANSFER_MODULE_IMAGE_ID_V1 == [0; 8] {
            return Err(AssetLaneCoordinatorGuestErrorV1::PinnedModuleImage);
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssetLaneCoordinatorGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Schema,
    PinnedModuleImage,
    Abi,
    ModuleRejected(AssetTransferRejectCodeV1),
    CoordinatorRejected(AssetLaneCoordinatorRejectCodeV1),
    ModuleJournalTooLarge,
    LaneJournalTooLarge,
}

impl AssetLaneCoordinatorGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "asset lane coordinator input is empty",
            Self::InputTooLarge => "asset lane coordinator input exceeds release bound",
            Self::Decode => "asset lane coordinator input decode failed",
            Self::NonCanonicalInput => "asset lane coordinator input is noncanonical",
            Self::Schema => "asset lane coordinator input schema rejected",
            Self::PinnedModuleImage => "asset lane coordinator module image is invalid",
            Self::Abi => "asset lane coordinator ABI validation failed",
            Self::ModuleRejected(_) => "asset lane coordinator module transition rejected",
            Self::CoordinatorRejected(_) => "asset lane coordinator transition rejected",
            Self::ModuleJournalTooLarge => "asset lane module journal exceeds ABI bound",
            Self::LaneJournalTooLarge => "asset lane composition journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for AssetLaneCoordinatorGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "asset lane coordinator guest rejected: {self:?}")
    }
}

impl std::error::Error for AssetLaneCoordinatorGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedAssetLaneCoordinatorV1 {
    pub input: AssetLaneCoordinatorGuestInputV1,
    pub module_accepted: AssetTransferLaneModuleAcceptedV1,
    pub lane_accepted: AssetLaneCompositionAcceptedV1,
    pub module_journal_bytes: Vec<u8>,
    pub lane_journal_bytes: Vec<u8>,
}

pub fn canonical_asset_lane_coordinator_guest_input_bytes_v1(
    input: &AssetLaneCoordinatorGuestInputV1,
) -> Result<Vec<u8>, AssetLaneCoordinatorGuestErrorV1> {
    input.validate()?;
    let bytes = canonical_bytes_v1(input).map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_asset_lane_coordinator_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedAssetLaneCoordinatorV1, AssetLaneCoordinatorGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: AssetLaneCoordinatorGuestInputV1 = serde_json::from_slice(input_bytes)
        .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Decode)?;
    let canonical =
        canonical_bytes_v1(&input).map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(AssetLaneCoordinatorGuestErrorV1::NonCanonicalInput);
    }
    prepare_asset_lane_coordinator_v1(input)
}

pub fn prepare_asset_lane_coordinator_v1(
    input: AssetLaneCoordinatorGuestInputV1,
) -> Result<PreparedAssetLaneCoordinatorV1, AssetLaneCoordinatorGuestErrorV1> {
    input.validate()?;
    let module_result = transition_asset_transfer_lane_module_v1(&input.module_input)
        .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;
    let module_accepted = match module_result {
        AssetTransferLaneModuleResultV1::Accepted(accepted) => *accepted,
        AssetTransferLaneModuleResultV1::Rejected(rejected) => {
            return Err(AssetLaneCoordinatorGuestErrorV1::ModuleRejected(
                rejected.code,
            ));
        }
    };
    module_accepted
        .validate()
        .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;

    let lane_result = compose_asset_lane_single_v1(
        &input.coordinator_context,
        &module_accepted.module_journal,
        &module_accepted.private_port,
        &module_accepted.effects,
    )
    .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;
    let lane_accepted = match lane_result {
        AssetLaneCompositionResultV1::Accepted(accepted) => *accepted,
        AssetLaneCompositionResultV1::Rejected(rejected) => {
            return Err(AssetLaneCoordinatorGuestErrorV1::CoordinatorRejected(
                rejected.code,
            ));
        }
    };
    lane_accepted
        .validate()
        .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;

    let module_journal_bytes = canonical_bytes_v1(&module_accepted.module_journal)
        .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;
    validate_journal_size_v1(
        &module_journal_bytes,
        AssetLaneCoordinatorGuestErrorV1::ModuleJournalTooLarge,
    )?;
    let lane_journal_bytes = canonical_bytes_v1(&lane_accepted.lane_journal)
        .map_err(|_| AssetLaneCoordinatorGuestErrorV1::Abi)?;
    validate_journal_size_v1(
        &lane_journal_bytes,
        AssetLaneCoordinatorGuestErrorV1::LaneJournalTooLarge,
    )?;

    Ok(PreparedAssetLaneCoordinatorV1 {
        input,
        module_accepted,
        lane_accepted,
        module_journal_bytes,
        lane_journal_bytes,
    })
}

fn validate_input_size_v1(input_bytes: &[u8]) -> Result<(), AssetLaneCoordinatorGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(AssetLaneCoordinatorGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_ASSET_LANE_COORDINATOR_GUEST_INPUT_BYTES_V1 {
        return Err(AssetLaneCoordinatorGuestErrorV1::InputTooLarge);
    }
    Ok(())
}

fn validate_journal_size_v1(
    journal_bytes: &[u8],
    error: AssetLaneCoordinatorGuestErrorV1,
) -> Result<(), AssetLaneCoordinatorGuestErrorV1> {
    let journal_len = u64::try_from(journal_bytes.len()).map_err(|_| error)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(error);
    }
    Ok(())
}
