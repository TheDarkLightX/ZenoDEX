//! Pure custody-complete ASSET lane coordination preflight.
//!
//! This crate owns ordinary input, acceptance, and canonical journal bytes.
//! It does not select an image, invoke a callback, or grant receipt,
//! settlement, release, or publication authority.

use core::fmt;

use serde::{Deserialize, Serialize};
use zenodex_asset_transfer_custody_module_risc0_shared::{
    prepare_asset_transfer_custody_module_v1, AssetTransferGuestErrorV1,
};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, compose_asset_lane_single_v1, AssetLaneCompositionAcceptedV1,
    AssetLaneCompositionResultV1, AssetLaneCoordinatorContextV1, AssetLaneCoordinatorRejectCodeV1,
    AssetTransferLaneModuleAcceptedV1, AssetTransferLaneModuleInputV1, AssetTransferRejectCodeV1,
    MAX_JOURNAL_BYTES_V1,
};

pub const ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_SCHEMA_V1: &str =
    "zenodex/asset-lane-coordinator-guest-input/v1";
pub const MAX_ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_BYTES_V1: usize = 1_048_576;
pub const MAX_ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_BYTES_U32_V1: u32 = 1_048_576;

/// The unchanged V1 wire envelope for custody-complete lane coordination.
#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneCustodyCoordinatorInputV1 {
    pub schema: String,
    pub module_input: AssetTransferLaneModuleInputV1,
    pub coordinator_context: AssetLaneCoordinatorContextV1,
}

impl AssetLaneCustodyCoordinatorInputV1 {
    pub fn validate(&self) -> Result<(), AssetLaneCustodyCoordinatorGuestErrorV1> {
        if self.schema != ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_SCHEMA_V1 {
            return Err(AssetLaneCustodyCoordinatorGuestErrorV1::Schema);
        }
        self.module_input
            .validate()
            .map_err(|_| AssetLaneCustodyCoordinatorGuestErrorV1::Abi)?;
        self.coordinator_context
            .validate()
            .map_err(|_| AssetLaneCustodyCoordinatorGuestErrorV1::Abi)?;
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssetLaneCustodyCoordinatorGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Schema,
    Abi,
    ModuleRejected(AssetTransferRejectCodeV1),
    CoordinatorRejected(AssetLaneCoordinatorRejectCodeV1),
    ModuleJournalTooLarge,
    LaneJournalTooLarge,
}

impl AssetLaneCustodyCoordinatorGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "asset lane custody coordinator input is empty",
            Self::InputTooLarge => "asset lane custody coordinator input exceeds release bound",
            Self::Decode => "asset lane custody coordinator input decode failed",
            Self::NonCanonicalInput => "asset lane custody coordinator input is noncanonical",
            Self::Schema => "asset lane custody coordinator input schema rejected",
            Self::Abi => "asset lane custody coordinator ABI validation failed",
            Self::ModuleRejected(_) => "asset lane custody coordinator module transition rejected",
            Self::CoordinatorRejected(_) => "asset lane custody coordinator transition rejected",
            Self::ModuleJournalTooLarge => "asset lane module journal exceeds ABI bound",
            Self::LaneJournalTooLarge => "asset lane composition journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for AssetLaneCustodyCoordinatorGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "asset lane custody coordinator guest rejected: {self:?}"
        )
    }
}

impl std::error::Error for AssetLaneCustodyCoordinatorGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedAssetLaneCustodyCoordinatorV1 {
    pub input: AssetLaneCustodyCoordinatorInputV1,
    pub module_accepted: AssetTransferLaneModuleAcceptedV1,
    pub lane_accepted: AssetLaneCompositionAcceptedV1,
    pub module_journal_bytes: Vec<u8>,
    pub lane_journal_bytes: Vec<u8>,
}

pub fn canonical_asset_lane_custody_coordinator_input_bytes_v1(
    input: &AssetLaneCustodyCoordinatorInputV1,
) -> Result<Vec<u8>, AssetLaneCustodyCoordinatorGuestErrorV1> {
    input.validate()?;
    let bytes =
        canonical_bytes_v1(input).map_err(|_| AssetLaneCustodyCoordinatorGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_asset_lane_custody_coordinator_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedAssetLaneCustodyCoordinatorV1, AssetLaneCustodyCoordinatorGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: AssetLaneCustodyCoordinatorInputV1 = serde_json::from_slice(input_bytes)
        .map_err(|_| AssetLaneCustodyCoordinatorGuestErrorV1::Decode)?;
    let canonical =
        canonical_bytes_v1(&input).map_err(|_| AssetLaneCustodyCoordinatorGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(AssetLaneCustodyCoordinatorGuestErrorV1::NonCanonicalInput);
    }
    prepare_asset_lane_custody_coordinator_v1(input)
}

pub fn prepare_asset_lane_custody_coordinator_v1(
    input: AssetLaneCustodyCoordinatorInputV1,
) -> Result<PreparedAssetLaneCustodyCoordinatorV1, AssetLaneCustodyCoordinatorGuestErrorV1> {
    input.validate()?;

    let module_prepared = prepare_asset_transfer_custody_module_v1(input.module_input.clone())
        .map_err(map_module_error)?;
    let module_accepted = module_prepared.accepted;
    let module_journal_bytes = module_prepared.journal_bytes;

    let lane_result = compose_asset_lane_single_v1(
        &input.coordinator_context,
        &module_accepted.module_journal,
        &module_accepted.private_port,
        &module_accepted.effects,
    )
    .map_err(|_| AssetLaneCustodyCoordinatorGuestErrorV1::Abi)?;
    let lane_accepted = match lane_result {
        AssetLaneCompositionResultV1::Accepted(accepted) => *accepted,
        AssetLaneCompositionResultV1::Rejected(rejected) => {
            return Err(
                AssetLaneCustodyCoordinatorGuestErrorV1::CoordinatorRejected(rejected.code),
            );
        }
    };
    lane_accepted
        .validate()
        .map_err(|_| AssetLaneCustodyCoordinatorGuestErrorV1::Abi)?;
    let lane_journal_bytes = canonical_bytes_v1(&lane_accepted.lane_journal)
        .map_err(|_| AssetLaneCustodyCoordinatorGuestErrorV1::Abi)?;
    validate_journal_size_v1(
        &lane_journal_bytes,
        AssetLaneCustodyCoordinatorGuestErrorV1::LaneJournalTooLarge,
    )?;

    Ok(PreparedAssetLaneCustodyCoordinatorV1 {
        input,
        module_accepted,
        lane_accepted,
        module_journal_bytes,
        lane_journal_bytes,
    })
}

fn map_module_error(error: AssetTransferGuestErrorV1) -> AssetLaneCustodyCoordinatorGuestErrorV1 {
    match error {
        AssetTransferGuestErrorV1::EmptyInput => {
            AssetLaneCustodyCoordinatorGuestErrorV1::EmptyInput
        }
        AssetTransferGuestErrorV1::InputTooLarge => {
            AssetLaneCustodyCoordinatorGuestErrorV1::InputTooLarge
        }
        AssetTransferGuestErrorV1::Decode => AssetLaneCustodyCoordinatorGuestErrorV1::Decode,
        AssetTransferGuestErrorV1::NonCanonicalInput => {
            AssetLaneCustodyCoordinatorGuestErrorV1::NonCanonicalInput
        }
        AssetTransferGuestErrorV1::Abi => AssetLaneCustodyCoordinatorGuestErrorV1::Abi,
        AssetTransferGuestErrorV1::Rejected(code) => {
            AssetLaneCustodyCoordinatorGuestErrorV1::ModuleRejected(code)
        }
        AssetTransferGuestErrorV1::JournalTooLarge => {
            AssetLaneCustodyCoordinatorGuestErrorV1::ModuleJournalTooLarge
        }
    }
}

fn validate_input_size_v1(
    input_bytes: &[u8],
) -> Result<(), AssetLaneCustodyCoordinatorGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(AssetLaneCustodyCoordinatorGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_ASSET_LANE_CUSTODY_COORDINATOR_GUEST_INPUT_BYTES_V1 {
        return Err(AssetLaneCustodyCoordinatorGuestErrorV1::InputTooLarge);
    }
    Ok(())
}

fn validate_journal_size_v1(
    journal_bytes: &[u8],
    error: AssetLaneCustodyCoordinatorGuestErrorV1,
) -> Result<(), AssetLaneCustodyCoordinatorGuestErrorV1> {
    let journal_len = u64::try_from(journal_bytes.len()).map_err(|_| error)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(error);
    }
    Ok(())
}
