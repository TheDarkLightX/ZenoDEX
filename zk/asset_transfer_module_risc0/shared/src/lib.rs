use core::fmt;

use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, transition_asset_transfer_lane_module_v1,
    AssetTransferLaneModuleAcceptedV1, AssetTransferLaneModuleInputV1,
    AssetTransferLaneModuleResultV1, AssetTransferRejectCodeV1, MAX_JOURNAL_BYTES_V1,
};

pub const MAX_ASSET_TRANSFER_GUEST_INPUT_BYTES_V1: usize = 1_048_576;
pub const MAX_ASSET_TRANSFER_GUEST_INPUT_BYTES_U32_V1: u32 = 1_048_576;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssetTransferGuestErrorV1 {
    EmptyInput,
    InputTooLarge,
    Decode,
    NonCanonicalInput,
    Abi,
    Rejected(AssetTransferRejectCodeV1),
    JournalTooLarge,
}

impl AssetTransferGuestErrorV1 {
    pub const fn abort_message(self) -> &'static str {
        match self {
            Self::EmptyInput => "asset transfer guest input is empty",
            Self::InputTooLarge => "asset transfer guest input exceeds release bound",
            Self::Decode => "asset transfer guest input decode failed",
            Self::NonCanonicalInput => "asset transfer guest input is noncanonical",
            Self::Abi => "asset transfer guest ABI validation failed",
            Self::Rejected(_) => "asset transfer economic transition rejected",
            Self::JournalTooLarge => "asset transfer module journal exceeds ABI bound",
        }
    }
}

impl fmt::Display for AssetTransferGuestErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "asset transfer guest rejected: {self:?}")
    }
}

impl std::error::Error for AssetTransferGuestErrorV1 {}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PreparedAssetTransferModuleV1 {
    pub input: AssetTransferLaneModuleInputV1,
    pub accepted: AssetTransferLaneModuleAcceptedV1,
    pub journal_bytes: Vec<u8>,
}

pub fn canonical_asset_transfer_guest_input_bytes_v1(
    input: &AssetTransferLaneModuleInputV1,
) -> Result<Vec<u8>, AssetTransferGuestErrorV1> {
    input
        .validate()
        .map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    let bytes = canonical_bytes_v1(input).map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    validate_input_size_v1(&bytes)?;
    Ok(bytes)
}

pub fn prepare_asset_transfer_module_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedAssetTransferModuleV1, AssetTransferGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: AssetTransferLaneModuleInputV1 =
        serde_json::from_slice(input_bytes).map_err(|_| AssetTransferGuestErrorV1::Decode)?;
    let canonical = canonical_bytes_v1(&input).map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(AssetTransferGuestErrorV1::NonCanonicalInput);
    }
    prepare_asset_transfer_module_v1(input)
}

pub fn prepare_asset_transfer_module_v1(
    input: AssetTransferLaneModuleInputV1,
) -> Result<PreparedAssetTransferModuleV1, AssetTransferGuestErrorV1> {
    input
        .validate()
        .map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    let result = transition_asset_transfer_lane_module_v1(&input)
        .map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    let accepted = match result {
        AssetTransferLaneModuleResultV1::Accepted(accepted) => *accepted,
        AssetTransferLaneModuleResultV1::Rejected(rejected) => {
            return Err(AssetTransferGuestErrorV1::Rejected(rejected.code));
        }
    };
    accepted
        .validate()
        .map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    let journal_bytes =
        canonical_bytes_v1(&accepted.module_journal).map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    let journal_len = u64::try_from(journal_bytes.len())
        .map_err(|_| AssetTransferGuestErrorV1::JournalTooLarge)?;
    if journal_len == 0 || journal_len > MAX_JOURNAL_BYTES_V1 {
        return Err(AssetTransferGuestErrorV1::JournalTooLarge);
    }
    Ok(PreparedAssetTransferModuleV1 {
        input,
        accepted,
        journal_bytes,
    })
}

fn validate_input_size_v1(input_bytes: &[u8]) -> Result<(), AssetTransferGuestErrorV1> {
    if input_bytes.is_empty() {
        return Err(AssetTransferGuestErrorV1::EmptyInput);
    }
    if input_bytes.len() > MAX_ASSET_TRANSFER_GUEST_INPUT_BYTES_V1 {
        return Err(AssetTransferGuestErrorV1::InputTooLarge);
    }
    Ok(())
}
