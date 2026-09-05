//! Candidate custody-complete ASSET transfer preflight.
//!
//! This crate retains the V1 wire values and legacy error/result types while
//! selecting the custody-complete transition for deterministic comparison.
//! It has no image, receipt, release, or publication authority.

pub use zenodex_asset_transfer_module_risc0_shared::{
    canonical_asset_transfer_guest_input_bytes_v1, AssetTransferGuestErrorV1,
    PreparedAssetTransferModuleV1, MAX_ASSET_TRANSFER_GUEST_INPUT_BYTES_U32_V1,
    MAX_ASSET_TRANSFER_GUEST_INPUT_BYTES_V1,
};
use zenodex_global_settlement_abi_v1::{
    canonical_bytes_v1, transition_asset_transfer_lane_module_custody_v1,
    AssetTransferLaneModuleInputV1, AssetTransferLaneModuleResultV1, MAX_JOURNAL_BYTES_V1,
};

/// Prepare one custody-complete V1 transfer using the statically selected
/// custody transition exactly once.
pub fn prepare_asset_transfer_custody_module_v1(
    input: AssetTransferLaneModuleInputV1,
) -> Result<PreparedAssetTransferModuleV1, AssetTransferGuestErrorV1> {
    input
        .validate()
        .map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    let result = transition_asset_transfer_lane_module_custody_v1(&input)
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

/// Decode and prepare only an exactly canonical, size-bounded V1 input.
pub fn prepare_asset_transfer_custody_module_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedAssetTransferModuleV1, AssetTransferGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let input: AssetTransferLaneModuleInputV1 =
        serde_json::from_slice(input_bytes).map_err(|_| AssetTransferGuestErrorV1::Decode)?;
    let canonical = canonical_bytes_v1(&input).map_err(|_| AssetTransferGuestErrorV1::Abi)?;
    if canonical != input_bytes {
        return Err(AssetTransferGuestErrorV1::NonCanonicalInput);
    }
    prepare_asset_transfer_custody_module_v1(input)
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
