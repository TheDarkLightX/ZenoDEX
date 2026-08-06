mod codec;
mod error;
mod hash;
mod transition;
mod types;

pub use codec::{decode_exact_asset_transfer_leaf_input_v1, encode_asset_transfer_leaf_input_v1};
pub use error::AssetTransferErrorV1;
pub use transition::{
    execute_asset_transfer_leaf_v1, AssetTransferAcceptedV1, AssetTransferLeafOutcomeV1,
    AssetTransferMovementV1, AssetTransferRejectCodeV1,
};
pub use types::{
    AssetTransferAccountIdV1, AssetTransferAssetIdV1, AssetTransferBalanceInputV1,
    AssetTransferBalanceV1, AssetTransferCommandInputV1, AssetTransferCommandV1,
    AssetTransferLeafInputV1, AssetTransferStateInputV1, AssetTransferStateRootV1,
    AssetTransferStateV1,
};
pub use zenodex_asset_transfer_core::MAX_ASSET_TRANSFER_BALANCE_ATOMS_V1;

pub const ASSET_TRANSFER_STATE_VERSION_V1: u16 = 1;
pub const ASSET_TRANSFER_COMMAND_VERSION_V1: u16 = 1;
pub const ASSET_TRANSFER_LEAF_INPUT_VERSION_V1: u16 = 1;
pub const MAX_ASSET_TRANSFER_STATE_ENTRIES_V1: usize = 256;
pub const MAX_ASSET_TRANSFER_LEAF_INPUT_BYTES_V1: usize = 32_768;
