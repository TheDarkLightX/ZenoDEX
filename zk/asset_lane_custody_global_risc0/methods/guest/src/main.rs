#![no_main]

use risc0_zkvm::guest::{abort, env};
use zenodex_asset_lane_custody_global_guest::read_custody_guest_frame_v2;
use zenodex_global_settlement_abi_v2::{
    prepare_asset_lane_custody_global_frame_v2, AssetLaneCustodyStatementResultV2,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let frame = read_custody_guest_frame_v2(&mut env::stdin())
        .unwrap_or_else(|_| abort("custody V2 guest input rejected"));
    match prepare_asset_lane_custody_global_frame_v2(&frame) {
        Ok(AssetLaneCustodyStatementResultV2::Statement(bytes)) => env::commit_slice(&bytes),
        Ok(AssetLaneCustodyStatementResultV2::Rejected(_)) => abort("custody V2 command rejected"),
        Err(_) => abort("custody V2 statement invalid"),
    }
}
