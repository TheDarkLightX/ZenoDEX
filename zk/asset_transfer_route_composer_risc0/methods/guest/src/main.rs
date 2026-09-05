#![no_main]
use risc0_zkvm::guest::{abort, env};
use zenodex_asset_transfer_route_composer_risc0_shared::{
    prepare_asset_transfer_route_from_bytes_v1, MAX_ASSET_TRANSFER_ROUTE_INPUT_BYTES_V1,
};
risc0_zkvm::guest::entry!(main);
pub fn main() {
    let mut length = 0u32;
    env::read_slice(core::slice::from_mut(&mut length));
    let length = match usize::try_from(length) {
        Ok(value) => value,
        Err(_) => abort("asset route length conversion"),
    };
    if length == 0 || length > MAX_ASSET_TRANSFER_ROUTE_INPUT_BYTES_V1 {
        abort("asset route input bounds");
    }
    let mut bytes = vec![0u8; length];
    env::read_slice(&mut bytes);
    let prepared = match prepare_asset_transfer_route_from_bytes_v1(&bytes) {
        Ok(value) => value,
        Err(_) => abort("asset route preflight rejected"),
    };
    match env::verify(prepared.coordinator_image(), prepared.lane_journal_bytes()) {
        Ok(()) => {}
        Err(never) => match never {},
    }
    env::commit_slice(prepared.route_journal_bytes());
}
