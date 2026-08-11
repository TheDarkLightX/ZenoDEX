#![no_main]

use risc0_zkvm::guest::{abort, env};
use zenodex_asset_lane_coordinator_risc0_shared::{
    prepare_asset_lane_coordinator_from_canonical_bytes_v1, ASSET_TRANSFER_MODULE_IMAGE_ID_V1,
    MAX_ASSET_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0_u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > MAX_ASSET_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1 {
        abort("asset lane coordinator input length unsupported");
    }
    let input_len = match usize::try_from(input_len) {
        Ok(value) => value,
        Err(_) => abort("asset lane coordinator input length conversion failed"),
    };
    let mut input_bytes = vec![0_u8; input_len];
    env::read_slice(&mut input_bytes);
    let prepared = match prepare_asset_lane_coordinator_from_canonical_bytes_v1(&input_bytes) {
        Ok(value) => value,
        Err(error) => abort(error.abort_message()),
    };
    verify_module_assumption(&prepared.module_journal_bytes);
    env::commit_slice(&prepared.lane_journal_bytes);
}

fn verify_module_assumption(module_journal_bytes: &[u8]) {
    match env::verify(ASSET_TRANSFER_MODULE_IMAGE_ID_V1, module_journal_bytes) {
        Ok(()) => {}
        Err(never) => match never {},
    }
}
