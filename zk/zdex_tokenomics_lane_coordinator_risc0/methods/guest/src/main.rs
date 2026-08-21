#![no_main]

use risc0_zkvm::{
    guest::{abort, env},
    Digest,
};
use zenodex_zdex_tokenomics_lane_coordinator_risc0_shared::{
    prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1,
    risc0_digest_bytes_from_root_v1, MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0_u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > MAX_ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1 {
        abort("ZDEX tokenomics coordinator guest input length unsupported");
    }
    let input_len = match usize::try_from(input_len) {
        Ok(value) => value,
        Err(_) => abort("ZDEX tokenomics coordinator guest input length conversion failed"),
    };
    let mut input_bytes = vec![0_u8; input_len];
    env::read_slice(&mut input_bytes);
    let prepared =
        match prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(&input_bytes) {
            Ok(value) => value,
            Err(error) => abort(error.abort_message()),
        };
    let image_bytes =
        match risc0_digest_bytes_from_root_v1(&prepared.input.module_release.guest_image_id) {
            Ok(value) => value,
            Err(error) => abort(error.abort_message()),
        };
    let image_id = Digest::from(image_bytes);
    match env::verify(image_id, prepared.burn_journal_bytes.as_slice()) {
        Ok(()) => {}
        Err(error) => match error {},
    }
    env::commit_slice(&prepared.lane_journal_bytes);
}
