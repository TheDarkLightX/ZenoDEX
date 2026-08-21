#![no_main]

use risc0_zkvm::guest::{abort, env};
use zenodex_zdex_fee_allocation_risc0_shared::{
    prepare_zdex_fee_allocation_from_canonical_bytes_v1,
    MAX_ZDEX_FEE_ALLOCATION_GUEST_INPUT_BYTES_U32_V1,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0_u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > MAX_ZDEX_FEE_ALLOCATION_GUEST_INPUT_BYTES_U32_V1 {
        abort("ZDEX fee-allocation guest input length unsupported");
    }
    let input_len = match usize::try_from(input_len) {
        Ok(value) => value,
        Err(_) => abort("ZDEX fee-allocation guest input length conversion failed"),
    };
    let mut input_bytes = vec![0_u8; input_len];
    env::read_slice(&mut input_bytes);
    let prepared = match prepare_zdex_fee_allocation_from_canonical_bytes_v1(&input_bytes) {
        Ok(value) => value,
        Err(error) => abort(error.abort_message()),
    };
    env::commit_slice(&prepared.journal_bytes);
}
