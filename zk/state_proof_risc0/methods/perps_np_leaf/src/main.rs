#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use tau_state_proof_risc0_shared::{
    compose_perps_np_recursive_leaf_summary_v1, PerpsNpRecursiveLeafInputV1,
    RECURSIVE_PERPS_NP_LEAF_MAX_INPUT_BYTES,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > RECURSIVE_PERPS_NP_LEAF_MAX_INPUT_BYTES {
        abort("recursive perps NP leaf input length unsupported");
    }
    let mut input_bytes = vec![0u8; input_len as usize];
    env::read_slice(&mut input_bytes);
    let input: PerpsNpRecursiveLeafInputV1 = match postcard::from_bytes(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("failed to decode recursive perps NP leaf input"),
    };
    let summary = match compose_perps_np_recursive_leaf_summary_v1(input) {
        Ok(value) => value,
        Err(_) => abort("recursive perps NP leaf transition rejected"),
    };
    let journal_bytes = match postcard::to_allocvec(&summary) {
        Ok(value) => value,
        Err(_) => abort("failed to encode recursive perps NP leaf journal"),
    };
    env::commit_slice(&journal_bytes);
}
