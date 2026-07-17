#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use tau_state_proof_risc0_shared::{
    compose_zusd_recursive_leaf_summary_v1, ZusdRecursiveLeafInputV1,
    RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES,
};
use tau_state_proof_risc0_zusd_policy::validate_zusd_recursive_baseline_input_v1;

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES {
        abort("recursive zUSD leaf input length unsupported");
    }
    let mut input_bytes = vec![0u8; input_len as usize];
    env::read_slice(&mut input_bytes);
    let input: ZusdRecursiveLeafInputV1 = match postcard::from_bytes(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("failed to decode recursive zUSD leaf input"),
    };
    if let Err(error) = validate_zusd_recursive_baseline_input_v1(&input) {
        abort(error.as_str());
    }
    let summary = match compose_zusd_recursive_leaf_summary_v1(input) {
        Ok(value) => value,
        Err(_) => abort("recursive zUSD leaf transition rejected"),
    };
    let journal_bytes = match postcard::to_allocvec(&summary) {
        Ok(value) => value,
        Err(_) => abort("failed to encode recursive zUSD leaf journal"),
    };
    env::commit_slice(&journal_bytes);
}
