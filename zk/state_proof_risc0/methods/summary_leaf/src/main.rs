#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use tau_state_proof_risc0_shared::{
    validate_recursive_effect_summary_shape_v1, RecursiveEffectSummaryV1,
    RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES, RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES {
        abort("recursive summary leaf input length unsupported");
    }
    let mut input_bytes = vec![0u8; input_len as usize];
    env::read_slice(&mut input_bytes);
    let summary: RecursiveEffectSummaryV1 = match postcard::from_bytes(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("failed to decode recursive summary leaf input"),
    };
    if summary.proof_profile != RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1 {
        abort("recursive summary leaf profile unsupported");
    }
    if validate_recursive_effect_summary_shape_v1(&summary).is_err() {
        abort("recursive summary leaf shape rejected");
    }
    let journal_bytes = match postcard::to_allocvec(&summary) {
        Ok(value) => value,
        Err(_) => abort("failed to encode recursive summary leaf journal"),
    };
    env::commit_slice(&journal_bytes);
}
