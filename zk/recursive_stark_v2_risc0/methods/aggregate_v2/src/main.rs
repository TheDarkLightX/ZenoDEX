#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use tau_state_proof_risc0_shared_v2::{
    compose_recursive_node_journal_v2, preflight_recursive_node_input_v2, RecursiveNodeInputV2,
    RECURSIVE_NODE_V2_MAX_INPUT_BYTES,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > RECURSIVE_NODE_V2_MAX_INPUT_BYTES {
        abort("recursive aggregate v2 input length unsupported");
    }

    let input_len = match usize::try_from(input_len) {
        Ok(value) => value,
        Err(_) => abort("recursive aggregate v2 input length conversion failed"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    let input: RecursiveNodeInputV2 = match postcard::from_bytes(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("failed to decode recursive aggregate v2 input"),
    };
    let canonical_input_bytes = match postcard::to_allocvec(&input) {
        Ok(value) => value,
        Err(_) => abort("failed to re-encode recursive aggregate v2 input"),
    };
    if canonical_input_bytes != input_bytes {
        abort("recursive aggregate v2 input encoding is not canonical");
    }

    let immediate_claims = match preflight_recursive_node_input_v2(&input) {
        Ok(value) => value,
        Err(_) => abort("recursive aggregate v2 input preflight rejected"),
    };
    for claim in &immediate_claims {
        match env::verify(claim.image_id, claim.journal_bytes.as_ref()) {
            Ok(()) => {}
            Err(never) => match never {},
        }
    }

    let journal = match compose_recursive_node_journal_v2(&input) {
        Ok(value) => value,
        Err(_) => abort("recursive aggregate v2 composition rejected"),
    };
    let journal_bytes = match postcard::to_allocvec(&journal) {
        Ok(value) => value,
        Err(_) => abort("failed to encode recursive aggregate v2 journal"),
    };
    env::commit_slice(&journal_bytes);
}
