#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use tau_state_proof_risc0_shared::{
    compose_recursive_epoch_journal_v1, RecursiveCompositionInputV1, RecursiveEffectSummaryV1,
    RECURSIVE_AGGREGATE_MAX_INPUT_BYTES,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > RECURSIVE_AGGREGATE_MAX_INPUT_BYTES {
        abort("recursive aggregate input length unsupported");
    }

    let mut input_bytes = vec![0u8; input_len as usize];
    env::read_slice(&mut input_bytes);
    let input: RecursiveCompositionInputV1 = match postcard::from_bytes(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("failed to decode recursive aggregate input"),
    };

    for child in &input.children {
        match env::verify(
            child.descriptor.child_image_id,
            child.child_journal_bytes.as_slice(),
        ) {
            Ok(()) => {}
            Err(never) => match never {},
        }
        let decoded_summary: RecursiveEffectSummaryV1 =
            match postcard::from_bytes(&child.child_journal_bytes) {
                Ok(value) => value,
                Err(_) => abort("failed to decode recursive child summary journal"),
            };
        if decoded_summary != child.summary {
            abort("recursive child summary journal mismatch");
        }
        if decoded_summary.risc0_image_id != child.descriptor.child_image_id {
            abort("recursive child journal image id mismatch");
        }
    }

    let journal = match compose_recursive_epoch_journal_v1(&input) {
        Ok(value) => value,
        Err(_) => abort("recursive aggregate rejected"),
    };
    let journal_bytes = match postcard::to_allocvec(&journal) {
        Ok(value) => value,
        Err(_) => abort("failed to encode recursive aggregate journal"),
    };
    env::commit_slice(&journal_bytes);
}
