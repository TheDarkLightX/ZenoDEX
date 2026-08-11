#![no_main]
#![no_std]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_global_economic_epoch_risc0_shared::{
    preflight_aggregated_economic_epoch_guest_input_v1,
    preflight_command_aggregation_guest_input_v1, preflight_economic_epoch_guest_input_v1,
    GlobalEconomicRecursiveGuestInputV1, MAX_EPOCH_GUEST_INPUT_BYTES_V1,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > MAX_EPOCH_GUEST_INPUT_BYTES_V1 {
        abort("global economic epoch input length unsupported");
    }
    let input_len = match usize::try_from(input_len) {
        Ok(value) => value,
        Err(_) => abort("global economic epoch input length conversion failed"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    let input: GlobalEconomicRecursiveGuestInputV1 = match postcard::from_bytes(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("global economic epoch input decoding failed"),
    };
    let canonical_input = match postcard::to_allocvec(&input) {
        Ok(value) => value,
        Err(_) => abort("global economic epoch input re-encoding failed"),
    };
    if canonical_input != input_bytes {
        abort("global economic epoch input encoding is not canonical");
    }

    match input {
        GlobalEconomicRecursiveGuestInputV1::DirectEpoch(input) => {
            let prepared = match preflight_economic_epoch_guest_input_v1(&input) {
                Ok(value) => value,
                Err(_) => abort("direct economic epoch input preflight rejected"),
            };
            for claim in &prepared.route_claims {
                verify_assumption(claim.image_id, &claim.journal_bytes);
            }
            env::commit_slice(&prepared.certificate_journal_bytes);
        }
        GlobalEconomicRecursiveGuestInputV1::CommandAggregation(input) => {
            let prepared = match preflight_command_aggregation_guest_input_v1(&input) {
                Ok(value) => value,
                Err(_) => abort("command aggregation input preflight rejected"),
            };
            for claim in &prepared.route_claims {
                verify_assumption(claim.image_id, &claim.journal_bytes);
            }
            env::commit_slice(&prepared.aggregation_journal_bytes);
        }
        GlobalEconomicRecursiveGuestInputV1::AggregatedEpoch(input) => {
            let prepared = match preflight_aggregated_economic_epoch_guest_input_v1(&input) {
                Ok(value) => value,
                Err(_) => abort("aggregated economic epoch input preflight rejected"),
            };
            for claim in &prepared.command_aggregation_claims {
                verify_assumption(claim.image_id, &claim.journal_bytes);
            }
            env::commit_slice(&prepared.certificate_journal_bytes);
        }
    }
}

fn verify_assumption(image_id: [u32; 8], journal_bytes: &[u8]) {
    match env::verify(image_id, journal_bytes) {
        Ok(()) => {}
        Err(never) => match never {},
    }
}
