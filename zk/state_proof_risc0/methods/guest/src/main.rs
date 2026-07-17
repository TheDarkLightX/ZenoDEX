#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use tau_state_proof_risc0_shared::{
    execute_perps_np_transition_v1, execute_state_proof_input_v1, execute_zusd_transition_v1,
    ZenoProofInputV1, RECURSIVE_AGGREGATE_MAX_INPUT_BYTES,
};

#[path = "../../common/zusd_proof_policy.rs"]
mod zusd_proof_policy;
use zusd_proof_policy::validate_zusd_scoped_snapshot_conservation_v1;

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > RECURSIVE_AGGREGATE_MAX_INPUT_BYTES {
        abort("recursive aggregate input length unsupported");
    }
    let mut input_bytes = vec![0u8; input_len as usize];
    env::read_slice(&mut input_bytes);
    let input: ZenoProofInputV1 = match postcard::from_bytes(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("failed to decode postcard proof input"),
    };
    match input {
        ZenoProofInputV1::Spot(input) => {
            let journal = match execute_state_proof_input_v1(input) {
                Ok(value) => value,
                Err(_) => abort("tauswap proof transition rejected"),
            };
            commit_journal(&journal);
        }
        ZenoProofInputV1::PerpsNp(input) => {
            let journal = match execute_perps_np_transition_v1(input) {
                Ok(value) => value,
                Err(_) => abort("perps np proof transition rejected"),
            };
            commit_journal(&journal);
        }
        ZenoProofInputV1::Zusd(input) => {
            if let Err(error) = validate_zusd_scoped_snapshot_conservation_v1(&input) {
                abort(error.as_str());
            }
            let journal = match execute_zusd_transition_v1(input) {
                Ok(value) => value,
                Err(_) => abort("zusd proof transition rejected"),
            };
            commit_journal(&journal);
        }
        ZenoProofInputV1::Recursive(_) => abort("recursive input requires aggregate image"),
    }
}

fn commit_journal<T: serde::Serialize>(journal: &T) {
    let journal_bytes = match postcard::to_allocvec(journal) {
        Ok(value) => value,
        Err(_) => abort("failed to encode postcard journal"),
    };
    env::commit_slice(&journal_bytes);
}
