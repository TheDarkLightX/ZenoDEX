#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::env;
use tau_state_proof_risc0_shared::{
    execute_perps_np_transition_v1, execute_state_proof_input_v1, execute_zusd_transition_v1,
    ZenoProofInputV1,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let mut input_bytes = vec![0u8; input_len as usize];
    env::read_slice(&mut input_bytes);
    let input: ZenoProofInputV1 =
        postcard::from_bytes(&input_bytes).expect("failed to decode postcard proof input");
    match input {
        ZenoProofInputV1::Spot(input) => {
            let journal =
                execute_state_proof_input_v1(input).expect("tauswap proof transition rejected");
            commit_journal(&journal);
        }
        ZenoProofInputV1::PerpsNp(input) => {
            let journal =
                execute_perps_np_transition_v1(input).expect("perps np proof transition rejected");
            commit_journal(&journal);
        }
        ZenoProofInputV1::Zusd(input) => {
            let journal =
                execute_zusd_transition_v1(input).expect("zusd proof transition rejected");
            commit_journal(&journal);
        }
    }
}

fn commit_journal<T: serde::Serialize>(journal: &T) {
    let journal_bytes = postcard::to_allocvec(journal).expect("failed to encode postcard journal");
    env::commit_slice(&journal_bytes);
}
