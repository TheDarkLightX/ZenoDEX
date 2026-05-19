#![no_std]
#![no_main]

extern crate alloc;

use risc0_zkvm::guest::env;
use tau_state_proof_risc0_shared::{execute_state_proof_input_v1, StateProofInputV1};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let input: StateProofInputV1 = env::read();
    let journal =
        execute_state_proof_input_v1(input).expect("ZenoDEX spot proof transition rejected");
    env::commit(&journal);
}
