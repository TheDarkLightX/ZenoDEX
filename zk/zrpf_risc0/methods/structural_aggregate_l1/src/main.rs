#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::{encode_node_journal_v3, MAX_NODE_JOURNAL_BYTES_V3};
use zenodex_zrpf_risc0_aggregate_shared::{
    compose_structural_aggregate_after_receipt_verification_v1,
    decode_exact_structural_aggregate_input_v1, StructuralAggregatePolicyV1,
    MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1,
};

risc0_zkvm::guest::entry!(main);

const PINNED_ADAPTER_IMAGE_ID: [u32; 8] = [
    3_045_257_841,
    281_444_177,
    3_435_235_465,
    2_147_567_259,
    867_057_786,
    252_644_892,
    735_118_677,
    1_951_735_332,
];
const POLICY: StructuralAggregatePolicyV1 =
    StructuralAggregatePolicyV1::level_one_adapter_children(PINNED_ADAPTER_IMAGE_ID);

pub fn main() {
    let input_bytes = read_bounded_input();
    let input = match decode_exact_structural_aggregate_input_v1(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("ZRPF structural aggregate L1 input rejected"),
    };

    for child_journal_bytes in &input.child_journal_bytes {
        match env::verify(
            POLICY.expected_child_image_id(),
            child_journal_bytes.as_slice(),
        ) {
            Ok(()) => {}
            Err(never) => match never {},
        }
    }

    let projection =
        match compose_structural_aggregate_after_receipt_verification_v1(&input, POLICY) {
            Ok(value) => value,
            Err(_) => abort("ZRPF structural aggregate L1 composition rejected"),
        };
    let journal_bytes = match encode_node_journal_v3(&projection.journal) {
        Ok(value) => value,
        Err(_) => abort("ZRPF structural aggregate L1 journal encoding failed"),
    };
    if journal_bytes.len() > MAX_NODE_JOURNAL_BYTES_V3 {
        abort("ZRPF structural aggregate L1 journal exceeds bound");
    }
    env::commit_slice(&journal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1 => value,
        _ => abort("ZRPF structural aggregate L1 input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
