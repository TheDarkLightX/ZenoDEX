#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::{encode_node_journal_v3, MAX_NODE_JOURNAL_BYTES_V3};
use zenodex_zrpf_risc0_shared::{
    decode_exact_adapter_input_v1, project_policy_bound_v1_journal, source_policy_v1,
    V1_LEAF_ADAPTER_MAX_INPUT_BYTES,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let input_bytes = read_bounded_input();
    let input = match decode_exact_adapter_input_v1(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V1 leaf adapter input rejected"),
    };
    let source_policy = source_policy_v1(input.source_kind);

    match env::verify(
        source_policy.image_id,
        input.source_journal_bytes.as_slice(),
    ) {
        Ok(()) => {}
        Err(never) => match never {},
    }

    let projection = match project_policy_bound_v1_journal(
        input.source_kind,
        &input.source_journal_bytes,
        input.assigned_leaf_ordinal,
        input.expected_adapter_image_id,
    ) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V1 leaf adapter projection rejected"),
    };
    let journal_bytes = match encode_node_journal_v3(&projection.journal) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V1 leaf adapter journal encoding failed"),
    };
    if journal_bytes.len() > MAX_NODE_JOURNAL_BYTES_V3 {
        abort("ZRPF V1 leaf adapter journal exceeds bound");
    }
    env::commit_slice(&journal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= V1_LEAF_ADAPTER_MAX_INPUT_BYTES => value,
        _ => abort("ZRPF V1 leaf adapter input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
