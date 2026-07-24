#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::{encode_node_journal_v3, MAX_NODE_JOURNAL_BYTES_V3};
use zenodex_zrpf_risc0_shared::{
    decode_exact_adapter_input_v2, project_policy_bound_v2_journal, source_policy_v2,
    V2_LEAF_ADAPTER_MAX_INPUT_BYTES,
};

risc0_zkvm::guest::entry!(main);

pub fn main() {
    let input_bytes = read_bounded_input();
    let input = match decode_exact_adapter_input_v2(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V2 leaf adapter input rejected"),
    };
    let source_policy = match source_policy_v2(input.source_kind) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V2 current source identity is unpinned"),
    };

    match env::verify(
        source_policy.image_id,
        input.source_journal_bytes.as_slice(),
    ) {
        Ok(()) => {}
        Err(never) => match never {},
    }

    let projection = match project_policy_bound_v2_journal(
        input.source_kind,
        &input.source_journal_bytes,
        input.assigned_leaf_ordinal,
        input.expected_adapter_image_id,
    ) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V2 leaf adapter projection rejected"),
    };
    let journal_bytes = match encode_node_journal_v3(&projection.journal) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V2 leaf adapter journal encoding failed"),
    };
    if journal_bytes.len() > MAX_NODE_JOURNAL_BYTES_V3 {
        abort("ZRPF V2 leaf adapter journal exceeds bound");
    }
    env::commit_slice(&journal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= V2_LEAF_ADAPTER_MAX_INPUT_BYTES => value,
        _ => abort("ZRPF V2 leaf adapter input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
