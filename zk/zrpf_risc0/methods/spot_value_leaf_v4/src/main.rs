#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::{encode_node_journal_v4, MAX_NODE_JOURNAL_BYTES_V4};
use zenodex_zrpf_risc0_value_node_shared::{
    decode_exact_raw_spot_value_leaf_input_v4, MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4,
};

use receipt_verified::ReceiptVerifiedSpotValueLeafInputV4;

risc0_zkvm::guest::entry!(main);

const _: () = assert!(MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4 == 17_260);
const _: () = assert!(MAX_NODE_JOURNAL_BYTES_V4 == 65_536);

mod receipt_verified {
    use risc0_zkvm::guest::env;
    use zenodex_zrpf_protocol_v3::NodeJournalV4;
    use zenodex_zrpf_risc0_value_node_shared::{
        propose_spot_value_leaf_v4, RawSpotValueLeafInputV4, SpotValueLeafProposalErrorV4,
        PINNED_V1_ADAPTER_IMAGE_ID_A,
    };

    /// Guest-local typestate constructible only by exact receipt verification.
    pub(super) struct ReceiptVerifiedSpotValueLeafInputV4 {
        raw: RawSpotValueLeafInputV4,
    }

    impl ReceiptVerifiedSpotValueLeafInputV4 {
        pub(super) fn authenticate(raw: RawSpotValueLeafInputV4) -> Self {
            match env::verify(PINNED_V1_ADAPTER_IMAGE_ID_A, raw.adapter_journal_bytes()) {
                Ok(()) => {}
                Err(never) => match never {},
            }
            Self { raw }
        }

        pub(super) fn propose(&self) -> Result<NodeJournalV4, SpotValueLeafProposalErrorV4> {
            propose_spot_value_leaf_v4(&self.raw)
        }
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    // This framing decode keeps the adapter journal and semantic witness
    // opaque. The witness first gains meaning inside `propose`, after the
    // exact journal bytes have passed `env::verify` above.
    let raw = match decode_exact_raw_spot_value_leaf_input_v4(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V4 Spot value leaf input rejected"),
    };
    let verified = ReceiptVerifiedSpotValueLeafInputV4::authenticate(raw);
    let journal = match verified.propose() {
        Ok(value) => value,
        Err(_) => abort("ZRPF V4 Spot value leaf proposal rejected"),
    };
    let journal_bytes = match encode_node_journal_v4(&journal) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V4 Spot value leaf journal encoding failed"),
    };
    if journal_bytes.len() > MAX_NODE_JOURNAL_BYTES_V4 {
        abort("ZRPF V4 Spot value leaf journal exceeds bound");
    }
    env::commit_slice(&journal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_SPOT_VALUE_LEAF_INPUT_BYTES_V4 => value,
        _ => abort("ZRPF V4 Spot value leaf input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
