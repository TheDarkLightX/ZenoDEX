#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    decode_exact_source_opened_spot_value_leaf_input_v6,
    encode_source_opened_spot_value_leaf_statement_v6,
    MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6,
    MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_BYTES_V6,
};

use receipt_verified::ReceiptVerifiedSourceOpenedSpotInputV6;

risc0_zkvm::guest::entry!(main);

const _: () = assert!(MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6 == 1_056_790);
const _: () = assert!(MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_BYTES_V6 == 65_536);

mod receipt_verified {
    use risc0_zkvm::guest::env;
    use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
        recompose_source_opened_spot_value_leaf_statement_v6, SourceOpenedSpotValueLeafEnvelopeV6,
        SourceOpenedSpotValueLeafErrorV6, SourceOpenedSpotValueLeafStatementV6,
        PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
    };

    /// Guest-local capability constructed only after the exact adapter journal
    /// bytes pass assumption verification under the V6 adapter-successor image.
    pub(super) struct ReceiptVerifiedSourceOpenedSpotInputV6 {
        envelope: SourceOpenedSpotValueLeafEnvelopeV6,
    }

    impl ReceiptVerifiedSourceOpenedSpotInputV6 {
        pub(super) fn authenticate(envelope: SourceOpenedSpotValueLeafEnvelopeV6) -> Self {
            match env::verify(
                PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
                envelope.adapter_journal_bytes(),
            ) {
                Ok(()) => {}
                Err(never) => match never {},
            }
            Self { envelope }
        }

        pub(super) fn recompose(
            &self,
        ) -> Result<SourceOpenedSpotValueLeafStatementV6, SourceOpenedSpotValueLeafErrorV6>
        {
            recompose_source_opened_spot_value_leaf_statement_v6(&self.envelope)
        }
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    // Only bounded framing and the opaque adapter journal are decoded before
    // receipt verification. Source transition bytes gain meaning inside the
    // sealed capability after the exact adapter receipt is authenticated.
    let envelope = match decode_exact_source_opened_spot_value_leaf_input_v6(&input_bytes) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V6 source-opened Spot input rejected"),
    };
    let verified = ReceiptVerifiedSourceOpenedSpotInputV6::authenticate(envelope);
    let statement = match verified.recompose() {
        Ok(value) => value,
        Err(_) => abort("ZRPF V6 source-opened Spot recomposition rejected"),
    };
    let statement_bytes = match encode_source_opened_spot_value_leaf_statement_v6(&statement) {
        Ok(value) => value,
        Err(_) => abort("ZRPF V6 source-opened Spot statement encoding failed"),
    };
    if statement_bytes.len() > MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_STATEMENT_BYTES_V6 {
        abort("ZRPF V6 source-opened Spot statement exceeds bound");
    }
    env::commit_slice(&statement_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_SOURCE_OPENED_SPOT_VALUE_LEAF_INPUT_BYTES_V6 => {
            value
        }
        _ => abort("ZRPF V6 source-opened Spot input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
