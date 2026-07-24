#![no_std]
#![no_main]

extern crate alloc;

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::{
    encode_value_aggregate_proposal_v5, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    decode_exact_value_aggregate_guest_input_v5, ValueAggregateGuestInputV5,
    MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5,
};

use receipt_verified::ReceiptVerifiedSpotLevelTwoInputV6;

risc0_zkvm::guest::entry!(main);

mod receipt_verified {
    use alloc::vec;
    use risc0_zkvm::guest::env;
    use zenodex_zrpf_protocol_v3::{
        decode_exact_value_aggregate_proposal_v5, ProposedValueAggregateV5,
    };
    use zenodex_zrpf_risc0_spot_value_aggregate_l2_policy_v6::{
        pinned_source_opened_spot_value_aggregate_l1_identity_v6,
        PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
    };
    use zenodex_zrpf_risc0_value_aggregate_shared::{
        compose_value_aggregate_level_two_after_receipt_verification_v5,
        ValueAggregateLevelTwoInputV5, ValueAggregateRecompositionErrorV5,
        ValueAggregateRecompositionPolicyV5,
    };

    /// Guest-local capability constructed only after every exact L1 proposal
    /// passes assumption verification under the V6-only L1 image.
    pub(super) struct ReceiptVerifiedSpotLevelTwoInputV6 {
        input: ValueAggregateLevelTwoInputV5,
    }

    impl ReceiptVerifiedSpotLevelTwoInputV6 {
        pub(super) fn authenticate(input: ValueAggregateLevelTwoInputV5) -> Self {
            for child_proposal_bytes in input.child_proposal_bytes() {
                match env::verify(
                    PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
                    child_proposal_bytes.as_slice(),
                ) {
                    Ok(()) => {}
                    Err(never) => match never {},
                }
            }
            Self { input }
        }

        pub(super) fn compose(
            &self,
        ) -> Result<ProposedValueAggregateV5, ValueAggregateRecompositionErrorV5> {
            let first_bytes = self.input.child_proposal_bytes().first().ok_or(
                ValueAggregateRecompositionErrorV5::InvalidPolicy("child_scope"),
            )?;
            let first = decode_exact_value_aggregate_proposal_v5(first_bytes)
                .map_err(|_| ValueAggregateRecompositionErrorV5::ChildV5ProposalDecode(0))?;
            let identity = pinned_source_opened_spot_value_aggregate_l1_identity_v6()?;
            let policy = ValueAggregateRecompositionPolicyV5::new(
                first.scope().clone(),
                vec![identity; self.input.child_proposal_bytes().len()],
            )?;
            compose_value_aggregate_level_two_after_receipt_verification_v5(&self.input, &policy)
        }
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    let input = match decode_exact_value_aggregate_guest_input_v5(&input_bytes) {
        Ok(ValueAggregateGuestInputV5::LevelTwo(value)) => value,
        Ok(_) => abort("ZRPF source-opened Spot V6 L2 child wire kind rejected"),
        Err(_) => abort("ZRPF source-opened Spot V6 L2 input rejected"),
    };
    let verified = ReceiptVerifiedSpotLevelTwoInputV6::authenticate(input);
    let proposal = match verified.compose() {
        Ok(value) => value,
        Err(_) => abort("ZRPF source-opened Spot V6 L2 composition rejected"),
    };
    let proposal_bytes = match encode_value_aggregate_proposal_v5(&proposal) {
        Ok(value) => value,
        Err(_) => abort("ZRPF source-opened Spot V6 L2 proposal encoding failed"),
    };
    if proposal_bytes.len() > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        abort("ZRPF source-opened Spot V6 L2 proposal exceeds bound");
    }
    env::commit_slice(&proposal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 => value,
        _ => abort("ZRPF source-opened Spot V6 L2 input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
