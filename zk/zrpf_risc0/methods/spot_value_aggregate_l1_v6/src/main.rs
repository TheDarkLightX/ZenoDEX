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

use receipt_verified::ReceiptVerifiedSpotLevelOneInputV6;

risc0_zkvm::guest::entry!(main);

mod receipt_verified {
    use alloc::vec;
    use risc0_zkvm::guest::env;
    use zenodex_zrpf_protocol_v3::ProposedValueAggregateV5;
    use zenodex_zrpf_risc0_spot_value_aggregate_l1_policy_v6::{
        pinned_source_opened_spot_value_leaf_identity_v6,
        PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6,
    };
    use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::decode_exact_source_opened_spot_value_leaf_statement_v6;
    use zenodex_zrpf_risc0_value_aggregate_shared::{
        compose_source_opened_spot_value_aggregate_level_one_after_receipt_verification_v6,
        ValueAggregateLevelOneInputV5, ValueAggregateRecompositionErrorV5,
        ValueAggregateRecompositionPolicyV5,
    };

    /// Guest-local capability created only after every exact V6 statement has
    /// passed RISC0 assumption verification under the governed leaf image.
    pub(super) struct ReceiptVerifiedSpotLevelOneInputV6 {
        input: ValueAggregateLevelOneInputV5,
    }

    impl ReceiptVerifiedSpotLevelOneInputV6 {
        pub(super) fn authenticate(input: ValueAggregateLevelOneInputV5) -> Self {
            for child_statement_bytes in input.child_journal_bytes() {
                match env::verify(
                    PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6,
                    child_statement_bytes.as_slice(),
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
            let policy = governed_policy_after_receipt_verification(&self.input)?;
            compose_source_opened_spot_value_aggregate_level_one_after_receipt_verification_v6(
                &self.input,
                &policy,
            )
        }
    }

    fn governed_policy_after_receipt_verification(
        input: &ValueAggregateLevelOneInputV5,
    ) -> Result<ValueAggregateRecompositionPolicyV5, ValueAggregateRecompositionErrorV5> {
        let first_bytes = input.child_journal_bytes().first().ok_or(
            ValueAggregateRecompositionErrorV5::InvalidPolicy("child_scope"),
        )?;
        let first_statement = decode_exact_source_opened_spot_value_leaf_statement_v6(first_bytes)
            .map_err(|_| ValueAggregateRecompositionErrorV5::ChildV6StatementDecode(0))?;
        let identity = pinned_source_opened_spot_value_leaf_identity_v6()?;
        ValueAggregateRecompositionPolicyV5::new(
            first_statement.structural_adapter_journal().scope().clone(),
            vec![identity; input.child_journal_bytes().len()],
        )
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    let input = match decode_exact_value_aggregate_guest_input_v5(&input_bytes) {
        Ok(ValueAggregateGuestInputV5::LevelOneSourceOpenedSpotV6(value)) => value,
        Ok(_) => abort("ZRPF source-opened Spot V6 L1 child wire kind rejected"),
        Err(_) => abort("ZRPF source-opened Spot V6 L1 input rejected"),
    };
    let verified = ReceiptVerifiedSpotLevelOneInputV6::authenticate(input);
    let proposal = match verified.compose() {
        Ok(value) => value,
        Err(_) => abort("ZRPF source-opened Spot V6 L1 composition rejected"),
    };
    let proposal_bytes = match encode_value_aggregate_proposal_v5(&proposal) {
        Ok(value) => value,
        Err(_) => abort("ZRPF source-opened Spot V6 L1 proposal encoding failed"),
    };
    if proposal_bytes.len() > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        abort("ZRPF source-opened Spot V6 L1 proposal exceeds bound");
    }
    env::commit_slice(&proposal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 => value,
        _ => abort("ZRPF source-opened Spot V6 L1 input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
