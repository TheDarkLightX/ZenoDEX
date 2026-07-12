#![no_std]
#![no_main]

extern crate alloc;

// This method authenticates and composes a bounded structural/value statement.
// It establishes no DA, schedule, carry, settlement, release, or production
// authority. A sealed outer verifier must bind this receipt to governed parent
// identity and expected scope before any downstream admission decision.

use alloc::vec;
use risc0_zkvm::guest::{abort, env};
use zenodex_zrpf_protocol_v3::{
    encode_value_aggregate_proposal_v5, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    decode_exact_value_aggregate_guest_input_v5, ValueAggregateGuestInputV5,
    MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5,
};

use receipt_verified::ReceiptVerifiedLevelTwoInputV5;

risc0_zkvm::guest::entry!(main);

const _: () = assert!(MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 == 524_324);
const _: () = assert!(MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 == 65_536);

mod receipt_verified {
    use alloc::vec;
    use risc0_zkvm::guest::env;
    use zenodex_zrpf_protocol_v3::{
        decode_exact_value_aggregate_proposal_v5, ProposedValueAggregateV5,
    };
    use zenodex_zrpf_risc0_value_aggregate_l2_policy::{
        provisional_value_aggregate_level_one_identity_v5,
        PROVISIONAL_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
    };
    use zenodex_zrpf_risc0_value_aggregate_shared::{
        compose_value_aggregate_level_two_after_receipt_verification_v5,
        ValueAggregateLevelTwoInputV5, ValueAggregateRecompositionErrorV5,
        ValueAggregateRecompositionPolicyV5,
    };

    /// Guest-local capability created only after every exact L1 child proposal
    /// has passed RISC0 assumption verification under the governed image.
    pub(super) struct ReceiptVerifiedLevelTwoInputV5 {
        input: ValueAggregateLevelTwoInputV5,
    }

    impl ReceiptVerifiedLevelTwoInputV5 {
        pub(super) fn authenticate(input: ValueAggregateLevelTwoInputV5) -> Self {
            for child_proposal_bytes in input.child_proposal_bytes() {
                match env::verify(
                    PROVISIONAL_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
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
            let policy = governed_policy_after_receipt_verification(&self.input)?;
            compose_value_aggregate_level_two_after_receipt_verification_v5(&self.input, &policy)
        }
    }

    fn governed_policy_after_receipt_verification(
        input: &ValueAggregateLevelTwoInputV5,
    ) -> Result<ValueAggregateRecompositionPolicyV5, ValueAggregateRecompositionErrorV5> {
        // Scope is learned only after all exact child receipts authenticate.
        // Downstream admission must compare it with independent expectations.
        let first_bytes = input.child_proposal_bytes().first().ok_or(
            ValueAggregateRecompositionErrorV5::InvalidPolicy("child_scope"),
        )?;
        let first_proposal = decode_exact_value_aggregate_proposal_v5(first_bytes)
            .map_err(|_| ValueAggregateRecompositionErrorV5::ChildV5ProposalDecode(0))?;
        let identity = provisional_value_aggregate_level_one_identity_v5()?;
        let identities = vec![identity; input.child_proposal_bytes().len()];
        ValueAggregateRecompositionPolicyV5::new(first_proposal.scope().clone(), identities)
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    // This decoder interprets only bounded framing. Child V5 proposal bytes
    // remain opaque until every exact receipt assumption is verified below.
    let input = match decode_exact_value_aggregate_guest_input_v5(&input_bytes) {
        Ok(ValueAggregateGuestInputV5::LevelTwo(value)) => value,
        Ok(ValueAggregateGuestInputV5::LevelOne(_)) => {
            abort("ZRPF value aggregate L2 child wire kind rejected")
        }
        Err(_) => abort("ZRPF value aggregate L2 input rejected"),
    };
    let verified = ReceiptVerifiedLevelTwoInputV5::authenticate(input);
    let proposal = match verified.compose() {
        Ok(value) => value,
        Err(_) => abort("ZRPF value aggregate L2 composition rejected"),
    };
    let proposal_bytes = match encode_value_aggregate_proposal_v5(&proposal) {
        Ok(value) => value,
        Err(_) => abort("ZRPF value aggregate L2 proposal encoding failed"),
    };
    if proposal_bytes.len() > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        abort("ZRPF value aggregate L2 proposal exceeds bound");
    }
    env::commit_slice(&proposal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 => value,
        _ => abort("ZRPF value aggregate L2 input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
