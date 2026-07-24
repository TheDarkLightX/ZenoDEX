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

use receipt_verified::ReceiptVerifiedLevelOneInputV5;

risc0_zkvm::guest::entry!(main);

const _: () = assert!(MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 == 524_324);
const _: () = assert!(MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 == 65_536);

const PINNED_SPOT_VALUE_V4_IMAGE_ID: [u32; 8] = [
    3_473_282_264,
    1_999_634_215,
    547_286_378,
    2_333_271_038,
    3_834_090_373,
    2_085_707_079,
    2_388_587_125,
    1_886_015_318,
];

mod receipt_verified {
    use alloc::vec;
    use risc0_zkvm::guest::env;
    use zenodex_zrpf_protocol_v3::{decode_exact_node_journal_v4, ProposedValueAggregateV5};
    use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
    use zenodex_zrpf_risc0_value_aggregate_shared::{
        compose_value_aggregate_level_one_after_receipt_verification_v5,
        GovernedValueChildIdentityV5, ValueAggregateLevelOneInputV5,
        ValueAggregateRecompositionErrorV5, ValueAggregateRecompositionPolicyV5,
    };
    use zenodex_zrpf_risc0_value_node_shared::{
        spot_value_leaf_manifest_root_v4, spot_value_leaf_profile_id_v4,
        PINNED_V1_ADAPTER_IMAGE_ID_A,
    };

    use super::PINNED_SPOT_VALUE_V4_IMAGE_ID;

    /// Guest-local capability created only after every exact child claim has
    /// passed RISC0 assumption verification under the governed V4 image.
    pub(super) struct ReceiptVerifiedLevelOneInputV5 {
        input: ValueAggregateLevelOneInputV5,
    }

    impl ReceiptVerifiedLevelOneInputV5 {
        pub(super) fn authenticate(input: ValueAggregateLevelOneInputV5) -> Self {
            for child_journal_bytes in input.child_journal_bytes() {
                match env::verify(
                    PINNED_SPOT_VALUE_V4_IMAGE_ID,
                    child_journal_bytes.as_slice(),
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
            compose_value_aggregate_level_one_after_receipt_verification_v5(&self.input, &policy)
        }
    }

    fn governed_policy_after_receipt_verification(
        input: &ValueAggregateLevelOneInputV5,
    ) -> Result<ValueAggregateRecompositionPolicyV5, ValueAggregateRecompositionErrorV5> {
        // Scope is learned from an authenticated child and committed into the
        // proposal. It is not an admission policy; downstream verification
        // must compare it with independently governed scope expectations.
        let first_bytes = input.child_journal_bytes().first().ok_or(
            ValueAggregateRecompositionErrorV5::InvalidPolicy("child_scope"),
        )?;
        let first_journal = decode_exact_node_journal_v4(first_bytes)
            .map_err(|_| ValueAggregateRecompositionErrorV5::ChildV4JournalDecode(0))?;
        let program_id = program_id_from_risc0_words_v3(PINNED_SPOT_VALUE_V4_IMAGE_ID)
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("child_program"))?;
        let adapter_program_id = program_id_from_risc0_words_v3(PINNED_V1_ADAPTER_IMAGE_ID_A)
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("adapter_program"))?;
        let profile_id = spot_value_leaf_profile_id_v4()
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("child_profile"))?;
        let manifest_root = spot_value_leaf_manifest_root_v4(program_id, adapter_program_id)
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("child_manifest"))?;
        let identity = GovernedValueChildIdentityV5::new(
            PINNED_SPOT_VALUE_V4_IMAGE_ID,
            program_id,
            profile_id,
            manifest_root,
        )?;
        let identities = vec![identity; input.child_journal_bytes().len()];
        ValueAggregateRecompositionPolicyV5::new(
            first_journal.structural().scope().clone(),
            identities,
        )
    }
}

pub fn main() {
    let input_bytes = read_bounded_input();
    // This decoder interprets only bounded framing. Child V4 journal bytes
    // remain opaque until every exact receipt assumption is verified below.
    let input = match decode_exact_value_aggregate_guest_input_v5(&input_bytes) {
        Ok(ValueAggregateGuestInputV5::LevelOne(value)) => value,
        Ok(
            ValueAggregateGuestInputV5::LevelOneSourceOpenedSpotV6(_)
            | ValueAggregateGuestInputV5::LevelTwo(_),
        ) => abort("ZRPF value aggregate L1 child wire kind rejected"),
        Err(_) => abort("ZRPF value aggregate L1 input rejected"),
    };
    let verified = ReceiptVerifiedLevelOneInputV5::authenticate(input);
    let proposal = match verified.compose() {
        Ok(value) => value,
        Err(_) => abort("ZRPF value aggregate L1 composition rejected"),
    };
    let proposal_bytes = match encode_value_aggregate_proposal_v5(&proposal) {
        Ok(value) => value,
        Err(_) => abort("ZRPF value aggregate L1 proposal encoding failed"),
    };
    if proposal_bytes.len() > MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 {
        abort("ZRPF value aggregate L1 proposal exceeds bound");
    }
    env::commit_slice(&proposal_bytes);
}

fn read_bounded_input() -> alloc::vec::Vec<u8> {
    let mut input_len = 0u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    let input_len = match usize::try_from(input_len) {
        Ok(value) if value > 0 && value <= MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5 => value,
        _ => abort("ZRPF value aggregate L1 input length unsupported"),
    };
    let mut input_bytes = vec![0u8; input_len];
    env::read_slice(&mut input_bytes);
    input_bytes
}
