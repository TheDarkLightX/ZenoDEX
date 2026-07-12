#![no_std]

//! Bounded, proof-neutral recomposition for ZRPF Value Aggregate V5.
//!
//! These kernels decode exact canonical child journals, enforce a governed
//! child-identity policy, merge `SemanticSubtreeV2` values, and derive the
//! expected `ProposedValueAggregateV5`. They contain no receipt bytes and call
//! no zkVM verification syscall. Consequently, their outputs authenticate no
//! proof and grant no ledger, settlement, release, or production authority.

extern crate alloc;
#[cfg(test)]
extern crate std;

mod child;
mod error;
mod guest_input;
mod input;
mod level_one;
mod level_two;
mod policy;

pub use error::ValueAggregateRecompositionErrorV5;
pub use guest_input::{
    decode_exact_value_aggregate_guest_input_v5, encode_value_aggregate_guest_input_v5,
    ValueAggregateGuestInputErrorV5, ValueAggregateGuestInputV5,
    MAX_VALUE_AGGREGATE_GUEST_INPUT_BYTES_V5, VALUE_AGGREGATE_GUEST_INPUT_SCHEMA_V5,
};
pub use input::{ValueAggregateLevelOneInputV5, ValueAggregateLevelTwoInputV5};
pub use level_one::{
    compose_value_aggregate_level_one_after_receipt_verification_v5,
    recompose_expected_value_aggregate_level_one_v5,
};
pub use level_two::{
    compose_value_aggregate_level_two_after_receipt_verification_v5,
    recompose_expected_value_aggregate_level_two_v5,
};
pub use policy::{GovernedValueChildIdentityV5, ValueAggregateRecompositionPolicyV5};
