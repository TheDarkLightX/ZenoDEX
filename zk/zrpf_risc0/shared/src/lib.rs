#![no_std]

#[cfg(all(feature = "test-only-candidate-source-policy", target_os = "zkvm"))]
compile_error!("test-only candidate source policy is forbidden on the zkVM target");

extern crate alloc;
#[cfg(test)]
extern crate std;

mod adapter_input_v1;
mod adapter_input_v2;
mod hashing_v1;
mod risc0_binding_v1;
mod source_binding_v3;
mod source_policy_v1;
mod source_policy_v2;
mod v1_leaf_adapter;
mod v2_leaf_adapter;

pub use adapter_input_v1::*;
pub use adapter_input_v2::*;
pub use hashing_v1::{
    derive_v1_adapter_compatibility_manifest_root, profile_id_v3, program_id_from_risc0_words_v3,
    risc0_image_words_to_bytes, source_transition_receipt_count_unit_id_v3,
};
pub use risc0_binding_v1::derive_risc0_verified_claim_binding_v1;
pub use source_binding_v3::SourceBindingV3;
pub use source_policy_v1::*;
pub use source_policy_v2::*;
pub use v1_leaf_adapter::*;
pub use v2_leaf_adapter::*;
