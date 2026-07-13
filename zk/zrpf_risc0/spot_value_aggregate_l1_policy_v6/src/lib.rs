#![no_std]

//! Cycle-free governed identity policy for source-opened Spot V6 L1.
//!
//! The leaf identity is pinned here and compiler-visible to the L1 guest. The
//! L1 program identity is supplied only by its receipt-verifying parent, so no
//! self-image field enters the L1 guest ABI.

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, ProfileIdV3, ProgramIdV3};
use zenodex_zrpf_risc0_shared::{profile_id_v3, program_id_from_risc0_words_v3};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    source_opened_spot_value_leaf_profile_id_v6,
    source_opened_spot_value_leaf_program_manifest_root_v6,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5,
};

pub const PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6: [u32; 8] = [
    521_780_439,
    1_746_029_462,
    3_039_308_085,
    4_098_244_711,
    3_250_819_727,
    2_804_917_875,
    1_420_521_270,
    3_737_106_208,
];

const L1_PROFILE_V6: &str = "zrpf_source_opened_spot_value_aggregate_l1_v6";
const L1_MANIFEST_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot_value_aggregate_l1_manifest.v6";
const L1_MANIFEST_CLASS_V6: &[u8] =
    b"source_opened_spot_value_aggregate_l1_v6_exact_child_identity";

pub fn pinned_source_opened_spot_value_leaf_identity_v6(
) -> Result<GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5> {
    let program_id =
        program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6)
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("leaf_program"))?;
    let profile_id = source_opened_spot_value_leaf_profile_id_v6()
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("leaf_profile"))?;
    let manifest_root = source_opened_spot_value_leaf_program_manifest_root_v6(program_id)
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("leaf_manifest"))?;
    GovernedValueChildIdentityV5::new(
        PINNED_SOURCE_OPENED_SPOT_VALUE_LEAF_IMAGE_ID_V6,
        program_id,
        profile_id,
        manifest_root,
    )
}

pub fn source_opened_spot_value_aggregate_l1_profile_id_v6(
) -> Result<ProfileIdV3, ValueAggregateRecompositionErrorV5> {
    profile_id_v3(L1_PROFILE_V6)
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_profile"))
}

pub fn source_opened_spot_value_aggregate_l1_manifest_root_v6(
    l1_program_id: ProgramIdV3,
) -> Result<CommitmentV3, ValueAggregateRecompositionErrorV5> {
    let leaf = pinned_source_opened_spot_value_leaf_identity_v6()?;
    hash_framed(
        L1_MANIFEST_DOMAIN_V6,
        &[
            l1_program_id.as_bytes(),
            source_opened_spot_value_aggregate_l1_profile_id_v6()?.as_bytes(),
            leaf.expected_program_id().as_bytes(),
            leaf.expected_profile_id().as_bytes(),
            leaf.expected_manifest_root().as_bytes(),
            L1_MANIFEST_CLASS_V6,
        ],
    )
}

fn hash_framed(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<CommitmentV3, ValueAggregateRecompositionErrorV5> {
    let mut hasher = Sha256::new();
    let domain_len = u16::try_from(domain.len())
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_domain"))?;
    hasher.update(domain_len.to_be_bytes());
    hasher.update(domain);
    for field in fields {
        let field_len = u32::try_from(field.len())
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_field"))?;
        hasher.update(field_len.to_be_bytes());
        hasher.update(field);
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_manifest"))
}
