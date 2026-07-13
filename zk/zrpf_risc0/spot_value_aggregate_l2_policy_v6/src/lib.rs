#![no_std]

//! Cycle-free governed identity policy for source-opened Spot V6 L2.

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, ProfileIdV3, ProgramIdV3};
use zenodex_zrpf_risc0_shared::{profile_id_v3, program_id_from_risc0_words_v3};
use zenodex_zrpf_risc0_spot_value_aggregate_l1_policy_v6::{
    source_opened_spot_value_aggregate_l1_manifest_root_v6,
    source_opened_spot_value_aggregate_l1_profile_id_v6,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5,
};

pub const PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6: [u32; 8] = [
    1_985_356_721,
    2_887_947_481,
    3_715_345_643,
    144_994_049,
    956_419_097,
    906_659_609,
    3_044_603_425,
    4_209_604_419,
];

const L2_PROFILE_V6: &str = "zrpf_source_opened_spot_value_aggregate_l2_v6";
const L2_MANIFEST_DOMAIN_V6: &[u8] =
    b"zenodex.zrpf.source_opened_spot_value_aggregate_l2_manifest.v6";
const L2_MANIFEST_CLASS_V6: &[u8] = b"source_opened_spot_value_aggregate_l2_v6_exact_l1_identity";

pub fn pinned_source_opened_spot_value_aggregate_l1_identity_v6(
) -> Result<GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5> {
    let program_id =
        program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6)
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_program"))?;
    GovernedValueChildIdentityV5::new(
        PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L1_IMAGE_ID_V6,
        program_id,
        source_opened_spot_value_aggregate_l1_profile_id_v6()?,
        source_opened_spot_value_aggregate_l1_manifest_root_v6(program_id)?,
    )
}

pub fn source_opened_spot_value_aggregate_l2_profile_id_v6(
) -> Result<ProfileIdV3, ValueAggregateRecompositionErrorV5> {
    profile_id_v3(L2_PROFILE_V6)
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l2_profile"))
}

pub fn source_opened_spot_value_aggregate_l2_manifest_root_v6(
    l2_program_id: ProgramIdV3,
) -> Result<CommitmentV3, ValueAggregateRecompositionErrorV5> {
    let l1 = pinned_source_opened_spot_value_aggregate_l1_identity_v6()?;
    let l2_profile = source_opened_spot_value_aggregate_l2_profile_id_v6()?;
    hash_framed(
        L2_MANIFEST_DOMAIN_V6,
        &[
            l2_program_id.as_bytes(),
            l2_profile.as_bytes(),
            l1.expected_program_id().as_bytes(),
            l1.expected_profile_id().as_bytes(),
            l1.expected_manifest_root().as_bytes(),
            L2_MANIFEST_CLASS_V6,
        ],
    )
}

fn hash_framed(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<CommitmentV3, ValueAggregateRecompositionErrorV5> {
    let mut hasher = Sha256::new();
    let domain_len = u16::try_from(domain.len())
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l2_domain"))?;
    hasher.update(domain_len.to_be_bytes());
    hasher.update(domain);
    for field in fields {
        let field_len = u32::try_from(field.len())
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l2_field"))?;
        hasher.update(field_len.to_be_bytes());
        hasher.update(field);
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l2_manifest"))
}
