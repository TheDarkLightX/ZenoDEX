#![no_std]

//! L2-only policy ownership for the bounded ZRPF Value Aggregate V5 guest.

use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, ProfileIdV3, ProgramIdV3};
use zenodex_zrpf_risc0_shared::{profile_id_v3, program_id_from_risc0_words_v3};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5,
};

/// Pinned image identity from the final cycle-free L1 build.
///
/// The L1 normal, build, and dev dependency closure excludes this crate, so
/// updating this L2 policy cannot alter the L1 image that it identifies.
pub const PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5: [u32; 8] = [
    3_564_831_385,
    48_132_607,
    806_382_536,
    926_782_106,
    1_009_225_155,
    144_638_977,
    346_148_796,
    2_113_518_866,
];

const VALUE_AGGREGATE_L1_PROFILE_V5: &str = "zrpf_value_aggregate_level_one_v5";
const VALUE_AGGREGATE_L1_MANIFEST_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_aggregate_l1_manifest.v5";
const VALUE_AGGREGATE_L1_MANIFEST_CLASS_V5: &[u8] =
    b"experimental_bounded_value_aggregate_level_one_v5";

/// Derive the proof-neutral protocol profile assigned to the bounded V5 L1
/// program. The profile authenticates no receipt by itself.
pub fn value_aggregate_level_one_profile_id_v5(
) -> Result<ProfileIdV3, ValueAggregateRecompositionErrorV5> {
    profile_id_v3(VALUE_AGGREGATE_L1_PROFILE_V5)
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_profile"))
}

/// Commit the exact L1 program, protocol profile, and experimental role.
///
/// This proof-neutral identity input conveys no ledger, data-availability,
/// release, or production claim.
pub fn value_aggregate_level_one_manifest_root_v5(
    program_id: ProgramIdV3,
) -> Result<CommitmentV3, ValueAggregateRecompositionErrorV5> {
    let profile_id = value_aggregate_level_one_profile_id_v5()?;
    commitment_hash_framed(
        VALUE_AGGREGATE_L1_MANIFEST_DOMAIN_V5,
        &[
            program_id.as_bytes(),
            profile_id.as_bytes(),
            VALUE_AGGREGATE_L1_MANIFEST_CLASS_V5,
        ],
    )
}

/// Construct the L1 identity governed by the V5 L2 guest policy.
pub fn pinned_value_aggregate_level_one_identity_v5(
) -> Result<GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5> {
    let program_id = program_id_from_risc0_words_v3(PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5)
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_program"))?;
    GovernedValueChildIdentityV5::new(
        PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
        program_id,
        value_aggregate_level_one_profile_id_v5()?,
        value_aggregate_level_one_manifest_root_v5(program_id)?,
    )
}

fn commitment_hash_framed(
    domain: &[u8],
    fields: &[&[u8]],
) -> Result<CommitmentV3, ValueAggregateRecompositionErrorV5> {
    let mut hasher = Sha256::new();
    let domain_length = u16::try_from(domain.len())
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_manifest_domain"))?;
    hasher.update(domain_length.to_be_bytes());
    hasher.update(domain);
    for field in fields {
        let length = u32::try_from(field.len())
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_manifest_field"))?;
        hasher.update(length.to_be_bytes());
        hasher.update(field);
    }
    CommitmentV3::new(hasher.finalize().into())
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_manifest"))
}
