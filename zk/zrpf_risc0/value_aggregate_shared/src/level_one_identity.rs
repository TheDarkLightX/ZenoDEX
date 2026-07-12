use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{CommitmentV3, ProfileIdV3, ProgramIdV3};
use zenodex_zrpf_risc0_shared::{profile_id_v3, program_id_from_risc0_words_v3};

use crate::{GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5};

/// Provisional image identity produced from integration commit `a50d3666`.
///
/// Later V5 leaf work can change transitive compiler-visible metadata and thus
/// the L1 ELF image. Replace this single constant after the final clean L1
/// rebuild, before generating an L2 ELF or any proof evidence.
pub const PROVISIONAL_VALUE_AGGREGATE_L1_IMAGE_ID_V5: [u32; 8] = [
    971_199_502,
    1_799_394_310,
    4_256_751_642,
    2_084_056_584,
    150_297_395,
    2_832_573_951,
    3_430_449_384,
    2_407_034_323,
];

const VALUE_AGGREGATE_L1_PROFILE_V5: &str = "zrpf_value_aggregate_level_one_v5";
const VALUE_AGGREGATE_L1_MANIFEST_DOMAIN_V5: &[u8] = b"zenodex.zrpf.value_aggregate_l1_manifest.v5";
const VALUE_AGGREGATE_L1_MANIFEST_CLASS_V5: &[u8] =
    b"experimental_bounded_value_aggregate_level_one_v5";

/// Derive the proof-neutral protocol profile assigned to the bounded V5 L1
/// value-aggregate program. The profile authenticates no receipt by itself.
pub fn value_aggregate_level_one_profile_id_v5(
) -> Result<ProfileIdV3, ValueAggregateRecompositionErrorV5> {
    profile_id_v3(VALUE_AGGREGATE_L1_PROFILE_V5)
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_profile"))
}

/// Commit the exact L1 program, protocol profile, and experimental role.
///
/// This manifest is an identity input for an L2 verifier policy. It conveys no
/// proof, ledger, data-availability, release, or production claim.
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

/// Construct the single governed child identity currently pinned by the V5 L2
/// guest. Replace the provisional image constant before building that guest.
pub fn provisional_value_aggregate_level_one_identity_v5(
) -> Result<GovernedValueChildIdentityV5, ValueAggregateRecompositionErrorV5> {
    let program_id = program_id_from_risc0_words_v3(PROVISIONAL_VALUE_AGGREGATE_L1_IMAGE_ID_V5)
        .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l1_program"))?;
    GovernedValueChildIdentityV5::new(
        PROVISIONAL_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
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
