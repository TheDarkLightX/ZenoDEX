#![no_std]

//! Governed root identity for the source-opened Spot V6 L2 receipt.

use zenodex_zrpf_protocol_v3::{CommitmentV3, ProfileIdV3, ProgramIdV3};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_spot_value_aggregate_l2_policy_v6::{
    source_opened_spot_value_aggregate_l2_manifest_root_v6,
    source_opened_spot_value_aggregate_l2_profile_id_v6,
};
use zenodex_zrpf_risc0_value_aggregate_shared::ValueAggregateRecompositionErrorV5;

pub const PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6: [u32; 8] = [
    3_029_634_908,
    3_574_245_293,
    3_328_839_098,
    1_426_090_941,
    3_276_333_481,
    2_066_626_345,
    1_225_959_460,
    1_873_217_535,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct GovernedSourceOpenedSpotValueAggregateRootIdentityV6 {
    expected_image_id: [u32; 8],
    expected_program_id: ProgramIdV3,
    expected_profile_id: ProfileIdV3,
    expected_manifest_root: CommitmentV3,
}

impl GovernedSourceOpenedSpotValueAggregateRootIdentityV6 {
    pub const fn expected_image_id(self) -> [u32; 8] {
        self.expected_image_id
    }

    pub const fn expected_program_id(self) -> ProgramIdV3 {
        self.expected_program_id
    }

    pub const fn expected_profile_id(self) -> ProfileIdV3 {
        self.expected_profile_id
    }

    pub const fn expected_manifest_root(self) -> CommitmentV3 {
        self.expected_manifest_root
    }
}

pub fn pinned_source_opened_spot_value_aggregate_l2_root_identity_v6(
) -> Result<GovernedSourceOpenedSpotValueAggregateRootIdentityV6, ValueAggregateRecompositionErrorV5>
{
    let program_id =
        program_id_from_risc0_words_v3(PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6)
            .map_err(|_| ValueAggregateRecompositionErrorV5::InvalidPolicy("l2_root_program"))?;
    Ok(GovernedSourceOpenedSpotValueAggregateRootIdentityV6 {
        expected_image_id: PINNED_SOURCE_OPENED_SPOT_VALUE_AGGREGATE_L2_IMAGE_ID_V6,
        expected_program_id: program_id,
        expected_profile_id: source_opened_spot_value_aggregate_l2_profile_id_v6()?,
        expected_manifest_root: source_opened_spot_value_aggregate_l2_manifest_root_v6(program_id)?,
    })
}
