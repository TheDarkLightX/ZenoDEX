use serde::Deserialize;
use zenodex_global_settlement_abi_v1::RootV1;

use crate::{
    prepare_zdex_tokenomics_fee_lane_coordinator_from_canonical_bytes_v1,
    prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1, validate_input_size_v1,
    PreparedZDEXTokenomicsFeeLaneCoordinatorV1, PreparedZDEXTokenomicsLaneCoordinatorV1,
    ZDEXTokenomicsLaneCoordinatorGuestErrorV1,
    ZDEX_TOKENOMICS_FEE_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1,
    ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1,
};

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PreparedZDEXTokenomicsLaneCoordinatorAnyV1 {
    Burn(Box<PreparedZDEXTokenomicsLaneCoordinatorV1>),
    FeeAllocation(Box<PreparedZDEXTokenomicsFeeLaneCoordinatorV1>),
}

impl PreparedZDEXTokenomicsLaneCoordinatorAnyV1 {
    pub fn child_image_id(&self) -> &RootV1 {
        match self {
            Self::Burn(prepared) => &prepared.input.module_release.guest_image_id,
            Self::FeeAllocation(prepared) => &prepared.input.module_release.guest_image_id,
        }
    }

    pub fn child_journal_bytes(&self) -> &[u8] {
        match self {
            Self::Burn(prepared) => &prepared.burn_journal_bytes,
            Self::FeeAllocation(prepared) => &prepared.child_journal_bytes,
        }
    }

    pub fn lane_journal_bytes(&self) -> &[u8] {
        match self {
            Self::Burn(prepared) => &prepared.lane_journal_bytes,
            Self::FeeAllocation(prepared) => &prepared.lane_journal_bytes,
        }
    }
}

#[derive(Deserialize)]
struct ZDEXTokenomicsLaneCoordinatorInputSchemaV1 {
    schema: String,
}

pub fn prepare_zdex_tokenomics_lane_coordinator_any_from_canonical_bytes_v1(
    input_bytes: &[u8],
) -> Result<PreparedZDEXTokenomicsLaneCoordinatorAnyV1, ZDEXTokenomicsLaneCoordinatorGuestErrorV1> {
    validate_input_size_v1(input_bytes)?;
    let discriminator: ZDEXTokenomicsLaneCoordinatorInputSchemaV1 =
        serde_json::from_slice(input_bytes)
            .map_err(|_| ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Decode)?;
    match discriminator.schema.as_str() {
        ZDEX_TOKENOMICS_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1 => {
            prepare_zdex_tokenomics_lane_coordinator_from_canonical_bytes_v1(input_bytes)
                .map(Box::new)
                .map(PreparedZDEXTokenomicsLaneCoordinatorAnyV1::Burn)
        }
        ZDEX_TOKENOMICS_FEE_LANE_COORDINATOR_GUEST_INPUT_SCHEMA_V1 => {
            prepare_zdex_tokenomics_fee_lane_coordinator_from_canonical_bytes_v1(input_bytes)
                .map(Box::new)
                .map(PreparedZDEXTokenomicsLaneCoordinatorAnyV1::FeeAllocation)
        }
        _ => Err(ZDEXTokenomicsLaneCoordinatorGuestErrorV1::Schema),
    }
}
