mod codec;
mod error;
mod lane;
mod registry;

pub use codec::{
    decode_exact_global_economic_lane_registry_v1, encode_global_economic_lane_registry_v1,
};
pub use error::GlobalSettlementAbiErrorV1;
pub use lane::{EconomicLaneCommandStatusV1, EconomicLaneIdV1};
pub use registry::{EconomicLaneRegistryEntryV1, GlobalEconomicLaneRegistryV1};

pub const GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1: u16 = 1;
pub const ECONOMIC_LANE_COUNT_V1: usize = 12;
pub const MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1: usize = 1_024;
