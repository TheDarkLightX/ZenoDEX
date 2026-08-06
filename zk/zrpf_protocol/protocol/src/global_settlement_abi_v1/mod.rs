mod codec;
mod error;
mod lane;
mod module_release;
mod module_release_codec;
mod module_release_registry;
mod module_release_registry_codec;
mod module_release_registry_error;
mod module_release_types;
mod registry;
mod release_error;
mod release_id;

pub use codec::{
    decode_exact_global_economic_lane_registry_v1, encode_global_economic_lane_registry_v1,
};
pub use error::GlobalSettlementAbiErrorV1;
pub use lane::{EconomicLaneCommandStatusV1, EconomicLaneIdV1};
pub use module_release::LaneModuleReleaseV1;
pub use module_release_codec::{
    decode_exact_lane_module_release_v1, encode_lane_module_release_v1,
};
pub use module_release_registry::LaneModuleReleaseRegistryV1;
pub use module_release_registry_codec::{
    decode_exact_lane_module_release_registry_v1, encode_lane_module_release_registry_v1,
};
pub use module_release_registry_error::LaneModuleReleaseRegistryErrorV1;
pub use module_release_types::{
    LaneModuleMigrationCompatibilityV1, LaneModuleMigrationModeV1, LaneModuleProvenanceRootsV1,
    LaneModuleReleaseContentV1, LaneModuleReleaseStatusV1, LaneModuleResourceLimitsV1,
    LaneModuleSchemaRootsV1, LaneModuleTerminalCoverageV1, TerminalCoverageStatusV1,
};
pub use registry::{EconomicLaneRegistryEntryV1, GlobalEconomicLaneRegistryV1};
pub use release_error::LaneModuleReleaseErrorV1;
pub use release_id::LaneModuleReleaseIdV1;

pub const GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1: u16 = 1;
pub const ECONOMIC_LANE_COUNT_V1: usize = 12;
pub const MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1: usize = 1_024;
pub const LANE_MODULE_RELEASE_VERSION_V1: u16 = 1;
pub const MAX_LANE_MODULE_RELEASE_BYTES_V1: usize = 2_048;
pub const LANE_MODULE_RELEASE_REGISTRY_VERSION_V1: u16 = 1;
pub const MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1: usize = 64;
pub const MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1: usize = 131_200;
