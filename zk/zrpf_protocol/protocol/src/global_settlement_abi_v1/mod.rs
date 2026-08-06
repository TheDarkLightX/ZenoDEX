mod codec;
mod economic_command_occurrence;
mod economic_command_occurrence_error;
mod economic_object_release_pin;
mod economic_object_release_pin_codec;
mod economic_profile_snapshot;
mod economic_profile_snapshot_codec;
mod economic_profile_snapshot_error;
mod economic_profile_snapshot_id;
mod economic_profile_snapshot_types;
mod error;
mod global_economic_effect_plan;
mod global_economic_effect_plan_bounded;
mod global_economic_effect_plan_codec;
mod global_economic_effect_plan_error;
mod global_economic_effect_plan_hash;
mod global_economic_effect_plan_reconcile;
mod global_economic_effect_plan_row_inputs;
mod global_economic_effect_plan_rows;
mod global_economic_effect_plan_types;
mod global_economic_effect_plan_validate;
mod global_economic_state;
mod global_economic_state_binding;
mod global_economic_state_codec;
mod global_economic_state_error;
mod global_economic_state_types;
mod lane;
mod lifecycle_route_resolver;
mod module_release;
mod module_release_codec;
mod module_release_registry;
mod module_release_registry_codec;
mod module_release_registry_error;
mod module_release_types;
mod registry;
mod release_error;
mod release_id;
mod route_release;
mod route_release_codec;
mod route_release_error;
mod route_release_id;
mod route_release_policy;
mod route_release_registry;
mod route_release_registry_codec;
mod route_release_registry_error;
mod route_release_registry_types;
mod route_release_roles;
mod route_release_types;

pub use codec::{
    decode_exact_global_economic_lane_registry_v1, encode_global_economic_lane_registry_v1,
};
pub use economic_command_occurrence::{
    bind_economic_command_occurrence_to_active_profile_v1,
    decode_exact_economic_command_occurrence_v1, encode_economic_command_occurrence_v1,
    EconomicCommandOccurrenceContentV1, EconomicCommandOccurrenceIdV1, EconomicCommandOccurrenceV1,
    EconomicOccurrencePositionV1, ProfileBoundEconomicCommandOccurrenceV1,
};
pub use economic_command_occurrence_error::EconomicCommandOccurrenceErrorV1;
pub use economic_object_release_pin::{
    EconomicObjectReleasePinProofV1, EconomicObjectReleasePinV1,
};
pub use economic_object_release_pin_codec::{
    decode_exact_economic_object_release_pin_proof_v1, encode_economic_object_release_pin_proof_v1,
};
pub use economic_profile_snapshot::EconomicProfileSnapshotV1;
pub use economic_profile_snapshot_codec::{
    decode_exact_economic_profile_snapshot_v1, encode_economic_profile_snapshot_v1,
};
pub use economic_profile_snapshot_error::EconomicProfileSnapshotErrorV1;
pub use economic_profile_snapshot_id::EconomicProfileIdV1;
pub use economic_profile_snapshot_types::{
    EconomicProfileRegistryRootsV1, EconomicProfileSnapshotContentV1,
    EconomicProfileTransitionModeV1,
};
pub use error::GlobalSettlementAbiErrorV1;
pub use global_economic_effect_plan::{
    bind_global_economic_effect_plan_to_occurrence_v1, GlobalEconomicEffectBodyV1,
    GlobalEconomicEffectPlanV1, OccurrenceBoundGlobalEconomicEffectPlanV1,
};
pub use global_economic_effect_plan_codec::{
    decode_exact_global_economic_effect_plan_v1, encode_global_economic_effect_plan_v1,
};
pub use global_economic_effect_plan_error::GlobalEconomicEffectPlanErrorV1;
pub use global_economic_effect_plan_row_inputs::{
    GlobalAccountMovementInputV1, GlobalCustodyEffectInputV1, GlobalExternalOutboxInputV1,
    GlobalFeeEffectInputV1, GlobalIssueBurnInputV1, GlobalLiabilityEffectInputV1,
    GlobalReserveEffectInputV1, GlobalRewardSlashInputV1,
};
pub use global_economic_effect_plan_types::{
    GlobalAssetReconciliationInputV1, GlobalAssetReconciliationV1, GlobalEconomicEffectBodyInputV1,
    GlobalEconomicEffectKindV1, GlobalEconomicEffectPlanInputV1, GlobalEconomicEffectRowV1,
    GlobalIssueBurnKindV1, GlobalOccurrenceConsumptionKindV1, GlobalRewardSlashKindV1,
};
pub use global_economic_state::GlobalEconomicStateV1;
pub use global_economic_state_binding::{
    bind_global_economic_state_to_profile_v1, bind_profile_bound_occurrence_to_global_state_v1,
    RegistryBoundGlobalEconomicStateV1, StateBoundEconomicCommandOccurrenceV1,
};
pub use global_economic_state_codec::{
    decode_exact_global_economic_state_v1, encode_global_economic_state_v1,
};
pub use global_economic_state_error::GlobalEconomicStateErrorV1;
pub use global_economic_state_types::{
    GlobalEconomicLaneStateRootV1, GlobalEconomicPartitionRootsInputV1,
    GlobalEconomicPartitionRootsV1, GlobalEconomicStateContentInputV1,
    GlobalEconomicStateContentV1, GlobalEconomicStateRootV1,
};
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
pub use route_release::RouteReleaseV1;
pub use route_release_codec::{decode_exact_route_release_v1, encode_route_release_v1};
pub use route_release_error::RouteReleaseErrorV1;
pub use route_release_id::RouteReleaseIdV1;
pub use route_release_policy::{RouteIssueBurnPolicyV1, RouteOraclePolicyV1};
pub use route_release_registry::RouteReleaseRegistryV1;
pub use route_release_registry_codec::{
    decode_exact_route_release_registry_v1, encode_route_release_registry_v1,
};
pub use route_release_registry_error::RouteReleaseRegistryErrorV1;
pub use route_release_registry_types::{RouteModuleReleaseSelectionV1, RouteSelectionKeyV1};
pub use route_release_roles::{RouteDependencyRoleV1, RouteDependencyRolesV1};
pub use route_release_types::{
    RouteDependencyLifecyclePurposeV1, RouteModuleDependencyV1, RouteReleaseContentV1,
    RouteResourceLimitsV1,
};

pub const GLOBAL_ECONOMIC_LANE_REGISTRY_VERSION_V1: u16 = 1;
pub const ECONOMIC_LANE_COUNT_V1: usize = 12;
pub const MAX_GLOBAL_ECONOMIC_LANE_REGISTRY_BYTES_V1: usize = 1_024;
pub const LANE_MODULE_RELEASE_VERSION_V1: u16 = 1;
pub const MAX_LANE_MODULE_RELEASE_BYTES_V1: usize = 2_048;
pub const LANE_MODULE_RELEASE_REGISTRY_VERSION_V1: u16 = 1;
pub const MAX_LANE_MODULE_RELEASES_PER_REGISTRY_V1: usize = 64;
pub const MAX_LANE_MODULE_RELEASE_REGISTRY_BYTES_V1: usize = 131_200;
pub const ROUTE_RELEASE_VERSION_V1: u16 = 1;
pub const MAX_ROUTE_DEPENDENCIES_V1: usize = 8;
pub const MAX_ROUTE_RELEASE_BYTES_V1: usize = 4_096;
pub const ROUTE_RELEASE_REGISTRY_VERSION_V1: u16 = 1;
pub const MAX_ROUTE_RELEASES_PER_REGISTRY_V1: usize = 256;
pub const MAX_ROUTE_RELEASE_REGISTRY_BYTES_V1: usize =
    MAX_ROUTE_RELEASES_PER_REGISTRY_V1 * MAX_ROUTE_RELEASE_BYTES_V1 + 64;
pub const ECONOMIC_PROFILE_SNAPSHOT_VERSION_V1: u16 = 1;
pub const MAX_ECONOMIC_PROFILE_SNAPSHOT_BYTES_V1: usize = 512;
pub const ECONOMIC_COMMAND_OCCURRENCE_VERSION_V1: u16 = 1;
pub const MAX_ECONOMIC_COMMAND_OCCURRENCE_BYTES_V1: usize = 16_384;
pub const GLOBAL_ECONOMIC_STATE_VERSION_V1: u16 = 1;
pub const MAX_GLOBAL_ECONOMIC_STATE_BYTES_V1: usize = 2_048;
pub const ECONOMIC_OBJECT_RELEASE_PIN_VERSION_V1: u16 = 1;
pub const MAX_ECONOMIC_OBJECT_RELEASE_PIN_PROOF_BYTES_V1: usize = 8_512;
pub const GLOBAL_ECONOMIC_EFFECT_PLAN_VERSION_V1: u16 = 1;
pub const MAX_GLOBAL_ECONOMIC_EFFECT_ROWS_V1: usize = 1_024;
pub const MAX_GLOBAL_ASSET_RECONCILIATIONS_V1: usize = 256;
pub const MAX_GLOBAL_ECONOMIC_EFFECT_PLAN_BYTES_V1: usize = 1_048_576;
