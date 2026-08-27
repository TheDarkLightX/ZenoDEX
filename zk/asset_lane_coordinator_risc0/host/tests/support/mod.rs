mod authenticated_command;
mod governed_registries;
mod governed_scenario;

use zenodex_asset_lane_coordinator_risc0_shared::AssetLaneCoordinatorGuestInputV1;
use zenodex_global_settlement_abi_v1::{
    AuthenticatedEconomicCommandV1, EconomicCommandOccurrenceV1, EconomicProfileSnapshotV1,
    LaneCoordinatorRegistryV1, LaneRegistryV1, RootV1, RouteRegistryV1,
};

pub use governed_scenario::release_aware_asset_lane_fixture_v1;

pub struct ReleaseAwareAssetLaneFixtureV1 {
    pub profile: EconomicProfileSnapshotV1,
    pub lanes: LaneRegistryV1,
    pub coordinators: LaneCoordinatorRegistryV1,
    pub routes: RouteRegistryV1,
    pub occurrence: EconomicCommandOccurrenceV1,
    pub authenticated_command: AuthenticatedEconomicCommandV1,
    pub guest_input: AssetLaneCoordinatorGuestInputV1,
}

pub fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "release-aware asset lane fixture root",
        false,
    )
    .unwrap()
}
