//! Closed semantic selection of the custody-complete transfer successor.
//!
//! The committed bundle at
//! `docs/specifications/asset-transfer-custody-semantic-bundle-v1.json` is the
//! specification subject of the `ASSET_TRANSFER` module release, its lane
//! coordinator release, and the governed single-lane `asset_transfer` route.
//! The family is selected only when all three governed roles carry the
//! reviewed bundle root as their `specification_root`. Semantic versions,
//! source, toolchain and image identities, status flags, callbacks, and
//! caller-supplied totals never participate in the selection. The guard
//! validates data only: it mints no witness, image, receipt, active-release,
//! or publication authority, and qualifies no image, profile, or release.

use crate::asset_transfer_types::ASSET_TRANSFER_COMMAND_KIND_V1;
use crate::canonical::{AbiErrorV1, AbiResultV1};
use crate::proof::EconomicCommandOccurrenceV1;
use crate::release::{
    EconomicProfileSnapshotV1, LaneCoordinatorRegistryV1, LaneIdV1, LaneRegistryV1, RouteRegistryV1,
};

/// Domain-separated root of the reviewed custody semantic bundle.
///
/// It is `hash_global_v1("zenodex/asset-transfer-custody-semantic-bundle/v1",
/// decoded_canonical_bundle_json)`. Runtime code keeps the reviewed literal and
/// performs no specification-file I/O. The raw file SHA-256 is a separate test
/// identity; it is not a release-selection value.
pub const ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1: &str =
    "0x02e297f6d65affbae54509516e6c5816e60e994ef2c674495884072cd0939df1";

/// Require the governed single-lane `asset_transfer` route and the reviewed
/// bundle root as the module, coordinator, and route specification root.
///
/// Rust validates its caller-constructible profile, registry, and occurrence
/// values before lookup. It deliberately defers profile activation and
/// occurrence-to-profile binding to the retained structural binder, matching
/// the public Python selector boundary. Specification roots are compared in
/// module, coordinator, route order and the first mismatch rejects.
pub fn require_asset_transfer_custody_semantics_v1(
    profile: &EconomicProfileSnapshotV1,
    lanes: &LaneRegistryV1,
    coordinators: &LaneCoordinatorRegistryV1,
    routes: &RouteRegistryV1,
    occurrence: &EconomicCommandOccurrenceV1,
) -> AbiResultV1<()> {
    profile.validate()?;
    profile.validate_registries(lanes, coordinators, routes)?;
    occurrence.validate()?;
    if occurrence.command_kind != ASSET_TRANSFER_COMMAND_KIND_V1 {
        return Err(AbiErrorV1::InvalidBinding(
            "custody semantics require an asset transfer command",
        ));
    }
    let route =
        routes.route_for_command(&occurrence.command_kind, Some(&occurrence.route_release_id))?;
    if route.ordered_lanes != [LaneIdV1::ASSET_TRANSFER] {
        return Err(AbiErrorV1::InvalidBinding(
            "custody semantics require one ASSET_TRANSFER route lane",
        ));
    }
    let selected = (
        lanes.release_for(LaneIdV1::ASSET_TRANSFER),
        coordinators.release_for(LaneIdV1::ASSET_TRANSFER),
    );
    let (Some(module), Some(coordinator)) = selected else {
        return Err(AbiErrorV1::InvalidBinding(
            "custody semantics ASSET_TRANSFER releases",
        ));
    };
    for (specification_root, field) in [
        (
            &module.specification_root,
            "custody semantics module specification root",
        ),
        (
            &coordinator.specification_root,
            "custody semantics coordinator specification root",
        ),
        (
            &route.specification_root,
            "custody semantics route specification root",
        ),
    ] {
        if specification_root.as_str() != ASSET_TRANSFER_CUSTODY_SPECIFICATION_ROOT_V1 {
            return Err(AbiErrorV1::InvalidBinding(field));
        }
    }
    Ok(())
}
