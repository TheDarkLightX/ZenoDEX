//! Canonical byte input boundary for the custody-aware asset lane successor.
//!
//! Each caller-provided value is decoded into its existing closed type before
//! transition dispatch. This adapter creates no request wire, receipt,
//! publisher, proof, settlement, or production authority.

use crate::asset_lane_coordinator_types::{AssetLaneCommandV2, AssetLaneRouteV2};
use crate::asset_lane_custody::{transition_asset_lane_custody_v2, AssetLaneCustodyResultV2};
use crate::asset_lane_custody_state::AssetLaneCustodyStateV2;
use crate::asset_lane_state::AssetLaneContextV2;
use crate::asset_transfer_types::AssetTransferCommandV2;
use crate::canonical::{decode_canonical_v2, AbiErrorV2, AbiResultV2};
use crate::managed_asset_lifecycle_types::ManagedAssetLifecycleCommandV2;

pub fn transition_asset_lane_custody_bytes_v2(
    route: AssetLaneRouteV2,
    context_raw: &[u8],
    pre_state_raw: &[u8],
    command_raw: &[u8],
) -> AbiResultV2<AssetLaneCustodyResultV2> {
    if route == AssetLaneRouteV2::COORDINATOR {
        return Err(AbiErrorV2::InvalidBinding("asset lane custody input route"));
    }

    let context = decode_canonical_v2::<AssetLaneContextV2>(context_raw)?;
    let pre_state = decode_canonical_v2::<AssetLaneCustodyStateV2>(pre_state_raw)?;
    let command = match route {
        AssetLaneRouteV2::TRANSFER => AssetLaneCommandV2::Transfer(decode_canonical_v2::<
            AssetTransferCommandV2,
        >(command_raw)?),
        AssetLaneRouteV2::MANAGED_LIFECYCLE => {
            AssetLaneCommandV2::ManagedLifecycle(decode_canonical_v2::<
                ManagedAssetLifecycleCommandV2,
            >(command_raw)?)
        }
        AssetLaneRouteV2::COORDINATOR => {
            return Err(AbiErrorV2::InvalidBinding("asset lane custody input route"));
        }
    };
    transition_asset_lane_custody_v2(&context, &pre_state, &command)
}
