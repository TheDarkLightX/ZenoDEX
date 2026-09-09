//! Bounded binary frame for custody-aware global statement inputs.
//!
//! Framing is checked in full before any JSON component is decoded. Decoded
//! values are passed to the existing statement producer and gain no additional
//! proof, receipt, publication, settlement, or production authority.

use crate::asset_lane_coordinator_types::{AssetLaneCommandV2, AssetLaneRouteV2};
use crate::asset_lane_custody_state::AssetLaneCustodyStateV2;
use crate::asset_lane_custody_statement::{
    prepare_asset_lane_custody_global_statement_v2, AssetLaneCustodyStatementResultV2,
};
use crate::asset_lane_state::AssetLaneContextV2;
use crate::asset_transfer_types::AssetTransferCommandV2;
use crate::canonical::{
    decode_canonical_v2, AbiErrorV2, AbiResultV2, MAX_CANONICAL_INPUT_BYTES_V2,
};
use crate::global_state::GlobalEconomicStateV2;
use crate::managed_asset_lifecycle_types::ManagedAssetLifecycleCommandV2;

pub const ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2: &[u8; 8] = b"ZDXCGV2\0";
pub const MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2: usize =
    ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2.len() + 1 + 5 * (4 + MAX_CANONICAL_INPUT_BYTES_V2);

const FRAME_STRUCTURE: &str = "asset lane custody global frame structure";
const FRAME_COMPONENT_BYTES: &str = "asset lane custody global frame component bytes";

fn parse_frame(raw: &[u8]) -> AbiResultV2<(AssetLaneRouteV2, [&[u8]; 5])> {
    if raw.len() > MAX_ASSET_LANE_CUSTODY_GLOBAL_FRAME_BYTES_V2 {
        return Err(AbiErrorV2::InvalidBounds(
            "asset lane custody global frame bytes",
        ));
    }
    let header_end = ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2
        .len()
        .checked_add(1)
        .ok_or(AbiErrorV2::InvalidBounds(FRAME_STRUCTURE))?;
    let header = raw
        .get(..header_end)
        .ok_or(AbiErrorV2::InvalidBounds(FRAME_STRUCTURE))?;
    if &header[..ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2.len()]
        != ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2
    {
        return Err(AbiErrorV2::InvalidBinding(
            "asset lane custody global frame magic",
        ));
    }
    let route = match header[ASSET_LANE_CUSTODY_GLOBAL_FRAME_MAGIC_V2.len()] {
        0 => AssetLaneRouteV2::TRANSFER,
        1 => AssetLaneRouteV2::MANAGED_LIFECYCLE,
        _ => {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody global frame route",
            ))
        }
    };

    let mut cursor = header_end;
    let mut components = [&raw[0..0]; 5];
    for component in &mut components {
        let length_end = cursor
            .checked_add(4)
            .ok_or(AbiErrorV2::InvalidBounds(FRAME_STRUCTURE))?;
        let length_slice = raw
            .get(cursor..length_end)
            .ok_or(AbiErrorV2::InvalidBounds(FRAME_STRUCTURE))?;
        let mut length_bytes = [0_u8; 4];
        length_bytes.copy_from_slice(length_slice);
        let length = u32::from_le_bytes(length_bytes) as usize;
        if length == 0 || length > MAX_CANONICAL_INPUT_BYTES_V2 {
            return Err(AbiErrorV2::InvalidBounds(FRAME_COMPONENT_BYTES));
        }
        cursor = length_end;
        let component_end = cursor
            .checked_add(length)
            .ok_or(AbiErrorV2::InvalidBounds(FRAME_STRUCTURE))?;
        *component = raw
            .get(cursor..component_end)
            .ok_or(AbiErrorV2::InvalidBounds(FRAME_STRUCTURE))?;
        cursor = component_end;
    }
    if cursor != raw.len() {
        return Err(AbiErrorV2::InvalidBounds(FRAME_STRUCTURE));
    }
    Ok((route, components))
}

pub fn prepare_asset_lane_custody_global_frame_v2(
    raw: &[u8],
) -> AbiResultV2<AssetLaneCustodyStatementResultV2> {
    let (route, [context_raw, pre_state_raw, command_raw, global_pre_raw, global_post_raw]) =
        parse_frame(raw)?;
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
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody global frame route",
            ));
        }
    };
    let global_pre = decode_canonical_v2::<GlobalEconomicStateV2>(global_pre_raw)?;
    let global_post = decode_canonical_v2::<GlobalEconomicStateV2>(global_post_raw)?;
    prepare_asset_lane_custody_global_statement_v2(
        &context,
        &pre_state,
        &command,
        &global_pre,
        &global_post,
    )
}
