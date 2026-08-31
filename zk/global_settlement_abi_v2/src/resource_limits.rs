//! Shared resource ceilings for rootable V2 asset-state and refinement values.
//!
//! These bounds are checked before traversing untrusted vectors. They constrain
//! the work admitted by the SHADOW mirror; they grant no production authority.

use crate::canonical::{AbiErrorV2, AbiResultV2};

pub const MAX_ASSETS_PER_ASSET_STATE_V2: usize = 256;
pub const MAX_BALANCE_ROWS_PER_ASSET_STATE_V2: usize = 4_096;
pub const MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2: usize = 1_048_576;
pub const MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2: usize = 64;
pub const MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2: usize = 64;

pub fn validate_asset_state_asset_count_v2(count: usize, field: &'static str) -> AbiResultV2<()> {
    validate_at_most_v2(count, MAX_ASSETS_PER_ASSET_STATE_V2, field)
}

pub fn validate_asset_state_balance_row_count_v2(
    count: usize,
    field: &'static str,
) -> AbiResultV2<()> {
    validate_at_most_v2(count, MAX_BALANCE_ROWS_PER_ASSET_STATE_V2, field)
}

pub fn validate_rootable_asset_state_canonical_bytes_v2(
    byte_count: usize,
    field: &'static str,
) -> AbiResultV2<()> {
    validate_at_most_v2(
        byte_count,
        MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
        field,
    )
}

pub fn validate_consumed_object_id_count_v2(count: usize, field: &'static str) -> AbiResultV2<()> {
    validate_at_most_v2(count, MAX_CONSUMED_OBJECT_IDS_PER_OCCURRENCE_V2, field)
}

pub fn validate_consumed_occurrence_count_v2(count: usize, field: &'static str) -> AbiResultV2<()> {
    validate_at_most_v2(count, MAX_CONSUMED_OCCURRENCES_PER_REFINEMENT_V2, field)
}

fn validate_at_most_v2(count: usize, limit: usize, field: &'static str) -> AbiResultV2<()> {
    if count > limit {
        return Err(AbiErrorV2::InvalidBounds(field));
    }
    Ok(())
}
