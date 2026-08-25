#![no_main]

use risc0_zkvm::guest::{abort, env};
use zenodex_perps_margin_route_composer_risc0_shared::{
    prepare_perps_margin_route_composer_from_canonical_bytes_v1,
    MAX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_BYTES_U32_V1,
    PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1,
};

risc0_zkvm::guest::entry!(main);

struct VerifiedPerpsMarginLaneAssumptionV1;

pub fn main() {
    let mut input_len = 0_u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > MAX_PERPS_MARGIN_ROUTE_COMPOSER_GUEST_INPUT_BYTES_U32_V1 {
        abort("perps margin route input length unsupported");
    }
    let input_len = match usize::try_from(input_len) {
        Ok(value) => value,
        Err(_) => abort("perps margin route input length conversion failed"),
    };
    let mut input_bytes = vec![0_u8; input_len];
    env::read_slice(&mut input_bytes);
    let prepared = match prepare_perps_margin_route_composer_from_canonical_bytes_v1(&input_bytes) {
        Ok(value) => value,
        Err(error) => abort(error.abort_message()),
    };
    let verified_lane = verify_lane_assumption(&prepared.lane_journal_bytes);
    commit_verified_route_journal(&prepared.route_journal_bytes, verified_lane);
}

fn verify_lane_assumption(lane_journal_bytes: &[u8]) -> VerifiedPerpsMarginLaneAssumptionV1 {
    match env::verify(
        PERPS_MARGIN_LANE_COORDINATOR_IMAGE_ID_V1,
        lane_journal_bytes,
    ) {
        Ok(()) => VerifiedPerpsMarginLaneAssumptionV1,
        Err(never) => match never {},
    }
}

fn commit_verified_route_journal(
    route_journal_bytes: &[u8],
    _verified_lane: VerifiedPerpsMarginLaneAssumptionV1,
) {
    env::commit_slice(route_journal_bytes);
}
