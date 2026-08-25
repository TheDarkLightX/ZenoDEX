#![no_main]

use risc0_zkvm::guest::{abort, env};
use zenodex_perps_margin_lane_coordinator_risc0_shared::{
    prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1,
    MAX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1, PERPS_MARGIN_MODULE_IMAGE_ID_V1,
};

risc0_zkvm::guest::entry!(main);

struct VerifiedPerpsMarginModuleAssumptionV1;

pub fn main() {
    let mut input_len = 0_u32;
    env::read_slice(core::slice::from_mut(&mut input_len));
    if input_len == 0 || input_len > MAX_PERPS_MARGIN_LANE_COORDINATOR_GUEST_INPUT_BYTES_U32_V1 {
        abort("perps margin lane coordinator input length unsupported");
    }
    let input_len = match usize::try_from(input_len) {
        Ok(value) => value,
        Err(_) => abort("perps margin lane coordinator input length conversion failed"),
    };
    let mut input_bytes = vec![0_u8; input_len];
    env::read_slice(&mut input_bytes);
    let prepared = match prepare_perps_margin_lane_coordinator_from_canonical_bytes_v1(&input_bytes)
    {
        Ok(value) => value,
        Err(error) => abort(error.abort_message()),
    };
    let verified_module = verify_module_assumption(&prepared.module_journal_bytes);
    commit_verified_lane_journal(&prepared.lane_journal_bytes, verified_module);
}

fn verify_module_assumption(module_journal_bytes: &[u8]) -> VerifiedPerpsMarginModuleAssumptionV1 {
    match env::verify(PERPS_MARGIN_MODULE_IMAGE_ID_V1, module_journal_bytes) {
        Ok(()) => VerifiedPerpsMarginModuleAssumptionV1,
        Err(never) => match never {},
    }
}

fn commit_verified_lane_journal(
    lane_journal_bytes: &[u8],
    _verified_module: VerifiedPerpsMarginModuleAssumptionV1,
) {
    env::commit_slice(lane_journal_bytes);
}
