//! Fixed custody image and exact native JSON receipt codec.

use risc0_zkvm::Receipt;
use std::process::ExitCode;
use zenodex_asset_lane_custody_global_risc0_host::decode_canonical_asset_lane_custody_receipt_v2;
use zenodex_asset_lane_custody_global_risc0_methods::{
    ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ELF, ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ID,
};

#[path = "../../../../risc0_receipt_verifier_v1/mod.rs"]
mod endpoint;

fn decode_receipt_v2(receipt_bytes: &[u8]) -> Result<Receipt, ()> {
    decode_canonical_asset_lane_custody_receipt_v2(receipt_bytes).map_err(|_| ())
}

fn main() -> ExitCode {
    endpoint::run_v1(
        ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ELF,
        ZENODEX_ASSET_LANE_CUSTODY_GLOBAL_GUEST_ID,
        decode_receipt_v2,
    )
}
