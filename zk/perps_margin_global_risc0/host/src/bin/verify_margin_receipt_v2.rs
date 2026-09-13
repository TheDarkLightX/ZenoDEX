//! Fixed margin V2 image using the existing measured verifier protocol.

use std::process::ExitCode;
use zenodex_perps_margin_global_risc0_host::decode_margin_receipt_v2;
use zenodex_perps_margin_global_risc0_methods::{
    ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ELF, ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ID,
};

#[path = "../../../../risc0_receipt_verifier_v1/mod.rs"]
mod endpoint;

fn main() -> ExitCode {
    endpoint::run_v1(
        ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ELF,
        ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ID,
        |bytes| decode_margin_receipt_v2(bytes).map_err(|_| ()),
    )
}
