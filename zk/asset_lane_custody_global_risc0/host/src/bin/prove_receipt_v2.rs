//! Produces a verified Succinct receipt for one bounded custody V2 guest frame.

use std::io::{self, Write};
use std::process::ExitCode;
use zenodex_asset_lane_custody_global_risc0_host::{
    encode_canonical_asset_lane_custody_receipt_v2, prove_asset_lane_custody_succinct_v2,
    read_asset_lane_custody_guest_input_v2, AssetLaneCustodyProofHostErrorV2,
};

fn run() -> Result<(), AssetLaneCustodyProofHostErrorV2> {
    if std::env::args_os().len() != 1 {
        return Err(AssetLaneCustodyProofHostErrorV2::Arguments);
    }
    let frame = read_asset_lane_custody_guest_input_v2(&mut io::stdin().lock())?;
    let receipt = prove_asset_lane_custody_succinct_v2(&frame)?;
    let output = encode_canonical_asset_lane_custody_receipt_v2(&receipt)
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::ReceiptEncoding)?;
    io::stdout()
        .lock()
        .write_all(&output)
        .map_err(|_| AssetLaneCustodyProofHostErrorV2::ReceiptEncoding)
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            let _ = writeln!(
                io::stderr().lock(),
                "custody receipt prover rejected: {error}"
            );
            ExitCode::from(2)
        }
    }
}
