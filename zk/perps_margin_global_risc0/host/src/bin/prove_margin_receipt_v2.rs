//! Standalone proof proposer. Takes an explicit r0vm path; it cannot publish.

use risc0_zkvm::{compute_image_id, ExecutorEnv, ExternalProver, Prover, ProverOpts};
use std::io::{self, Write};
use std::path::Path;
use std::process::ExitCode;
use zenodex_perps_margin_global_guest::read_margin_guest_frame_v2;
use zenodex_perps_margin_global_risc0_host::{
    encode_margin_receipt_v2, verify_margin_receipt_v2, MAX_MARGIN_GUEST_CYCLES_V2,
};
use zenodex_perps_margin_global_risc0_methods::{
    ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ELF, ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ID,
};
use zenodex_perps_margin_global_v2::prepare_perps_margin_global_from_frame_v2;

fn run(r0vm: &Path) -> Result<(), String> {
    if !r0vm.is_absolute() || !r0vm.is_file() {
        return Err("r0vm must name an existing absolute executable path".into());
    }
    if std::env::var_os("RISC0_DEV_MODE").is_some_and(|value| value != "0") {
        return Err("unset RISC0_DEV_MODE or set it to 0".into());
    }
    let image = ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ID;
    let elf = ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ELF;
    if image == [0; 8]
        || elf.is_empty()
        || compute_image_id(elf)
            .map_err(|_| "invalid guest ELF")?
            .as_words()
            != image
    {
        return Err("compiled margin guest image mismatch".into());
    }
    let frame = read_margin_guest_frame_v2(&mut io::stdin().lock())
        .map_err(|error| format!("input: {error}"))?;
    let journal = prepare_perps_margin_global_from_frame_v2(&frame)
        .map_err(|error| format!("statement: {error}"))?;
    let size = u32::try_from(frame.len()).map_err(|_| "frame length")?;
    let mut builder = ExecutorEnv::builder();
    builder.session_limit(Some(MAX_MARGIN_GUEST_CYCLES_V2));
    builder.write_slice(&size.to_le_bytes());
    builder.write_slice(&frame);
    let env = builder
        .build()
        .map_err(|error| format!("environment: {error}"))?;
    // Explicit IPC selection avoids environment-selected backends that ignore
    // session limits or receipt options. The r0vm process remains untrusted for
    // economic acceptance; resource enforcement assumes the pinned IPC server.
    let proof = ExternalProver::new("margin-v2", r0vm)
        .prove_with_opts(env, elf, &ProverOpts::succinct())
        .map_err(|error| format!("proving: {error}"))?;
    verify_margin_receipt_v2(&proof.receipt, image, &journal)
        .map_err(|error| format!("receipt: {error:?}"))?;
    let bytes =
        encode_margin_receipt_v2(&proof.receipt).map_err(|error| format!("encoding: {error:?}"))?;
    io::stdout()
        .lock()
        .write_all(&bytes)
        .map_err(|error| format!("output: {error}"))
}

fn main() -> ExitCode {
    let args: Vec<_> = std::env::args_os().collect();
    let result = match args.as_slice() {
        [_, r0vm] => run(Path::new(r0vm)),
        _ => Err("usage: prove_margin_receipt_v2 /absolute/path/to/r0vm".into()),
    };
    match result {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            let _ = writeln!(io::stderr().lock(), "margin proof rejected: {error}");
            ExitCode::from(2)
        }
    }
}
