//! Real zkVM execution oracle for qualification; produces no receipt or authority.

use risc0_zkvm::{Executor, ExecutorEnv, ExternalProver};
use std::io::{self, Write};
use std::path::Path;
use zenodex_perps_margin_global_guest::read_margin_guest_frame_v2;
use zenodex_perps_margin_global_risc0_host::MAX_MARGIN_GUEST_CYCLES_V2;
use zenodex_perps_margin_global_risc0_methods::ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ELF;

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let args: Vec<_> = std::env::args_os().collect();
    let [_, r0vm] = args.as_slice() else {
        return Err("usage: execute_margin_frame_v2 /absolute/path/to/r0vm".into());
    };
    let r0vm = Path::new(r0vm);
    if !r0vm.is_absolute() || !r0vm.is_file() {
        return Err("r0vm must be an absolute executable path".into());
    }
    let frame = read_margin_guest_frame_v2(&mut io::stdin().lock())?;
    let size = u32::try_from(frame.len())?;
    let mut builder = ExecutorEnv::builder();
    builder.session_limit(Some(MAX_MARGIN_GUEST_CYCLES_V2));
    builder.write_slice(&size.to_le_bytes());
    builder.write_slice(&frame);
    // Deliberately omit native semantic preflight: malformed inner frames must
    // actually reach and be rejected by the compiled guest in negative tests.
    let session = ExternalProver::new("margin-execution-test", r0vm)
        .execute(builder.build()?, ZENODEX_PERPS_MARGIN_GLOBAL_GUEST_ELF)?;
    if session.exit_code != risc0_zkvm::ExitCode::Halted(0) {
        return Err("guest did not halt successfully".into());
    }
    writeln!(
        io::stderr().lock(),
        "execution only; user cycles: {}",
        session.cycles()
    )?;
    io::stdout().lock().write_all(&session.journal.bytes)?;
    Ok(())
}

fn main() -> std::process::ExitCode {
    match run() {
        Ok(()) => std::process::ExitCode::SUCCESS,
        Err(error) => {
            let _ = writeln!(io::stderr().lock(), "guest execution rejected: {error}");
            std::process::ExitCode::from(2)
        }
    }
}
