#![cfg_attr(target_os = "zkvm", no_main)]

#[cfg(target_os = "zkvm")]
risc0_zkvm::guest::entry!(main);

#[cfg(target_os = "zkvm")]
pub fn main() {
    use risc0_zkvm::guest::{abort, env};
    use zenodex_spot_swap_global_guest::read_spot_guest_frame_v2;
    use zenodex_spot_swap_global_v2::prepare_spot_swap_global_from_frame_v2;

    let frame = match read_spot_guest_frame_v2(&mut env::stdin()) {
        Ok(frame) => frame,
        Err(_) => abort("Spot V2 input rejected"),
    };
    match prepare_spot_swap_global_from_frame_v2(&frame) {
        Ok(journal) => env::commit_slice(&journal),
        Err(_) => abort("Spot V2 transition rejected"),
    }
}

// A native build never reports zkVM execution or substitutes a fake receipt.
#[cfg(not(target_os = "zkvm"))]
fn main() -> std::process::ExitCode {
    std::process::ExitCode::from(2)
}
