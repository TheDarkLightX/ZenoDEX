//! Native host replay of the exact guest input. Stdout is journal bytes only.
//! An empty stdout plus nonzero exit represents failure; no receipt is issued.

use std::io::{self, Write};
use std::process::ExitCode;
use zenodex_spot_swap_global_guest::read_spot_guest_frame_v2;
use zenodex_spot_swap_global_v2::prepare_spot_swap_global_from_frame_v2;

fn main() -> ExitCode {
    let frame = match read_spot_guest_frame_v2(&mut io::stdin().lock()) {
        Ok(frame) => frame,
        Err(error) => {
            eprintln!("{error}");
            return ExitCode::from(2);
        }
    };
    match prepare_spot_swap_global_from_frame_v2(&frame) {
        Ok(journal) => match io::stdout().lock().write_all(&journal) {
            Ok(()) => ExitCode::SUCCESS,
            Err(error) => {
                eprintln!("{error}");
                ExitCode::from(3)
            }
        },
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(2)
        }
    }
}
