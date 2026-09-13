//! Bounded native replay transport for Python/guest correspondence tests.
//! This executable checks no cryptographic receipt and grants no authority.

use std::io::{self, Read, Write};
use zenodex_perps_margin_global_v2::{
    prepare_perps_margin_global_from_frame_v2, MAX_PERPS_MARGIN_FRAME_BYTES_V2,
};

fn run() -> Result<(), Box<dyn std::error::Error>> {
    let limit = u64::try_from(MAX_PERPS_MARGIN_FRAME_BYTES_V2)?
        .checked_add(1)
        .ok_or("frame bound overflow")?;
    let mut frame = Vec::new();
    io::stdin().take(limit).read_to_end(&mut frame)?;
    let journal = prepare_perps_margin_global_from_frame_v2(&frame)?;
    io::stdout().write_all(&journal)?;
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(2);
    }
}
