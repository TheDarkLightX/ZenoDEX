use std::io::{self, Read, Write};
use std::process::ExitCode;

use zenodex_zrpf_full_blob_da_checker_v1::{check_request_bytes_v1, MAX_CHECKER_REQUEST_BYTES_V1};

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(()) => ExitCode::FAILURE,
    }
}

fn run() -> Result<(), ()> {
    let maximum = u64::try_from(MAX_CHECKER_REQUEST_BYTES_V1).map_err(|_| ())?;
    let mut request = Vec::new();
    io::stdin()
        .take(maximum.saturating_add(1))
        .read_to_end(&mut request)
        .map_err(|_| ())?;
    if request.len() > MAX_CHECKER_REQUEST_BYTES_V1 {
        return Err(());
    }
    let response = check_request_bytes_v1(&request).map_err(|_| ())?;
    let mut stdout = io::stdout().lock();
    stdout.write_all(&response).map_err(|_| ())?;
    stdout.flush().map_err(|_| ())
}
