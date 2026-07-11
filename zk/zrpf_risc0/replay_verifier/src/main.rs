use std::env;

use zenodex_zrpf_risc0_replay_verifier::{rejection_report, run_cli};

fn main() {
    match run_cli(env::args().skip(1)) {
        Ok(report) => println!("{}", report.as_json()),
        Err(error) => {
            eprintln!("{}", rejection_report(error));
            std::process::exit(1);
        }
    }
}
