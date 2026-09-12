//! Test-only differential transport; the production transition owns all semantics.
use std::io::{self, BufRead};

use serde::Deserialize;
use zenodex_global_settlement_abi_v1::{
    transition_perps_margin_v1, PerpsMarginCommandV1, PerpsMarginContextV1, PerpsMarginResultV1,
    PerpsMarginStateV1,
};

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct Input {
    context: PerpsMarginContextV1,
    state: PerpsMarginStateV1,
    command: PerpsMarginCommandV1,
}

fn main() -> Result<(), Box<dyn std::error::Error>> {
    for line in io::stdin().lock().lines() {
        let input: Input = serde_json::from_str(&line?)?;
        let outcome = transition_perps_margin_v1(&input.context, &input.state, &input.command)?;
        let value = match outcome {
            PerpsMarginResultV1::Accepted(value) => serde_json::to_string(&*value)?,
            PerpsMarginResultV1::Rejected(value) => serde_json::to_string(&*value)?,
        };
        println!("{value}");
    }
    Ok(())
}
