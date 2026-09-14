//! Bounded quote differential tool for exhaustive arithmetic testing.
//!
//! Test transport only. Each input line is
//! `{"mode": "exact_in" | "exact_out", "reserve_in": u64, "reserve_out": u64,
//! "amount": u64, "fee_bps": u64}`. The output is
//! `{"status": "quoted", ...}` with every quote field, or
//! `{"status": "rejected", "reason": <SpotQuoteErrorV2 name>}` where the
//! Python settlement helper raises, or `{"status": "input_error", "code": ...}`
//! for malformed lines. Reject reasons are native names; the Python side only
//! distinguishes raise from return. Lines are at most 4 KiB.

use std::io::{self, BufRead};

use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use zenodex_spot_swap_global_v2::{
    quote_cpmm_swap_exact_in_v2, quote_cpmm_swap_exact_out_v2, SpotQuoteErrorV2, SpotSwapQuoteV2,
};

const MAX_QUOTE_LINE_BYTES: usize = 4_096;

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct QuoteRequest {
    mode: String,
    reserve_in: u64,
    reserve_out: u64,
    amount: u64,
    fee_bps: u64,
}

#[derive(Serialize)]
struct QuoteResponse {
    status: &'static str,
    mode: &'static str,
    amount_in: u128,
    amount_out: u128,
    fee_paid: u128,
    net_in: u128,
    reserve_in_after: u128,
    reserve_out_after: u128,
    k_before: u128,
    k_after: u128,
    amount_out_quote: u128,
    overdelivery_gap_bps: u128,
}

fn quote(
    request: &QuoteRequest,
) -> Result<Result<SpotSwapQuoteV2, SpotQuoteErrorV2>, &'static str> {
    let reserve_in = u128::from(request.reserve_in);
    let reserve_out = u128::from(request.reserve_out);
    let amount = u128::from(request.amount);
    let fee_bps = u128::from(request.fee_bps);
    match request.mode.as_str() {
        "exact_in" => Ok(quote_cpmm_swap_exact_in_v2(
            reserve_in,
            reserve_out,
            amount,
            fee_bps,
        )),
        "exact_out" => Ok(quote_cpmm_swap_exact_out_v2(
            reserve_in,
            reserve_out,
            amount,
            fee_bps,
        )),
        _ => Err("INPUT_MODE"),
    }
}

fn response(quoted: &SpotSwapQuoteV2) -> Value {
    let body = QuoteResponse {
        status: "quoted",
        mode: quoted.mode.as_str(),
        amount_in: quoted.amount_in,
        amount_out: quoted.amount_out,
        fee_paid: quoted.fee_paid,
        net_in: quoted.net_in,
        reserve_in_after: quoted.reserve_in_after,
        reserve_out_after: quoted.reserve_out_after,
        k_before: quoted.k_before,
        k_after: quoted.k_after,
        amount_out_quote: quoted.amount_out_quote,
        overdelivery_gap_bps: quoted.overdelivery_gap_bps,
    };
    serde_json::to_value(body)
        .unwrap_or_else(|_| json!({"status": "input_error", "code": "INPUT_INTERNAL"}))
}

fn handle(line: &str) -> Value {
    let request: QuoteRequest = match serde_json::from_str(line) {
        Ok(request) => request,
        Err(_) => return json!({"status": "input_error", "code": "INPUT_JSON"}),
    };
    match quote(&request) {
        Err(code) => json!({"status": "input_error", "code": code}),
        Ok(Err(error)) => json!({"status": "rejected", "reason": error.as_str()}),
        Ok(Ok(quoted)) => response(&quoted),
    }
}

fn read_bounded_line<R: BufRead>(reader: &mut R) -> io::Result<Option<String>> {
    let mut bytes = Vec::new();
    loop {
        let chunk = reader.fill_buf()?;
        if chunk.is_empty() {
            if bytes.is_empty() {
                return Ok(None);
            }
            break;
        }
        let newline = chunk.iter().position(|byte| *byte == b'\n');
        let take = newline.map_or(chunk.len(), |index| index + 1);
        if bytes.len().saturating_add(take) > MAX_QUOTE_LINE_BYTES {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "quote input line exceeds four KiB",
            ));
        }
        bytes.extend_from_slice(&chunk[..take]);
        reader.consume(take);
        if newline.is_some() {
            break;
        }
    }
    String::from_utf8(bytes)
        .map(Some)
        .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error))
}

fn main() {
    let stdin = io::stdin();
    let mut input = stdin.lock();
    loop {
        let line = match read_bounded_line(&mut input) {
            Ok(Some(line)) => line,
            Ok(None) => break,
            Err(_) => {
                println!("{}", json!({"status": "input_error", "code": "INPUT_LINE"}));
                break;
            }
        };
        if line.trim().is_empty() {
            continue;
        }
        println!("{}", handle(line.trim()));
    }
}
