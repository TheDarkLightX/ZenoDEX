//! Emit stable reject-code vectors for the authority-neutral V7 protocol.

use zenodex_zrpf_spot_v7_firecracker_runtime::{
    build_data_only_output_image_v1, decode_structural_spot_v7_payload_v1,
    validate_committed_output_v1, SpotV7FirecrackerProtocolErrorV1, SpotV7FirecrackerRequestV1,
};

const GOLDEN_PAYLOAD_HEX: &str =
    include_str!("../../../verifier/tests/vectors/spot_settlement_v7_firecracker_output_v1.hex");

fn main() {
    if let Err(error) = run() {
        eprintln!("spot-v7-firecracker-negative-vector-v1: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    if std::env::args_os().len() != 1 {
        return Err("arguments are forbidden".to_string());
    }
    let request = SpotV7FirecrackerRequestV1::new([1; 32], [2; 32], [3; 32], [4; 32], [5; 32])
        .map_err(|error| error.to_string())?;
    let payload_bytes = decode_golden_payload()?;
    let payload =
        decode_structural_spot_v7_payload_v1(&payload_bytes).map_err(|error| error.to_string())?;
    let output = build_data_only_output_image_v1(&request, [4; 32], &payload)
        .map_err(|error| error.to_string())?;

    let mut request_magic = request.encode();
    request_magic[0] ^= 1;
    let request_magic = reject_code(SpotV7FirecrackerRequestV1::decode(&request_magic))?;

    let mut output_commit = output;
    let last = output_commit
        .len()
        .checked_sub(1)
        .ok_or_else(|| "output unexpectedly empty".to_string())?;
    output_commit[last] ^= 1;
    let output_commit = reject_code(validate_committed_output_v1(&output_commit, &request))?;

    let mut payload_magic = payload_bytes.clone();
    payload_magic[0] ^= 1;
    let payload_magic = reject_code(decode_structural_spot_v7_payload_v1(&payload_magic))?;

    let mut plan_hash = payload_bytes;
    let last = plan_hash
        .len()
        .checked_sub(1)
        .ok_or_else(|| "payload unexpectedly empty".to_string())?;
    plan_hash[last] ^= 1;
    let plan_hash = reject_code(decode_structural_spot_v7_payload_v1(&plan_hash))?;

    println!(
        "{{\"output_commit\":\"{output_commit}\",\"request_magic\":\"{request_magic}\",\"v7_output_magic\":\"{payload_magic}\",\"v7_plan_bytes_sha256\":\"{plan_hash}\"}}"
    );
    Ok(())
}

fn reject_code<T>(
    result: Result<T, SpotV7FirecrackerProtocolErrorV1>,
) -> Result<&'static str, String> {
    match result {
        Ok(_) => Err("mutation unexpectedly accepted".to_string()),
        Err(error) => Ok(error.code()),
    }
}

fn decode_golden_payload() -> Result<Vec<u8>, String> {
    let compact = GOLDEN_PAYLOAD_HEX
        .lines()
        .map(|line| {
            line.split_once("//")
                .map_or(line, |(prefix, _)| prefix)
                .trim()
        })
        .collect::<String>();
    hex::decode(compact).map_err(|error| format!("golden payload hex rejected: {error}"))
}
