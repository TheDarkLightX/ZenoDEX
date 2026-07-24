//! Emit one canonical cross-language vector for the authority-neutral V7 protocol.

use sha2::{Digest as _, Sha256};
use zenodex_zrpf_spot_v7_firecracker_runtime::{
    build_data_only_output_image_v1, decode_structural_spot_v7_payload_v1,
    SpotV7FirecrackerRequestV1, SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1,
};

const GOLDEN_PAYLOAD_HEX: &str =
    include_str!("../../../verifier/tests/vectors/spot_settlement_v7_firecracker_output_v1.hex");

fn main() {
    if let Err(error) = run() {
        eprintln!("spot-v7-firecracker-protocol-vector-v1: {error}");
        std::process::exit(2);
    }
}

fn run() -> Result<(), String> {
    if std::env::args_os().len() != 1 {
        return Err("arguments are forbidden".to_string());
    }
    let request = SpotV7FirecrackerRequestV1::new([1; 32], [2; 32], [3; 32], [4; 32], [5; 32])
        .map_err(|error| error.to_string())?;
    let payload = decode_structural_spot_v7_payload_v1(&decode_golden_payload()?)
        .map_err(|error| error.to_string())?;
    let output = build_data_only_output_image_v1(&request, [4; 32], &payload)
        .map_err(|error| error.to_string())?;
    let output_sha256 = hex::encode(sha256(&output));
    let payload_sha256 = hex::encode(payload.sha256());
    let profile_sha256 = hex::encode(sha256(SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1));
    let request_sha256 = hex::encode(request.sha256());
    println!(
        "{{\"output_sha256\":\"{output_sha256}\",\"payload_sha256\":\"{payload_sha256}\",\"profile_sha256\":\"{profile_sha256}\",\"request_sha256\":\"{request_sha256}\"}}"
    );
    Ok(())
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

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
