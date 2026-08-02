#![forbid(unsafe_code)]

use std::env;
use std::fs;

use zenodex_runtime_core::canonical::{domain_sep_bytes, sha256_hex};

const MAGIC: &[u8] = b"FCIS-M6-G02\x01";
const CODEC_DOMAIN: &str = "zenodex/fcis/m6/g02/proof-context-codec";
const FIELD_SPECS: [(&str, u8); 15] = [
    ("chain_id", b'T'),
    ("deployment_id", b'T'),
    ("state_root", b'R'),
    ("configuration_root", b'R'),
    ("protocol_version", b'T'),
    ("language_runtime_version", b'T'),
    ("verifier_implementation_id", b'T'),
    ("verification_key_digest", b'R'),
    ("statement_schema_id", b'T'),
    ("algorithm_profile_id", b'T'),
    ("history_genesis_authority_root", b'R'),
    ("authority_epoch", b'U'),
    ("not_before_epoch", b'U'),
    ("expires_at_epoch", b'O'),
    ("context_root", b'R'),
];

fn frame(output: &mut Vec<u8>, value: &[u8]) -> Result<(), String> {
    let length = u32::try_from(value.len()).map_err(|_| "frame exceeds u32".to_owned())?;
    output.extend_from_slice(&length.to_be_bytes());
    output.extend_from_slice(value);
    Ok(())
}

fn epoch_bytes(value: &str, field: &str) -> Result<Vec<u8>, String> {
    let parsed = value
        .parse::<u64>()
        .map_err(|_| format!("{field} is not a u64"))?;
    Ok(parsed.to_be_bytes().to_vec())
}

fn field_bytes(value: &str, tag: u8, field: &str) -> Result<Vec<u8>, String> {
    match tag {
        b'T' | b'R' => Ok(value.as_bytes().to_vec()),
        b'U' => epoch_bytes(value, field),
        b'O' if value == "none" => Ok(vec![0]),
        b'O' => {
            let epoch = epoch_bytes(value, field)?;
            let mut output = vec![1];
            output.extend_from_slice(&epoch);
            Ok(output)
        }
        _ => Err(format!("{field} has an unsupported tag")),
    }
}

fn build_payload(record: &str) -> Result<Vec<u8>, String> {
    let fields: Vec<&str> = record.trim_end_matches('\n').split('\t').collect();
    if fields.len() != FIELD_SPECS.len() {
        return Err(format!("expected {} fields", FIELD_SPECS.len()));
    }
    let mut output = Vec::new();
    output.extend_from_slice(MAGIC);
    output.extend_from_slice(&(FIELD_SPECS.len() as u16).to_be_bytes());
    for ((name, tag), value) in FIELD_SPECS.iter().zip(fields.iter()) {
        frame(&mut output, name.as_bytes())?;
        output.push(*tag);
        frame(&mut output, &field_bytes(value, *tag, name)?)?;
    }
    Ok(output)
}

fn hex_encode(bytes: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut output = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        output.push(HEX[usize::from(byte >> 4)] as char);
        output.push(HEX[usize::from(byte & 0x0f)] as char);
    }
    output
}

fn run(
    input_path: &str,
    expected_payload_path: &str,
    expected_root_path: &str,
) -> Result<(), String> {
    let input = fs::read_to_string(input_path).map_err(|error| format!("input: {error}"))?;
    let expected_payload = fs::read_to_string(expected_payload_path)
        .map_err(|error| format!("expected payload: {error}"))?
        .trim()
        .to_owned();
    let expected_root = fs::read_to_string(expected_root_path)
        .map_err(|error| format!("expected root: {error}"))?
        .trim()
        .to_owned();
    let payload = build_payload(&input)?;
    let payload_hex = hex_encode(&payload);
    if payload_hex != expected_payload {
        return Err("Rust payload differs from Python vector".to_owned());
    }
    let mut preimage = domain_sep_bytes(CODEC_DOMAIN, 1);
    preimage.extend_from_slice(&(payload.len() as u64).to_be_bytes());
    preimage.extend_from_slice(&payload);
    let root = sha256_hex(&preimage);
    if root != expected_root {
        return Err("Rust codec root differs from Python vector".to_owned());
    }
    println!("G02_RUST_PARITY_PASS {root}");
    Ok(())
}

fn main() {
    let arguments: Vec<String> = env::args().collect();
    if arguments.len() != 4 {
        eprintln!("usage: g02-parity INPUT.tsv PAYLOAD.hex ROOT.txt");
        std::process::exit(2);
    }
    if let Err(error) = run(&arguments[1], &arguments[2], &arguments[3]) {
        eprintln!("G02_RUST_PARITY_FAIL {error}");
        std::process::exit(1);
    }
}
