use std::fs::{File, OpenOptions};
use std::hint::black_box;
use std::io::{Read, Seek, SeekFrom};
use std::sync::atomic::{AtomicUsize, Ordering};

use sha2::{Digest as _, Sha256};
use zenodex_zrpf_spot_v7_firecracker_runtime::{
    commit_data_only_output_v1, decode_structural_spot_v7_payload_v1, validate_committed_output_v1,
    SpotV7FirecrackerProtocolErrorV1, SpotV7FirecrackerRequestV1,
    SPOT_V7_FIRECRACKER_EXECUTION_AUTHORITY_V1, SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1,
    SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1, SPOT_V7_FIRECRACKER_PRODUCTION_READY_V1,
    SPOT_V7_FIRECRACKER_RELEASE_AUTHORITY_V1, SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1,
    SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1, SPOT_V7_FIRECRACKER_SETTLEMENT_AUTHORITY_V1,
};

const GOLDEN_PAYLOAD_HEX: &str =
    include_str!("../../verifier/tests/vectors/spot_settlement_v7_firecracker_output_v1.hex");
const LIB_SOURCE: &str = include_str!("../src/lib.rs");
static NEXT_FILE: AtomicUsize = AtomicUsize::new(0);

#[test]
fn profile_and_request_match_python_vectors() {
    assert!(!black_box(SPOT_V7_FIRECRACKER_EXECUTION_AUTHORITY_V1));
    assert!(!black_box(SPOT_V7_FIRECRACKER_SETTLEMENT_AUTHORITY_V1));
    assert!(!black_box(SPOT_V7_FIRECRACKER_RELEASE_AUTHORITY_V1));
    assert!(!black_box(SPOT_V7_FIRECRACKER_PRODUCTION_READY_V1));
    assert_eq!(
        sha256(SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1),
        SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1
    );
    assert_eq!(
        hex::encode(SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1),
        "1b60e4bc78bc3ea3938f2ca72848418097208096574a1fc37e3404b841f36cd4"
    );
    let request = request();
    let encoded = request.encode();
    assert_eq!(SpotV7FirecrackerRequestV1::decode(&encoded), Ok(request));
    assert_eq!(
        hex::encode(sha256(&encoded)),
        "613519701cef6cde07f58ed97c10cedd60ec9a3c790efdab5824afb02ef27a36"
    );
    assert!(!LIB_SOURCE.contains("VerifiedReplayReport"));
    assert!(
        !LIB_SOURCE.contains("e7ab29b1327cd89dd7180cd45aed9663fdb9234d738f7acb51412bb576c8c88e")
    );
}

#[test]
fn golden_payload_and_committed_output_match_python_vectors() {
    let payload = golden_payload();
    let decoded =
        decode_structural_spot_v7_payload_v1(&payload).expect("golden payload must decode");
    assert_eq!(decoded.raw_bytes(), payload);
    assert_eq!(
        hex::encode(decoded.sha256()),
        "979b2e9cb4757de50ec935c55ca827c693ad5cb4e22ee8034bee9e7866de148c"
    );

    let path = test_output_path();
    let mut file = create_output_file(&path);
    let request = request();
    commit_data_only_output_v1(&mut file, &request, [3; 32], &decoded)
        .expect("golden payload must commit");
    let output = read_output(&mut file);
    let replayed =
        validate_committed_output_v1(&output, &request).expect("committed output must validate");
    assert_eq!(replayed, decoded);
    assert_eq!(
        hex::encode(sha256(&output)),
        "5109be6580c464569034d6c1652f9b01d00d2229440445b2c3e48b7b10676dfa"
    );
    drop(file);
    std::fs::remove_file(path).expect("remove output fixture");
}

#[test]
fn request_and_output_mutations_reject_at_stable_boundaries() {
    let mut request_bytes = request().encode();
    request_bytes[0] ^= 1;
    assert_eq!(
        SpotV7FirecrackerRequestV1::decode(&request_bytes),
        Err(SpotV7FirecrackerProtocolErrorV1::RequestMagic)
    );

    let path = test_output_path();
    let mut file = create_output_file(&path);
    let request = request();
    let payload = decode_structural_spot_v7_payload_v1(&golden_payload()).expect("valid fixture");
    commit_data_only_output_v1(&mut file, &request, [3; 32], &payload).expect("commit fixture");
    let mut output = read_output(&mut file);
    output[SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1 + payload.raw_bytes().len() + 1] = 1;
    assert_eq!(
        validate_committed_output_v1(&output, &request),
        Err(SpotV7FirecrackerProtocolErrorV1::OutputTrailingBytes)
    );
    output[SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1 + payload.raw_bytes().len() + 1] = 0;
    let last = output.len() - 1;
    output[last] ^= 1;
    assert_eq!(
        validate_committed_output_v1(&output, &request),
        Err(SpotV7FirecrackerProtocolErrorV1::OutputCommit)
    );
    drop(file);
    std::fs::remove_file(path).expect("remove output fixture");
}

#[test]
fn v7_payload_nested_mutations_reject() {
    let mut payload = golden_payload();
    payload[0] ^= 1;
    assert_eq!(
        decode_structural_spot_v7_payload_v1(&payload),
        Err(SpotV7FirecrackerProtocolErrorV1::V7OutputMagic)
    );

    let mut payload = golden_payload();
    let last = payload.len() - 1;
    payload[last] ^= 1;
    assert_eq!(
        decode_structural_spot_v7_payload_v1(&payload),
        Err(SpotV7FirecrackerProtocolErrorV1::V7PlanBytesSha256)
    );
}

#[test]
fn rejected_input_binding_leaves_commit_marker_absent() {
    let path = test_output_path();
    let mut file = create_output_file(&path);
    let request = request();
    let payload = decode_structural_spot_v7_payload_v1(&golden_payload()).expect("valid fixture");

    assert_eq!(
        commit_data_only_output_v1(&mut file, &request, [9; 32], &payload),
        Err(SpotV7FirecrackerProtocolErrorV1::OutputBinding)
    );
    let output = read_output(&mut file);
    assert!(output.iter().all(|byte| *byte == 0));
    drop(file);
    std::fs::remove_file(path).expect("remove output fixture");
}

fn request() -> SpotV7FirecrackerRequestV1 {
    SpotV7FirecrackerRequestV1::new([1; 32], [2; 32], [3; 32], [4; 32])
        .expect("valid request fixture")
}

fn golden_payload() -> Vec<u8> {
    let compact = GOLDEN_PAYLOAD_HEX
        .lines()
        .map(|line| line.split("//").next().unwrap_or("").trim())
        .collect::<String>();
    hex::decode(compact).expect("valid golden payload hex")
}

fn test_output_path() -> std::path::PathBuf {
    let sequence = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
    std::env::temp_dir().join(format!(
        "zrpf-spot-v7-firecracker-output-test-{}-{sequence}.raw",
        std::process::id()
    ))
}

fn create_output_file(path: &std::path::Path) -> File {
    let file = OpenOptions::new()
        .read(true)
        .write(true)
        .create_new(true)
        .open(path)
        .expect("create output fixture");
    file.set_len(SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1 as u64)
        .expect("size output fixture");
    file
}

fn read_output(file: &mut File) -> Vec<u8> {
    file.seek(SeekFrom::Start(0)).expect("seek output");
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes).expect("read output");
    bytes
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
