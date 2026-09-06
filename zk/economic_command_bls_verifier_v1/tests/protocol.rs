use std::io::Write;
use std::process::{Command, Output, Stdio};

use sha2::{Digest, Sha256};

const REQUEST_MAGIC_V1: &[u8; 8] = b"ZDXBLSV1";
const ACCEPT_MAGIC_V1: &[u8; 8] = b"ZDXBOKV1";
const REJECT_MAGIC_V1: &[u8; 8] = b"ZDXBNOV1";
const PUBLIC_KEY_BYTES_V1: usize = 48;
const SIGNATURE_BYTES_V1: usize = 96;
const MAX_MESSAGE_BYTES_V1: usize = 1_048_576;
const MAX_REQUEST_BYTES_V1: usize = 8 + 48 + 96 + 4 + MAX_MESSAGE_BYTES_V1;

const PY_ECC_PUBLIC_KEY_HEX: &str =
    "acb58c81ae0cae2e9d4d446b730922239923c345744eee58efaadb36e9a0925545b18a987acf0bad469035b291e37269";
const PY_ECC_MESSAGE_HEX: &str =
    "7a656e6f6465782f69736f6c617465642d626c732d65766964656e63652f76313a7075626c69632d636f6e74726f6c";
const PY_ECC_SIGNATURE_HEX: &str = concat!(
    "82491e8deb3876a5fe0982d1ff34956f75e458d5d5ee2e8e6cdefc177d737450",
    "e44fbaa17356285cec8253d29ca1e1c80b13813b5f7a2f386e801c24e0fc7047",
    "f8456a7a2c3029f7ef376541175b183a61f9611bc430e3d96333f95cb0ac6764",
);
const PY_ECC_PREHASH_SIGNATURE_HEX: &str = concat!(
    "b8f38046aff28f34dae4968442090057fae068d771365fcbb910d26fd58e16480",
    "ca2a77007fc6504618e7f0ef808e2c8109ef6f1eec0adf7add4bb35880597785",
    "74bc1c272a42a01ca168fb30c8cd9e57d12aefca3459872e600f48fb480f62d",
);
const PY_ECC_FOREIGN_PUBLIC_KEY_HEX: &str =
    "81ccc19e3b938ec2405099e90022a4218baa5082a3ca0974b24be0bc8b07e5fffaed64bef0d02c4dbfb6a307829afc5c";
const PYTHON_FIXED_REQUEST_DIGEST_HEX: &str =
    "728c18de0e7a5ef87efc195f8db8a64b159443e73c3e8ba0070c5414d5cdf2e1";

fn endpoint() -> &'static str {
    env!("CARGO_BIN_EXE_zenodex-economic-command-bls-verifier-v1")
}

fn decode_hex(value: &str) -> Vec<u8> {
    assert_eq!(value.len() % 2, 0);
    value
        .as_bytes()
        .chunks_exact(2)
        .map(|pair| {
            let text = std::str::from_utf8(pair).expect("fixture hex is ASCII");
            u8::from_str_radix(text, 16).expect("fixture hex is valid")
        })
        .collect()
}

fn py_ecc_public_key() -> Vec<u8> {
    decode_hex(PY_ECC_PUBLIC_KEY_HEX)
}

fn py_ecc_message() -> Vec<u8> {
    decode_hex(PY_ECC_MESSAGE_HEX)
}

fn py_ecc_signature() -> Vec<u8> {
    decode_hex(PY_ECC_SIGNATURE_HEX)
}

fn request(public_key: &[u8], signature: &[u8], message: &[u8]) -> Vec<u8> {
    assert_eq!(public_key.len(), PUBLIC_KEY_BYTES_V1);
    assert_eq!(signature.len(), SIGNATURE_BYTES_V1);
    let message_len = u32::try_from(message.len()).expect("test message length fits u32");
    let mut request = Vec::with_capacity(8 + 48 + 96 + 4 + message.len());
    request.extend_from_slice(REQUEST_MAGIC_V1);
    request.extend_from_slice(public_key);
    request.extend_from_slice(signature);
    request.extend_from_slice(&message_len.to_le_bytes());
    request.extend_from_slice(message);
    request
}

fn run_with_args(input: &[u8], args: &[&str]) -> Output {
    let mut child = Command::new(endpoint())
        .args(args)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("endpoint starts");
    child
        .stdin
        .take()
        .expect("child stdin exists")
        .write_all(input)
        .expect("request writes");
    child.wait_with_output().expect("endpoint exits")
}

fn run(input: &[u8]) -> Output {
    run_with_args(input, &[])
}

fn expected_response(magic: &[u8; 8], input: &[u8]) -> Vec<u8> {
    let mut response = Vec::with_capacity(40);
    response.extend_from_slice(magic);
    response.extend_from_slice(&Sha256::digest(input));
    response
}

fn assert_malformed(input: &[u8]) {
    let output = run(input);
    assert!(!output.status.success());
    assert_eq!(output.stdout, b"");
    assert_eq!(output.stderr, b"");
}

#[test]
fn given_existing_py_ecc_g2basic_fixture_when_verified_then_accept_exactly() {
    let input = request(&py_ecc_public_key(), &py_ecc_signature(), &py_ecc_message());
    let output = run(&input);

    assert!(output.status.success());
    assert_eq!(
        Sha256::digest(&input).as_slice(),
        decode_hex(PYTHON_FIXED_REQUEST_DIGEST_HEX)
    );
    assert_eq!(output.stdout, expected_response(ACCEPT_MAGIC_V1, &input));
    assert_eq!(output.stdout.len(), 40);
    assert_eq!(output.stderr, b"");
}

#[test]
fn given_well_framed_foreign_bls_inputs_when_verified_then_reject_with_request_digest() {
    let public_key = py_ecc_public_key();
    let signature = py_ecc_signature();
    let message = py_ecc_message();
    let mut wrong_message = message.clone();
    *wrong_message.last_mut().expect("message is nonempty") ^= 1;
    let mut infinity_public_key = [0u8; PUBLIC_KEY_BYTES_V1];
    infinity_public_key[0] = 0xc0;
    let mut infinity_signature = [0u8; SIGNATURE_BYTES_V1];
    infinity_signature[0] = 0xc0;
    let cases = [
        request(&public_key, &signature, &wrong_message),
        request(
            &decode_hex(PY_ECC_FOREIGN_PUBLIC_KEY_HEX),
            &signature,
            &message,
        ),
        request(
            &public_key,
            &decode_hex(PY_ECC_PREHASH_SIGNATURE_HEX),
            &message,
        ),
        request(
            &[0u8; PUBLIC_KEY_BYTES_V1],
            &[0u8; SIGNATURE_BYTES_V1],
            &message,
        ),
        request(&infinity_public_key, &signature, &message),
        request(&public_key, &infinity_signature, &message),
    ];

    for input in cases {
        let output = run(&input);
        assert!(output.status.success());
        assert_eq!(output.stdout, expected_response(REJECT_MAGIC_V1, &input));
        assert_eq!(output.stderr, b"");
    }
}

#[test]
fn given_adjacent_messages_when_rejected_then_response_digest_binds_exact_request() {
    let public_key = [0u8; PUBLIC_KEY_BYTES_V1];
    let signature = [0u8; SIGNATURE_BYTES_V1];
    let left = request(&public_key, &signature, b"left");
    let right = request(&public_key, &signature, b"lefT");

    let left_output = run(&left);
    let right_output = run(&right);
    assert_eq!(
        left_output.stdout,
        expected_response(REJECT_MAGIC_V1, &left)
    );
    assert_eq!(
        right_output.stdout,
        expected_response(REJECT_MAGIC_V1, &right)
    );
    assert_ne!(left_output.stdout, right_output.stdout);
}

#[test]
fn given_minimum_and_maximum_messages_when_framed_then_endpoint_returns_one_response() {
    let public_key = [0u8; PUBLIC_KEY_BYTES_V1];
    let signature = [0u8; SIGNATURE_BYTES_V1];
    for message in [vec![0x5a], vec![0x5a; MAX_MESSAGE_BYTES_V1]] {
        let input = request(&public_key, &signature, &message);
        let output = run(&input);
        assert!(output.status.success());
        assert_eq!(output.stdout, expected_response(REJECT_MAGIC_V1, &input));
        assert_eq!(output.stdout.len(), 40);
        assert_eq!(output.stderr, b"");
    }
}

#[test]
fn given_malformed_or_out_of_bounds_frames_when_read_then_fail_without_stdout() {
    let valid = request(&py_ecc_public_key(), &py_ecc_signature(), &py_ecc_message());
    let mut wrong_magic = valid.clone();
    wrong_magic[0] ^= 1;
    let mut zero_length = valid[..8 + 48 + 96 + 4].to_vec();
    zero_length[8 + 48 + 96..].copy_from_slice(&0u32.to_le_bytes());
    let mut declared_too_large = zero_length.clone();
    let declared_too_large_len = u32::try_from(MAX_MESSAGE_BYTES_V1)
        .expect("message ceiling fits u32")
        .checked_add(1)
        .expect("adjacent length fits u32");
    declared_too_large[8 + 48 + 96..].copy_from_slice(&declared_too_large_len.to_le_bytes());
    let mut trailing = valid.clone();
    trailing.push(0);
    let truncated = &valid[..valid.len() - 1];
    let oversized_actual = vec![0u8; MAX_REQUEST_BYTES_V1 + 1];

    for input in [
        b"".as_slice(),
        wrong_magic.as_slice(),
        zero_length.as_slice(),
        declared_too_large.as_slice(),
        trailing.as_slice(),
        truncated,
        oversized_actual.as_slice(),
    ] {
        assert_malformed(input);
    }

    let output = run_with_args(b"", &["unexpected-argument"]);
    assert!(!output.status.success());
    assert_eq!(output.stdout, b"");
    assert_eq!(output.stderr, b"");
}
