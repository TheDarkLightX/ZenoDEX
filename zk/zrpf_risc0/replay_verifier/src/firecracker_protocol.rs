//! Fixed binary request and committed-output ABI for the Firecracker replay guest.

use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};

use sha2::{Digest as _, Sha256};

use crate::VerifiedReplayReport;

pub const REQUEST_BYTES_V1: usize = 192;
pub const OUTPUT_BYTES_V1: usize = 16_777_216;
pub const OUTPUT_HEADER_BYTES_V1: usize = 256;
pub const OUTPUT_COMMIT_BYTES_V1: usize = 32;
pub const OUTPUT_PAYLOAD_CAP_BYTES_V1: usize = 65_536;

const REQUEST_MAGIC_V1: &[u8; 8] = b"ZRPFREQ1";
const OUTPUT_MAGIC_V1: &[u8; 8] = b"ZRPFOU01";
const OUTPUT_COMMIT_DOMAIN_V1: &[u8] = b"zenodex/zrpf_firecracker_output_commit/v1\0";
const VERSION_V1: u16 = 1;
const ACCEPTED_STATUS_V1: u32 = 1;
const COMMIT_OFFSET_V1: u64 = (OUTPUT_BYTES_V1 - OUTPUT_COMMIT_BYTES_V1) as u64;

pub const CANDIDATE_PROFILE_CANONICAL_SHA256_V1: [u8; 32] = [
    0x3b, 0xe2, 0x2c, 0x7d, 0x06, 0xbc, 0x3c, 0x4a, 0x7f, 0x0d, 0x83, 0x06, 0x5f, 0xe2, 0xca, 0xdb,
    0xb7, 0xb2, 0x84, 0x83, 0x0a, 0x70, 0x79, 0x71, 0x65, 0xe3, 0x2e, 0x22, 0x9a, 0x1b, 0xdd, 0x0f,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FirecrackerProtocolError {
    RequestLength,
    RequestMagic,
    RequestVersion,
    RequestFlags,
    RequestNonce,
    RequestProfile,
    RequestManifest,
    RequestInput,
    RequestIntent,
    RequestOutputBounds,
    RequestReserved,
    OutputLength,
    OutputIo,
    OutputHeader,
    OutputBinding,
    OutputPayload,
    OutputTrailingBytes,
    OutputCommit,
}

impl FirecrackerProtocolError {
    pub const fn code(self) -> &'static str {
        match self {
            Self::RequestLength => "request_length",
            Self::RequestMagic => "request_magic",
            Self::RequestVersion => "request_version",
            Self::RequestFlags => "request_flags",
            Self::RequestNonce => "request_nonce",
            Self::RequestProfile => "request_profile",
            Self::RequestManifest => "request_manifest",
            Self::RequestInput => "request_input",
            Self::RequestIntent => "request_intent",
            Self::RequestOutputBounds => "request_output_bounds",
            Self::RequestReserved => "request_reserved",
            Self::OutputLength => "output_length",
            Self::OutputIo => "output_io",
            Self::OutputHeader => "output_header",
            Self::OutputBinding => "output_binding",
            Self::OutputPayload => "output_payload",
            Self::OutputTrailingBytes => "output_trailing_bytes",
            Self::OutputCommit => "output_commit",
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FirecrackerRequestV1 {
    run_nonce_256: [u8; 32],
    runtime_manifest_sha256: [u8; 32],
    input_drive_sha256: [u8; 32],
    replay_intent_sha256: [u8; 32],
}

impl FirecrackerRequestV1 {
    pub fn new(
        run_nonce_256: [u8; 32],
        runtime_manifest_sha256: [u8; 32],
        input_drive_sha256: [u8; 32],
        replay_intent_sha256: [u8; 32],
    ) -> Result<Self, FirecrackerProtocolError> {
        require_nonzero(&run_nonce_256, FirecrackerProtocolError::RequestNonce)?;
        require_nonzero(
            &runtime_manifest_sha256,
            FirecrackerProtocolError::RequestManifest,
        )?;
        require_nonzero(&input_drive_sha256, FirecrackerProtocolError::RequestInput)?;
        require_nonzero(
            &replay_intent_sha256,
            FirecrackerProtocolError::RequestIntent,
        )?;
        Ok(Self {
            run_nonce_256,
            runtime_manifest_sha256,
            input_drive_sha256,
            replay_intent_sha256,
        })
    }

    pub const fn run_nonce_256(&self) -> &[u8; 32] {
        &self.run_nonce_256
    }

    pub const fn runtime_manifest_sha256(&self) -> &[u8; 32] {
        &self.runtime_manifest_sha256
    }

    pub const fn input_drive_sha256(&self) -> &[u8; 32] {
        &self.input_drive_sha256
    }

    pub const fn replay_intent_sha256(&self) -> &[u8; 32] {
        &self.replay_intent_sha256
    }

    pub fn encode(&self) -> [u8; REQUEST_BYTES_V1] {
        let mut output = [0_u8; REQUEST_BYTES_V1];
        output[0..8].copy_from_slice(REQUEST_MAGIC_V1);
        output[8..10].copy_from_slice(&VERSION_V1.to_le_bytes());
        output[10..12].copy_from_slice(&(REQUEST_BYTES_V1 as u16).to_le_bytes());
        output[16..48].copy_from_slice(&self.run_nonce_256);
        output[48..80].copy_from_slice(&CANDIDATE_PROFILE_CANONICAL_SHA256_V1);
        output[80..112].copy_from_slice(&self.runtime_manifest_sha256);
        output[112..144].copy_from_slice(&self.input_drive_sha256);
        output[144..152].copy_from_slice(&(OUTPUT_BYTES_V1 as u64).to_le_bytes());
        output[152..156].copy_from_slice(&(OUTPUT_PAYLOAD_CAP_BYTES_V1 as u32).to_le_bytes());
        output[156..188].copy_from_slice(&self.replay_intent_sha256);
        output
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, FirecrackerProtocolError> {
        validate_request_header(bytes)?;
        let nonce = array_32(bytes, 16)?;
        let profile = array_32(bytes, 48)?;
        let manifest = array_32(bytes, 80)?;
        let input = array_32(bytes, 112)?;
        let intent = array_32(bytes, 156)?;
        if profile != CANDIDATE_PROFILE_CANONICAL_SHA256_V1 {
            return Err(FirecrackerProtocolError::RequestProfile);
        }
        if bytes[188..REQUEST_BYTES_V1].iter().any(|byte| *byte != 0) {
            return Err(FirecrackerProtocolError::RequestReserved);
        }
        Self::new(nonce, manifest, input, intent)
    }

    pub fn sha256(&self) -> [u8; 32] {
        sha256(&self.encode())
    }
}

pub fn read_request_from_output(
    output: &mut File,
) -> Result<FirecrackerRequestV1, FirecrackerProtocolError> {
    require_output_file_size(output)?;
    output
        .seek(SeekFrom::Start(0))
        .map_err(|_| FirecrackerProtocolError::OutputIo)?;
    let mut bytes = [0_u8; REQUEST_BYTES_V1];
    output
        .read_exact(&mut bytes)
        .map_err(|_| FirecrackerProtocolError::OutputIo)?;
    FirecrackerRequestV1::decode(&bytes)
}

pub fn commit_accepted_output(
    output: &mut File,
    request: &FirecrackerRequestV1,
    observed_input_drive_sha256: [u8; 32],
    report: &VerifiedReplayReport,
) -> Result<(), FirecrackerProtocolError> {
    if &observed_input_drive_sha256 != request.input_drive_sha256() {
        return Err(FirecrackerProtocolError::OutputBinding);
    }
    let payload = report.canonical_cli_bytes();
    let (header, marker) = encode_output_parts(request, observed_input_drive_sha256, &payload)?;
    require_output_file_size(output)?;
    zero_output(output)?;
    output
        .seek(SeekFrom::Start(0))
        .and_then(|_| output.write_all(&header))
        .and_then(|_| output.write_all(&payload))
        .and_then(|_| output.sync_data())
        .map_err(|_| FirecrackerProtocolError::OutputIo)?;
    output
        .seek(SeekFrom::Start(COMMIT_OFFSET_V1))
        .and_then(|_| output.write_all(&marker))
        .and_then(|_| output.sync_data())
        .map_err(|_| FirecrackerProtocolError::OutputIo)
}

pub fn validate_committed_output<'a>(
    bytes: &'a [u8],
    request: &FirecrackerRequestV1,
) -> Result<&'a [u8], FirecrackerProtocolError> {
    if bytes.len() != OUTPUT_BYTES_V1 {
        return Err(FirecrackerProtocolError::OutputLength);
    }
    let payload_length = validate_output_header(bytes, request)?;
    let payload_end = OUTPUT_HEADER_BYTES_V1
        .checked_add(payload_length)
        .ok_or(FirecrackerProtocolError::OutputPayload)?;
    let commit_offset = OUTPUT_BYTES_V1 - OUTPUT_COMMIT_BYTES_V1;
    if payload_end > commit_offset {
        return Err(FirecrackerProtocolError::OutputPayload);
    }
    let payload = &bytes[OUTPUT_HEADER_BYTES_V1..payload_end];
    if sha256(payload) != array_32(bytes, 192)? {
        return Err(FirecrackerProtocolError::OutputPayload);
    }
    if bytes[payload_end..commit_offset]
        .iter()
        .any(|byte| *byte != 0)
    {
        return Err(FirecrackerProtocolError::OutputTrailingBytes);
    }
    let marker = output_commit_marker(&bytes[..OUTPUT_HEADER_BYTES_V1], payload);
    if bytes[commit_offset..] != marker {
        return Err(FirecrackerProtocolError::OutputCommit);
    }
    Ok(payload)
}

fn validate_request_header(bytes: &[u8]) -> Result<(), FirecrackerProtocolError> {
    if bytes.len() != REQUEST_BYTES_V1 {
        return Err(FirecrackerProtocolError::RequestLength);
    }
    if &bytes[0..8] != REQUEST_MAGIC_V1 {
        return Err(FirecrackerProtocolError::RequestMagic);
    }
    if read_u16(bytes, 8)? != VERSION_V1 || read_u16(bytes, 10)? != REQUEST_BYTES_V1 as u16 {
        return Err(FirecrackerProtocolError::RequestVersion);
    }
    if read_u32(bytes, 12)? != 0 {
        return Err(FirecrackerProtocolError::RequestFlags);
    }
    if read_u64(bytes, 144)? != OUTPUT_BYTES_V1 as u64
        || read_u32(bytes, 152)? != OUTPUT_PAYLOAD_CAP_BYTES_V1 as u32
    {
        return Err(FirecrackerProtocolError::RequestOutputBounds);
    }
    Ok(())
}

fn encode_output_parts(
    request: &FirecrackerRequestV1,
    input_sha256: [u8; 32],
    payload: &[u8],
) -> Result<([u8; OUTPUT_HEADER_BYTES_V1], [u8; 32]), FirecrackerProtocolError> {
    if payload.is_empty() || payload.len() > OUTPUT_PAYLOAD_CAP_BYTES_V1 {
        return Err(FirecrackerProtocolError::OutputPayload);
    }
    let mut header = [0_u8; OUTPUT_HEADER_BYTES_V1];
    header[0..8].copy_from_slice(OUTPUT_MAGIC_V1);
    header[8..10].copy_from_slice(&VERSION_V1.to_le_bytes());
    header[10..12].copy_from_slice(&(OUTPUT_HEADER_BYTES_V1 as u16).to_le_bytes());
    header[12..16].copy_from_slice(&ACCEPTED_STATUS_V1.to_le_bytes());
    header[16..20].copy_from_slice(&(payload.len() as u32).to_le_bytes());
    header[24..32].copy_from_slice(&(OUTPUT_BYTES_V1 as u64).to_le_bytes());
    header[32..64].copy_from_slice(request.run_nonce_256());
    header[64..96].copy_from_slice(&request.sha256());
    header[96..128].copy_from_slice(&input_sha256);
    header[128..160].copy_from_slice(&CANDIDATE_PROFILE_CANONICAL_SHA256_V1);
    header[160..192].copy_from_slice(request.runtime_manifest_sha256());
    header[192..224].copy_from_slice(&sha256(payload));
    let marker = output_commit_marker(&header, payload);
    Ok((header, marker))
}

fn validate_output_header(
    bytes: &[u8],
    request: &FirecrackerRequestV1,
) -> Result<usize, FirecrackerProtocolError> {
    if &bytes[0..8] != OUTPUT_MAGIC_V1
        || read_u16(bytes, 8)? != VERSION_V1
        || read_u16(bytes, 10)? != OUTPUT_HEADER_BYTES_V1 as u16
        || read_u32(bytes, 12)? != ACCEPTED_STATUS_V1
        || read_u64(bytes, 24)? != OUTPUT_BYTES_V1 as u64
        || bytes[20..24].iter().any(|byte| *byte != 0)
        || bytes[224..OUTPUT_HEADER_BYTES_V1]
            .iter()
            .any(|byte| *byte != 0)
    {
        return Err(FirecrackerProtocolError::OutputHeader);
    }
    if array_32(bytes, 32)? != *request.run_nonce_256()
        || array_32(bytes, 64)? != request.sha256()
        || array_32(bytes, 96)? != *request.input_drive_sha256()
        || array_32(bytes, 128)? != CANDIDATE_PROFILE_CANONICAL_SHA256_V1
        || array_32(bytes, 160)? != *request.runtime_manifest_sha256()
    {
        return Err(FirecrackerProtocolError::OutputBinding);
    }
    let payload_length = usize::try_from(read_u32(bytes, 16)?)
        .map_err(|_| FirecrackerProtocolError::OutputPayload)?;
    if payload_length == 0 || payload_length > OUTPUT_PAYLOAD_CAP_BYTES_V1 {
        return Err(FirecrackerProtocolError::OutputPayload);
    }
    Ok(payload_length)
}

fn output_commit_marker(header: &[u8], payload: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(OUTPUT_COMMIT_DOMAIN_V1);
    hasher.update(header);
    hasher.update(payload);
    hasher.finalize().into()
}

fn zero_output(output: &mut File) -> Result<(), FirecrackerProtocolError> {
    output
        .seek(SeekFrom::Start(0))
        .map_err(|_| FirecrackerProtocolError::OutputIo)?;
    let block = [0_u8; 65_536];
    for _ in 0..(OUTPUT_BYTES_V1 / block.len()) {
        output
            .write_all(&block)
            .map_err(|_| FirecrackerProtocolError::OutputIo)?;
    }
    Ok(())
}

fn require_output_file_size(output: &mut File) -> Result<(), FirecrackerProtocolError> {
    let size = output
        .seek(SeekFrom::End(0))
        .map_err(|_| FirecrackerProtocolError::OutputIo)?;
    if size != OUTPUT_BYTES_V1 as u64 {
        return Err(FirecrackerProtocolError::OutputLength);
    }
    Ok(())
}

fn require_nonzero(
    value: &[u8; 32],
    error: FirecrackerProtocolError,
) -> Result<(), FirecrackerProtocolError> {
    if value.iter().all(|byte| *byte == 0) {
        return Err(error);
    }
    Ok(())
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn array_32(bytes: &[u8], offset: usize) -> Result<[u8; 32], FirecrackerProtocolError> {
    bytes
        .get(offset..offset + 32)
        .and_then(|value| value.try_into().ok())
        .ok_or(FirecrackerProtocolError::OutputHeader)
}

fn read_u16(bytes: &[u8], offset: usize) -> Result<u16, FirecrackerProtocolError> {
    bytes
        .get(offset..offset + 2)
        .and_then(|value| value.try_into().ok())
        .map(u16::from_le_bytes)
        .ok_or(FirecrackerProtocolError::OutputHeader)
}

fn read_u32(bytes: &[u8], offset: usize) -> Result<u32, FirecrackerProtocolError> {
    bytes
        .get(offset..offset + 4)
        .and_then(|value| value.try_into().ok())
        .map(u32::from_le_bytes)
        .ok_or(FirecrackerProtocolError::OutputHeader)
}

fn read_u64(bytes: &[u8], offset: usize) -> Result<u64, FirecrackerProtocolError> {
    bytes
        .get(offset..offset + 8)
        .and_then(|value| value.try_into().ok())
        .map(u64::from_le_bytes)
        .ok_or(FirecrackerProtocolError::OutputHeader)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs::OpenOptions;
    use std::sync::atomic::{AtomicUsize, Ordering};

    static NEXT_FILE: AtomicUsize = AtomicUsize::new(0);

    fn request() -> FirecrackerRequestV1 {
        match FirecrackerRequestV1::new([1; 32], [2; 32], [3; 32], [4; 32]) {
            Ok(value) => value,
            Err(error) => panic!("valid fixture rejected: {}", error.code()),
        }
    }

    #[test]
    fn request_round_trip_and_reserved_bytes_reject() {
        let encoded = request().encode();
        assert_eq!(FirecrackerRequestV1::decode(&encoded), Ok(request()));
        assert_eq!(
            hex::encode(sha256(&encoded)),
            "2235d4e91730fbb30044a676f671120a2abe68cec0c9d0f10984f7c31455f1d2"
        );

        let mut changed = encoded;
        changed[191] = 1;
        assert_eq!(
            FirecrackerRequestV1::decode(&changed),
            Err(FirecrackerProtocolError::RequestReserved)
        );
    }

    #[test]
    fn compiled_profile_hash_matches_governed_json() {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../../config/proof_profiles/zrpf_v3_firecracker_replay_profile_v1.json");
        let raw = match std::fs::read(path) {
            Ok(value) => value,
            Err(error) => panic!("read governed profile failed: {error}"),
        };
        let value: serde_json::Value = match serde_json::from_slice(&raw) {
            Ok(value) => value,
            Err(error) => panic!("decode governed profile failed: {error}"),
        };
        let canonical = match serde_json::to_vec(&value) {
            Ok(value) => value,
            Err(error) => panic!("canonicalize governed profile failed: {error}"),
        };
        assert_eq!(sha256(&canonical), CANDIDATE_PROFILE_CANONICAL_SHA256_V1);
    }

    #[test]
    fn request_rejects_zero_authority_bindings() {
        assert_eq!(
            FirecrackerRequestV1::new([0; 32], [2; 32], [3; 32], [4; 32]),
            Err(FirecrackerProtocolError::RequestNonce)
        );
        assert_eq!(
            FirecrackerRequestV1::new([1; 32], [0; 32], [3; 32], [4; 32]),
            Err(FirecrackerProtocolError::RequestManifest)
        );
        assert_eq!(
            FirecrackerRequestV1::new([1; 32], [2; 32], [0; 32], [4; 32]),
            Err(FirecrackerProtocolError::RequestInput)
        );
        assert_eq!(
            FirecrackerRequestV1::new([1; 32], [2; 32], [3; 32], [0; 32]),
            Err(FirecrackerProtocolError::RequestIntent)
        );
    }

    #[test]
    fn committed_output_round_trip_and_mutations_reject() {
        let path = test_output_path();
        let mut file = create_output_file(&path);
        let report = VerifiedReplayReport::from_verified_json(r#"{"ok":true}"#.to_owned());
        let payload = report.canonical_cli_bytes();
        assert_eq!(
            commit_accepted_output(&mut file, &request(), [3; 32], &report),
            Ok(())
        );
        let bytes = read_output(&mut file);
        assert_eq!(
            hex::encode(sha256(&bytes)),
            "6065d36f3846fcd149068355f8c787ff9b73e0d87759291194f21ae2980c6e71"
        );
        assert_eq!(
            validate_committed_output(&bytes, &request()),
            Ok(payload.as_slice())
        );

        let mut changed = bytes.clone();
        changed[OUTPUT_HEADER_BYTES_V1 + payload.len() + 1] = 1;
        assert_eq!(
            validate_committed_output(&changed, &request()),
            Err(FirecrackerProtocolError::OutputTrailingBytes)
        );
        let last = changed.len() - 1;
        changed[OUTPUT_HEADER_BYTES_V1 + payload.len() + 1] = 0;
        changed[last] ^= 1;
        assert_eq!(
            validate_committed_output(&changed, &request()),
            Err(FirecrackerProtocolError::OutputCommit)
        );
        drop(file);
        let _ = std::fs::remove_file(path);
    }

    #[test]
    fn committed_output_rejects_declared_payload_above_cap() {
        let path = test_output_path();
        let mut file = create_output_file(&path);
        let report = VerifiedReplayReport::from_verified_json(r#"{"ok":true}"#.to_owned());
        assert_eq!(
            commit_accepted_output(&mut file, &request(), [3; 32], &report),
            Ok(())
        );
        let mut bytes = read_output(&mut file);
        bytes[16..20].copy_from_slice(&((OUTPUT_PAYLOAD_CAP_BYTES_V1 as u32) + 1).to_le_bytes());
        assert_eq!(
            validate_committed_output(&bytes, &request()),
            Err(FirecrackerProtocolError::OutputPayload)
        );
        drop(file);
        let _ = std::fs::remove_file(path);
    }

    fn test_output_path() -> std::path::PathBuf {
        let sequence = NEXT_FILE.fetch_add(1, Ordering::Relaxed);
        std::env::temp_dir().join(format!(
            "zrpf-firecracker-output-test-{}-{sequence}.raw",
            std::process::id()
        ))
    }

    fn create_output_file(path: &std::path::Path) -> File {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(path);
        let file = match file {
            Ok(value) => value,
            Err(error) => panic!("create output fixture failed: {error}"),
        };
        if let Err(error) = file.set_len(OUTPUT_BYTES_V1 as u64) {
            panic!("size output fixture failed: {error}");
        }
        file
    }

    fn read_output(file: &mut File) -> Vec<u8> {
        if let Err(error) = file.seek(SeekFrom::Start(0)) {
            panic!("seek output fixture failed: {error}");
        }
        let mut bytes = Vec::new();
        if let Err(error) = file.read_to_end(&mut bytes) {
            panic!("read output fixture failed: {error}");
        }
        bytes
    }
}
