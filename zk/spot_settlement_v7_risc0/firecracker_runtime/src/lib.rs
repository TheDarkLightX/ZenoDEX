//! Authority-neutral Spot V7 Firecracker binary protocol.
//!
//! This crate deliberately excludes the retained V3 profile and its report
//! type. The nested V7 decoder checks structural framing and selected hash
//! associations; it does not decode Plan B semantics. A decoded payload and
//! committed output remain data until a future guest verifies the actual V7
//! and V6 receipts under a governed runtime.

use std::fmt;
use std::fs::File;
use std::io::{Read, Seek, SeekFrom, Write};

use sha2::{Digest as _, Sha256};

pub const SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1: usize = 192;
pub const SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1: usize = 16_777_216;
pub const SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1: usize = 256;
pub const SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_BYTES_V1: usize = 32;
pub const SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1: usize = 65_536;

const REQUEST_MAGIC_V1: &[u8; 8] = b"ZSV7REQ1";
const OUTPUT_MAGIC_V1: &[u8; 8] = b"ZSV7OUT1";
const OUTPUT_COMMIT_DOMAIN_V1: &[u8] = b"zenodex/zrpf_spot_v7_firecracker_output_commit/v1\0";
const PROTOCOL_VERSION_V1: u16 = 1;
const DATA_ONLY_COMMITTED_STATUS_V1: u32 = 1;
const REQUEST_BYTES_FIELD_V1: u16 = 192;
const OUTPUT_BYTES_FIELD_V1: u64 = 16_777_216;
const OUTPUT_HEADER_BYTES_FIELD_V1: u16 = 256;
const OUTPUT_PAYLOAD_CAP_FIELD_V1: u32 = 65_536;
const OUTPUT_COMMIT_BYTES_FIELD_V1: u64 = 32;
const COMMIT_OFFSET_V1: u64 = OUTPUT_BYTES_FIELD_V1 - OUTPUT_COMMIT_BYTES_FIELD_V1;

const V7_OUTPUT_MAGIC_V1: &[u8; 8] = b"ZSPTV7O1";
const V7_OUTPUT_VERSION_V1: u16 = 1;
const V7_OUTPUT_FIXED_FIELD_COUNT_V1: usize = 19;
const V7_OUTPUT_HEADER_BYTES_V1: usize = 8 + 2 + 4 * 4 + 32 * V7_OUTPUT_FIXED_FIELD_COUNT_V1;
const V7_JOURNAL_MAGIC_V1: &[u8; 8] = b"ZSPTV7J1";
const V7_JOURNAL_VERSION_V1: u16 = 1;
const V7_JOURNAL_FIXED_FIELD_COUNT_V1: usize = 13;
const V7_JOURNAL_HEADER_BYTES_V1: usize = 8 + 2 + 4 + 4 + 2 + 2 + 4;
const V7_SEMANTIC_JOURNAL_BYTES_V1: usize = 2 + 8 * 32 + 48 + 4;
const V7_EFFECT_BINDING_JOURNAL_BYTES_V1: usize = 2 + 12 * 32;
const V7_MAX_PLAN_B_BYTES_V1: usize = 48 * 1_024;
const V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.spot_settlement_v7_effect_binding_journal.v1";
const V7_EFFECT_BINDING_COMMITMENT_DOMAIN_BYTES_V1: u16 = 57;

pub const SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_DESCRIPTOR_V1: &[u8] = concat!(
    "zenodex.zrpf.spot_v7.firecracker.runtime_profile.v1\n",
    "request_magic=ZSV7REQ1\n",
    "request_bytes=192\n",
    "request_version=1\n",
    "request_endian=little\n",
    "request_layout=magic:u8x8,version:u16,bytes:u16,flags:u32,nonce:u8x32,profile:u8x32,runtime_manifest:u8x32,input_drive:u8x32,output_bytes:u64,payload_cap:u32,settlement_intent:u8x32,reserved:u8x4\n",
    "output_magic=ZSV7OUT1\n",
    "output_bytes=16777216\n",
    "output_header_bytes=256\n",
    "output_commit_bytes=32\n",
    "output_payload_cap_bytes=65536\n",
    "output_header_endian=little\n",
    "output_header_layout=magic:u8x8,version:u16,header_bytes:u16,status:u32,payload_bytes:u32,flags:u32,output_bytes:u64,nonce:u8x32,request_sha256:u8x32,profile:u8x32,runtime_manifest:u8x32,input_drive:u8x32,settlement_intent:u8x32,payload_sha256:u8x32\n",
    "output_status=1:data_only_committed\n",
    "output_zero_region=header_plus_payload_to_commit_offset\n",
    "payload_magic=ZSPTV7O1\n",
    "payload_version=1\n",
    "payload_codec=SpotSettlementV7VerifierOutputV1_structural_envelope_big_endian\n",
    "payload_journal_magic=ZSPTV7J1\n",
    "payload_journal_version=1\n",
    "commit_domain=zenodex/zrpf_spot_v7_firecracker_output_commit/v1\\0\n",
    "commit_formula=sha256(domain||profile_sha256||request_sha256||header||payload)\n",
    "authority=data_only\n",
)
.as_bytes();

pub const SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1: [u8; 32] = [
    0x1b, 0x60, 0xe4, 0xbc, 0x78, 0xbc, 0x3e, 0xa3, 0x93, 0x8f, 0x2c, 0xa7, 0x28, 0x48, 0x41, 0x80,
    0x97, 0x20, 0x80, 0x96, 0x57, 0x4a, 0x1f, 0xc3, 0x7e, 0x34, 0x04, 0xb8, 0x41, 0xf3, 0x6c, 0xd4,
];

pub const SPOT_V7_FIRECRACKER_EXECUTION_AUTHORITY_V1: bool = false;
pub const SPOT_V7_FIRECRACKER_SETTLEMENT_AUTHORITY_V1: bool = false;
pub const SPOT_V7_FIRECRACKER_RELEASE_AUTHORITY_V1: bool = false;
pub const SPOT_V7_FIRECRACKER_PRODUCTION_READY_V1: bool = false;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SpotV7FirecrackerProtocolErrorV1 {
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
    V7OutputLength,
    V7OutputMagic,
    V7OutputVersion,
    V7OutputFraming,
    V7OutputFixedField,
    V7OutputJournalBinding,
    V7JournalLength,
    V7JournalMagic,
    V7JournalVersion,
    V7JournalFraming,
    V7JournalFixedField,
    V7SemanticJournalSha256,
    V7EffectBindingCommitment,
    V7EffectBindingLength,
    V7EffectBindingVersion,
    V7EffectBindingField,
    V7PlanCommitmentBinding,
    V7PlanBytesSha256,
}

impl SpotV7FirecrackerProtocolErrorV1 {
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
            Self::V7OutputLength => "v7_output_length",
            Self::V7OutputMagic => "v7_output_magic",
            Self::V7OutputVersion => "v7_output_version",
            Self::V7OutputFraming => "v7_output_framing",
            Self::V7OutputFixedField => "v7_output_fixed_field",
            Self::V7OutputJournalBinding => "v7_output_journal_binding",
            Self::V7JournalLength => "v7_journal_length",
            Self::V7JournalMagic => "v7_journal_magic",
            Self::V7JournalVersion => "v7_journal_version",
            Self::V7JournalFraming => "v7_journal_framing",
            Self::V7JournalFixedField => "v7_journal_fixed_field",
            Self::V7SemanticJournalSha256 => "v7_semantic_journal_hash",
            Self::V7EffectBindingCommitment => "v7_effect_binding_commitment",
            Self::V7EffectBindingLength => "v7_effect_binding_length",
            Self::V7EffectBindingVersion => "v7_effect_binding_version",
            Self::V7EffectBindingField => "v7_effect_binding_field",
            Self::V7PlanCommitmentBinding => "v7_plan_commitment_binding",
            Self::V7PlanBytesSha256 => "v7_plan_bytes_sha256",
        }
    }
}

impl fmt::Display for SpotV7FirecrackerProtocolErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(self.code())
    }
}

impl std::error::Error for SpotV7FirecrackerProtocolErrorV1 {}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SpotV7FirecrackerRequestV1 {
    run_nonce_256: [u8; 32],
    runtime_manifest_sha256: [u8; 32],
    input_drive_sha256: [u8; 32],
    settlement_intent_sha256: [u8; 32],
}

impl SpotV7FirecrackerRequestV1 {
    pub fn new(
        run_nonce_256: [u8; 32],
        runtime_manifest_sha256: [u8; 32],
        input_drive_sha256: [u8; 32],
        settlement_intent_sha256: [u8; 32],
    ) -> Result<Self, SpotV7FirecrackerProtocolErrorV1> {
        require_nonzero(
            &run_nonce_256,
            SpotV7FirecrackerProtocolErrorV1::RequestNonce,
        )?;
        require_nonzero(
            &runtime_manifest_sha256,
            SpotV7FirecrackerProtocolErrorV1::RequestManifest,
        )?;
        require_nonzero(
            &input_drive_sha256,
            SpotV7FirecrackerProtocolErrorV1::RequestInput,
        )?;
        require_nonzero(
            &settlement_intent_sha256,
            SpotV7FirecrackerProtocolErrorV1::RequestIntent,
        )?;
        Ok(Self {
            run_nonce_256,
            runtime_manifest_sha256,
            input_drive_sha256,
            settlement_intent_sha256,
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

    pub const fn settlement_intent_sha256(&self) -> &[u8; 32] {
        &self.settlement_intent_sha256
    }

    pub fn encode(&self) -> [u8; SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1] {
        let mut output = [0_u8; SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1];
        output[0..8].copy_from_slice(REQUEST_MAGIC_V1);
        output[8..10].copy_from_slice(&PROTOCOL_VERSION_V1.to_le_bytes());
        output[10..12].copy_from_slice(&REQUEST_BYTES_FIELD_V1.to_le_bytes());
        output[16..48].copy_from_slice(&self.run_nonce_256);
        output[48..80].copy_from_slice(&SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1);
        output[80..112].copy_from_slice(&self.runtime_manifest_sha256);
        output[112..144].copy_from_slice(&self.input_drive_sha256);
        output[144..152].copy_from_slice(&OUTPUT_BYTES_FIELD_V1.to_le_bytes());
        output[152..156].copy_from_slice(&OUTPUT_PAYLOAD_CAP_FIELD_V1.to_le_bytes());
        output[156..188].copy_from_slice(&self.settlement_intent_sha256);
        output
    }

    pub fn decode(bytes: &[u8]) -> Result<Self, SpotV7FirecrackerProtocolErrorV1> {
        validate_request_header(bytes)?;
        let profile = array_32(bytes, 48, SpotV7FirecrackerProtocolErrorV1::RequestProfile)?;
        if profile != SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1 {
            return Err(SpotV7FirecrackerProtocolErrorV1::RequestProfile);
        }
        if bytes[188..].iter().any(|byte| *byte != 0) {
            return Err(SpotV7FirecrackerProtocolErrorV1::RequestReserved);
        }
        Self::new(
            array_32(bytes, 16, SpotV7FirecrackerProtocolErrorV1::RequestNonce)?,
            array_32(bytes, 80, SpotV7FirecrackerProtocolErrorV1::RequestManifest)?,
            array_32(bytes, 112, SpotV7FirecrackerProtocolErrorV1::RequestInput)?,
            array_32(bytes, 156, SpotV7FirecrackerProtocolErrorV1::RequestIntent)?,
        )
    }

    pub fn sha256(&self) -> [u8; 32] {
        sha256(&self.encode())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StructurallyDecodedSpotV7PayloadV1 {
    raw_bytes: Vec<u8>,
    journal_bytes: Vec<u8>,
    plan_b_bytes: Vec<u8>,
    state_root_host_input_length: u32,
}

impl StructurallyDecodedSpotV7PayloadV1 {
    pub fn raw_bytes(&self) -> &[u8] {
        &self.raw_bytes
    }

    pub fn journal_bytes(&self) -> &[u8] {
        &self.journal_bytes
    }

    pub fn plan_b_bytes(&self) -> &[u8] {
        &self.plan_b_bytes
    }

    pub const fn state_root_host_input_length(&self) -> u32 {
        self.state_root_host_input_length
    }

    pub fn sha256(&self) -> [u8; 32] {
        sha256(&self.raw_bytes)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DecodedV7JournalV1 {
    raw_bytes: Vec<u8>,
    plan_b_bytes: Vec<u8>,
    fixed_fields: [[u8; 32]; V7_JOURNAL_FIXED_FIELD_COUNT_V1],
    effect_binding_fields: [[u8; 32]; 12],
    state_root_host_input_length: u32,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct V7JournalShapeV1 {
    host_input_length: u32,
    semantic_length: usize,
    binding_length: usize,
    plan_length: usize,
}

pub fn decode_structural_spot_v7_payload_v1(
    bytes: &[u8],
) -> Result<StructurallyDecodedSpotV7PayloadV1, SpotV7FirecrackerProtocolErrorV1> {
    if bytes.len() <= V7_OUTPUT_HEADER_BYTES_V1
        || bytes.len() > SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7OutputLength);
    }
    if &bytes[0..8] != V7_OUTPUT_MAGIC_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7OutputMagic);
    }
    if read_u16_be(bytes, 8)? != V7_OUTPUT_VERSION_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7OutputVersion);
    }
    let total = read_usize_u32_be(bytes, 10)?;
    let journal_length = read_usize_u32_be(bytes, 14)?;
    let plan_length = read_usize_u32_be(bytes, 18)?;
    let host_input_length = read_u32_be(bytes, 22)?;
    if total != bytes.len()
        || journal_length != bytes.len() - V7_OUTPUT_HEADER_BYTES_V1
        || plan_length == 0
        || plan_length > V7_MAX_PLAN_B_BYTES_V1
        || host_input_length == 0
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7OutputFraming);
    }
    let fixed = read_fixed_fields::<V7_OUTPUT_FIXED_FIELD_COUNT_V1>(
        bytes,
        26,
        SpotV7FirecrackerProtocolErrorV1::V7OutputFixedField,
    )?;
    let journal_bytes = bytes
        .get(V7_OUTPUT_HEADER_BYTES_V1..)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7OutputFraming)?;
    let journal = decode_exact_v7_journal_v1(journal_bytes)?;
    if plan_length != journal.plan_b_bytes.len()
        || host_input_length != journal.state_root_host_input_length
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7OutputJournalBinding);
    }
    require_output_journal_associations(&fixed, &journal)?;
    Ok(StructurallyDecodedSpotV7PayloadV1 {
        raw_bytes: bytes.to_vec(),
        journal_bytes: journal.raw_bytes,
        plan_b_bytes: journal.plan_b_bytes,
        state_root_host_input_length: host_input_length,
    })
}

pub fn read_request_from_output_v1(
    output: &mut File,
) -> Result<SpotV7FirecrackerRequestV1, SpotV7FirecrackerProtocolErrorV1> {
    require_output_file_size(output)?;
    output
        .seek(SeekFrom::Start(0))
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputIo)?;
    let mut bytes = [0_u8; SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1];
    output
        .read_exact(&mut bytes)
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputIo)?;
    SpotV7FirecrackerRequestV1::decode(&bytes)
}

pub fn commit_data_only_output_v1(
    output: &mut File,
    request: &SpotV7FirecrackerRequestV1,
    observed_input_drive_sha256: [u8; 32],
    payload: &StructurallyDecodedSpotV7PayloadV1,
) -> Result<(), SpotV7FirecrackerProtocolErrorV1> {
    if &observed_input_drive_sha256 != request.input_drive_sha256() {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputBinding);
    }
    let (header, marker) = build_output_header_and_marker(request, payload.raw_bytes())?;
    require_output_file_size(output)?;
    zero_output(output)?;
    output
        .seek(SeekFrom::Start(0))
        .and_then(|_| output.write_all(&header))
        .and_then(|_| output.write_all(payload.raw_bytes()))
        .and_then(|_| output.sync_data())
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputIo)?;
    output
        .seek(SeekFrom::Start(COMMIT_OFFSET_V1))
        .and_then(|_| output.write_all(&marker))
        .and_then(|_| output.sync_data())
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputIo)
}

pub fn build_data_only_output_image_v1(
    request: &SpotV7FirecrackerRequestV1,
    observed_input_drive_sha256: [u8; 32],
    payload: &StructurallyDecodedSpotV7PayloadV1,
) -> Result<Vec<u8>, SpotV7FirecrackerProtocolErrorV1> {
    if &observed_input_drive_sha256 != request.input_drive_sha256() {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputBinding);
    }
    let (header, marker) = build_output_header_and_marker(request, payload.raw_bytes())?;
    let mut output = vec![0_u8; SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1];
    output[..SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1].copy_from_slice(&header);
    let payload_end = SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1
        .checked_add(payload.raw_bytes().len())
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputPayload)?;
    output[SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1..payload_end]
        .copy_from_slice(payload.raw_bytes());
    output[SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1 - SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_BYTES_V1..]
        .copy_from_slice(&marker);
    Ok(output)
}

pub fn validate_committed_output_v1(
    bytes: &[u8],
    request: &SpotV7FirecrackerRequestV1,
) -> Result<StructurallyDecodedSpotV7PayloadV1, SpotV7FirecrackerProtocolErrorV1> {
    if bytes.len() != SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputLength);
    }
    let payload_length = validate_output_header(bytes, request)?;
    let payload_end = SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1
        .checked_add(payload_length)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputPayload)?;
    let commit_offset =
        SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1 - SPOT_V7_FIRECRACKER_OUTPUT_COMMIT_BYTES_V1;
    if payload_end > commit_offset {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputPayload);
    }
    let payload = bytes
        .get(SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1..payload_end)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputPayload)?;
    if sha256(payload) != array_32(bytes, 224, SpotV7FirecrackerProtocolErrorV1::OutputPayload)? {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputPayload);
    }
    if bytes[payload_end..commit_offset]
        .iter()
        .any(|byte| *byte != 0)
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputTrailingBytes);
    }
    let marker = output_commit_marker(
        request,
        &bytes[..SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1],
        payload,
    );
    if bytes[commit_offset..] != marker {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputCommit);
    }
    decode_structural_spot_v7_payload_v1(payload)
}

fn validate_request_header(bytes: &[u8]) -> Result<(), SpotV7FirecrackerProtocolErrorV1> {
    if bytes.len() != SPOT_V7_FIRECRACKER_REQUEST_BYTES_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::RequestLength);
    }
    if &bytes[0..8] != REQUEST_MAGIC_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::RequestMagic);
    }
    if read_u16_le(bytes, 8)? != PROTOCOL_VERSION_V1
        || read_u16_le(bytes, 10)? != REQUEST_BYTES_FIELD_V1
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::RequestVersion);
    }
    if read_u32_le(bytes, 12)? != 0 {
        return Err(SpotV7FirecrackerProtocolErrorV1::RequestFlags);
    }
    if read_u64_le(bytes, 144)? != OUTPUT_BYTES_FIELD_V1
        || read_u32_le(bytes, 152)? != OUTPUT_PAYLOAD_CAP_FIELD_V1
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::RequestOutputBounds);
    }
    Ok(())
}

fn build_output_header_and_marker(
    request: &SpotV7FirecrackerRequestV1,
    payload: &[u8],
) -> Result<
    ([u8; SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1], [u8; 32]),
    SpotV7FirecrackerProtocolErrorV1,
> {
    if payload.is_empty() || payload.len() > SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputPayload);
    }
    let payload_length = u32::try_from(payload.len())
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputPayload)?;
    let mut header = [0_u8; SPOT_V7_FIRECRACKER_OUTPUT_HEADER_BYTES_V1];
    header[0..8].copy_from_slice(OUTPUT_MAGIC_V1);
    header[8..10].copy_from_slice(&PROTOCOL_VERSION_V1.to_le_bytes());
    header[10..12].copy_from_slice(&OUTPUT_HEADER_BYTES_FIELD_V1.to_le_bytes());
    header[12..16].copy_from_slice(&DATA_ONLY_COMMITTED_STATUS_V1.to_le_bytes());
    header[16..20].copy_from_slice(&payload_length.to_le_bytes());
    header[24..32].copy_from_slice(&OUTPUT_BYTES_FIELD_V1.to_le_bytes());
    header[32..64].copy_from_slice(request.run_nonce_256());
    header[64..96].copy_from_slice(&request.sha256());
    header[96..128].copy_from_slice(&SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1);
    header[128..160].copy_from_slice(request.runtime_manifest_sha256());
    header[160..192].copy_from_slice(request.input_drive_sha256());
    header[192..224].copy_from_slice(request.settlement_intent_sha256());
    header[224..256].copy_from_slice(&sha256(payload));
    let marker = output_commit_marker(request, &header, payload);
    Ok((header, marker))
}

fn validate_output_header(
    bytes: &[u8],
    request: &SpotV7FirecrackerRequestV1,
) -> Result<usize, SpotV7FirecrackerProtocolErrorV1> {
    if &bytes[0..8] != OUTPUT_MAGIC_V1
        || read_u16_le(bytes, 8)? != PROTOCOL_VERSION_V1
        || read_u16_le(bytes, 10)? != OUTPUT_HEADER_BYTES_FIELD_V1
        || read_u32_le(bytes, 12)? != DATA_ONLY_COMMITTED_STATUS_V1
        || read_u32_le(bytes, 20)? != 0
        || read_u64_le(bytes, 24)? != OUTPUT_BYTES_FIELD_V1
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputHeader);
    }
    let bindings = [
        (32, *request.run_nonce_256()),
        (64, request.sha256()),
        (96, SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1),
        (128, *request.runtime_manifest_sha256()),
        (160, *request.input_drive_sha256()),
        (192, *request.settlement_intent_sha256()),
    ];
    for (offset, expected) in bindings {
        if array_32(
            bytes,
            offset,
            SpotV7FirecrackerProtocolErrorV1::OutputBinding,
        )? != expected
        {
            return Err(SpotV7FirecrackerProtocolErrorV1::OutputBinding);
        }
    }
    let payload_length = usize::try_from(read_u32_le(bytes, 16)?)
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputPayload)?;
    if payload_length == 0 || payload_length > SPOT_V7_FIRECRACKER_OUTPUT_PAYLOAD_CAP_BYTES_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputPayload);
    }
    Ok(payload_length)
}

fn decode_exact_v7_journal_v1(
    bytes: &[u8],
) -> Result<DecodedV7JournalV1, SpotV7FirecrackerProtocolErrorV1> {
    let minimum = V7_JOURNAL_HEADER_BYTES_V1
        + 32 * V7_JOURNAL_FIXED_FIELD_COUNT_V1
        + V7_SEMANTIC_JOURNAL_BYTES_V1
        + V7_EFFECT_BINDING_JOURNAL_BYTES_V1;
    if bytes.len() <= minimum || bytes.len() > minimum + V7_MAX_PLAN_B_BYTES_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7JournalLength);
    }
    if &bytes[0..8] != V7_JOURNAL_MAGIC_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7JournalMagic);
    }
    if read_u16_be(bytes, 8)? != V7_JOURNAL_VERSION_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7JournalVersion);
    }
    let total = read_usize_u32_be(bytes, 10)?;
    let host_length = read_u32_be(bytes, 14)?;
    let semantic_length = usize::from(read_u16_be(bytes, 18)?);
    let binding_length = usize::from(read_u16_be(bytes, 20)?);
    let plan_length = read_usize_u32_be(bytes, 22)?;
    let shape = V7JournalShapeV1 {
        host_input_length: host_length,
        semantic_length,
        binding_length,
        plan_length,
    };
    if total != bytes.len()
        || shape.host_input_length == 0
        || shape.semantic_length != V7_SEMANTIC_JOURNAL_BYTES_V1
        || shape.binding_length != V7_EFFECT_BINDING_JOURNAL_BYTES_V1
        || shape.plan_length == 0
        || shape.plan_length > V7_MAX_PLAN_B_BYTES_V1
        || minimum.checked_add(shape.plan_length) != Some(bytes.len())
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7JournalFraming);
    }
    decode_v7_journal_body(bytes, shape)
}

fn decode_v7_journal_body(
    bytes: &[u8],
    shape: V7JournalShapeV1,
) -> Result<DecodedV7JournalV1, SpotV7FirecrackerProtocolErrorV1> {
    let fixed = read_fixed_fields::<V7_JOURNAL_FIXED_FIELD_COUNT_V1>(
        bytes,
        V7_JOURNAL_HEADER_BYTES_V1,
        SpotV7FirecrackerProtocolErrorV1::V7JournalFixedField,
    )?;
    let mut cursor = V7_JOURNAL_HEADER_BYTES_V1 + 32 * V7_JOURNAL_FIXED_FIELD_COUNT_V1;
    let semantic = bounded_slice(bytes, cursor, shape.semantic_length)?;
    cursor = cursor
        .checked_add(shape.semantic_length)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7JournalFraming)?;
    let binding = bounded_slice(bytes, cursor, shape.binding_length)?;
    cursor = cursor
        .checked_add(shape.binding_length)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7JournalFraming)?;
    let plan = bounded_slice(bytes, cursor, shape.plan_length)?;
    if sha256(semantic) != fixed[8] {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7SemanticJournalSha256);
    }
    if binding_journal_commitment(binding) != fixed[9] {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7EffectBindingCommitment);
    }
    let binding_fields = decode_effect_binding_journal_v1(binding)?;
    if binding_fields[4] != fixed[10] {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7PlanCommitmentBinding);
    }
    if sha256(plan) != fixed[11] {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7PlanBytesSha256);
    }
    Ok(DecodedV7JournalV1 {
        raw_bytes: bytes.to_vec(),
        plan_b_bytes: plan.to_vec(),
        fixed_fields: fixed,
        effect_binding_fields: binding_fields,
        state_root_host_input_length: shape.host_input_length,
    })
}

fn decode_effect_binding_journal_v1(
    bytes: &[u8],
) -> Result<[[u8; 32]; 12], SpotV7FirecrackerProtocolErrorV1> {
    if bytes.len() != V7_EFFECT_BINDING_JOURNAL_BYTES_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7EffectBindingLength);
    }
    if read_u16_be(bytes, 0)? != 1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7EffectBindingVersion);
    }
    read_fixed_fields::<12>(
        bytes,
        2,
        SpotV7FirecrackerProtocolErrorV1::V7EffectBindingField,
    )
}

fn require_output_journal_associations(
    output: &[[u8; 32]; V7_OUTPUT_FIXED_FIELD_COUNT_V1],
    journal: &DecodedV7JournalV1,
) -> Result<(), SpotV7FirecrackerProtocolErrorV1> {
    let fixed = &journal.fixed_fields;
    let binding = &journal.effect_binding_fields;
    let expected = [
        (3, sha256(&journal.raw_bytes)),
        (4, fixed[0]),
        (5, fixed[1]),
        (6, fixed[2]),
        (7, fixed[3]),
        (8, fixed[4]),
        (9, fixed[5]),
        (10, fixed[10]),
        (11, fixed[11]),
        (12, binding[6]),
        (13, binding[7]),
        (14, fixed[12]),
        (18, fixed[7]),
    ];
    if expected
        .iter()
        .any(|(index, value)| output[*index] != *value)
    {
        return Err(SpotV7FirecrackerProtocolErrorV1::V7OutputJournalBinding);
    }
    Ok(())
}

fn output_commit_marker(
    request: &SpotV7FirecrackerRequestV1,
    header: &[u8],
    payload: &[u8],
) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(OUTPUT_COMMIT_DOMAIN_V1);
    hasher.update(SPOT_V7_FIRECRACKER_RUNTIME_PROFILE_SHA256_V1);
    hasher.update(request.sha256());
    hasher.update(header);
    hasher.update(payload);
    hasher.finalize().into()
}

fn binding_journal_commitment(bytes: &[u8]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(V7_EFFECT_BINDING_COMMITMENT_DOMAIN_BYTES_V1.to_be_bytes());
    hasher.update(V7_EFFECT_BINDING_COMMITMENT_DOMAIN_V1);
    hasher.update(bytes);
    hasher.finalize().into()
}

fn zero_output(output: &mut File) -> Result<(), SpotV7FirecrackerProtocolErrorV1> {
    output
        .seek(SeekFrom::Start(0))
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputIo)?;
    let block = [0_u8; 65_536];
    for _ in 0..(SPOT_V7_FIRECRACKER_OUTPUT_BYTES_V1 / block.len()) {
        output
            .write_all(&block)
            .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputIo)?;
    }
    Ok(())
}

fn require_output_file_size(output: &mut File) -> Result<(), SpotV7FirecrackerProtocolErrorV1> {
    let size = output
        .seek(SeekFrom::End(0))
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::OutputIo)?;
    if size != OUTPUT_BYTES_FIELD_V1 {
        return Err(SpotV7FirecrackerProtocolErrorV1::OutputLength);
    }
    Ok(())
}

fn require_nonzero(
    value: &[u8; 32],
    error: SpotV7FirecrackerProtocolErrorV1,
) -> Result<(), SpotV7FirecrackerProtocolErrorV1> {
    if value.iter().all(|byte| *byte == 0) {
        return Err(error);
    }
    Ok(())
}

fn read_fixed_fields<const N: usize>(
    bytes: &[u8],
    offset: usize,
    error: SpotV7FirecrackerProtocolErrorV1,
) -> Result<[[u8; 32]; N], SpotV7FirecrackerProtocolErrorV1> {
    let mut fields = [[0_u8; 32]; N];
    for (index, field) in fields.iter_mut().enumerate() {
        let field_offset = index
            .checked_mul(32)
            .and_then(|delta| offset.checked_add(delta))
            .ok_or(error)?;
        *field = array_32(bytes, field_offset, error)?;
        require_nonzero(field, error)?;
    }
    Ok(fields)
}

fn bounded_slice(
    bytes: &[u8],
    offset: usize,
    length: usize,
) -> Result<&[u8], SpotV7FirecrackerProtocolErrorV1> {
    let end = offset
        .checked_add(length)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7JournalFraming)?;
    bytes
        .get(offset..end)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7JournalFraming)
}

fn array_32(
    bytes: &[u8],
    offset: usize,
    error: SpotV7FirecrackerProtocolErrorV1,
) -> Result<[u8; 32], SpotV7FirecrackerProtocolErrorV1> {
    let end = offset.checked_add(32).ok_or(error)?;
    bytes
        .get(offset..end)
        .and_then(|value| value.try_into().ok())
        .ok_or(error)
}

fn read_u16_le(bytes: &[u8], offset: usize) -> Result<u16, SpotV7FirecrackerProtocolErrorV1> {
    let end = offset
        .checked_add(2)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputHeader)?;
    bytes
        .get(offset..end)
        .and_then(|value| value.try_into().ok())
        .map(u16::from_le_bytes)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputHeader)
}

fn read_u32_le(bytes: &[u8], offset: usize) -> Result<u32, SpotV7FirecrackerProtocolErrorV1> {
    let end = offset
        .checked_add(4)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputHeader)?;
    bytes
        .get(offset..end)
        .and_then(|value| value.try_into().ok())
        .map(u32::from_le_bytes)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputHeader)
}

fn read_u64_le(bytes: &[u8], offset: usize) -> Result<u64, SpotV7FirecrackerProtocolErrorV1> {
    let end = offset
        .checked_add(8)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputHeader)?;
    bytes
        .get(offset..end)
        .and_then(|value| value.try_into().ok())
        .map(u64::from_le_bytes)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::OutputHeader)
}

fn read_u16_be(bytes: &[u8], offset: usize) -> Result<u16, SpotV7FirecrackerProtocolErrorV1> {
    let end = offset
        .checked_add(2)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7OutputFraming)?;
    bytes
        .get(offset..end)
        .and_then(|value| value.try_into().ok())
        .map(u16::from_be_bytes)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7OutputFraming)
}

fn read_u32_be(bytes: &[u8], offset: usize) -> Result<u32, SpotV7FirecrackerProtocolErrorV1> {
    let end = offset
        .checked_add(4)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7OutputFraming)?;
    bytes
        .get(offset..end)
        .and_then(|value| value.try_into().ok())
        .map(u32::from_be_bytes)
        .ok_or(SpotV7FirecrackerProtocolErrorV1::V7OutputFraming)
}

fn read_usize_u32_be(
    bytes: &[u8],
    offset: usize,
) -> Result<usize, SpotV7FirecrackerProtocolErrorV1> {
    usize::try_from(read_u32_be(bytes, offset)?)
        .map_err(|_| SpotV7FirecrackerProtocolErrorV1::V7OutputFraming)
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}
