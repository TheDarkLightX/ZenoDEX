//! Authority-neutral execution profiling for exact ZRPF RISC0 stages.
//!
//! Execution establishes workload shape and expected-journal parity. It does
//! not generate a receipt and cannot grant proof, release, settlement, or
//! production authority.

use std::{env, fmt, fs, io::Read, os::unix::fs::MetadataExt, path::Path, time::Instant};

use risc0_zkvm::{
    compute_image_id, default_executor, sha::Digestible, Digest, ExecutorEnv, ExitCode, Receipt,
};
use serde::{Deserialize, Serialize};
use sha2::{Digest as _, Sha256};

pub const STAGE_EXECUTION_PROFILE_SCHEMA_V1: &str = "zenodex/zrpf_risc0_stage_execution_profile/v1";
pub const STAGE_EXECUTION_PROFILE_STATUS_V1: &str =
    "exact_execution_observed_without_proof_or_accelerator_authority";
pub const ZRPF_SEGMENT_LIMIT_PO2_V1: u32 = 20;
pub const MIN_SEGMENT_PO2_V1: u32 = 13;
pub const MAX_SEGMENT_PO2_V1: u32 = 24;
pub const MAX_PROFILE_BYTES_V1: usize = 2 * 1024 * 1024;
pub const MAX_SEGMENTS_V1: usize = 65_536;
pub const MAX_R0VM_BYTES_V1: u64 = 512 * 1024 * 1024;
pub const ZRPF_PROOF_PROFILE_ID_V1: &str = "risc0_succinct_poseidon2_resolve_3_0_5_v1";

const RECORD_ID_DOMAIN_V1: &[u8] = b"zenodex/zrpf-risc0-stage-execution-profile-id/v1\0";
const ZERO_SHA256: &str = "0000000000000000000000000000000000000000000000000000000000000000";
const CPU_COMPUTE_PROFILE_ID_V1: &str = "risc0_ipc_cpu_v1";
const CUDA_COMPUTE_PROFILE_ID_V1: &str = "risc0_ipc_cuda_single_visible_device_build_request_v1";
const NON_CLAIMS_V1: [&str; 5] = [
    "execution profiling generates no RISC0 receipt or proof",
    "execution profiling does not establish CUDA or other accelerator execution",
    "the observed r0vm bytes have no source-to-binary or release authority",
    "the profile grants no settlement or ledger authority",
    "the profile grants no production authority",
];

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecutionProfileErrorV1(String);

impl ExecutionProfileErrorV1 {
    fn reject(message: impl Into<String>) -> Self {
        Self(message.into())
    }
}

impl fmt::Display for ExecutionProfileErrorV1 {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for ExecutionProfileErrorV1 {}

#[derive(Clone, Debug)]
pub struct ExactAssumptionV1<'a> {
    receipt: &'a Receipt,
    expected_image_id: [u32; 8],
}

impl<'a> ExactAssumptionV1<'a> {
    pub fn new(receipt: &'a Receipt, expected_image_id: [u32; 8]) -> Self {
        Self {
            receipt,
            expected_image_id,
        }
    }
}

#[derive(Clone, Debug)]
pub struct ExactStageExecutionRequestV1<'a> {
    stage_id: &'a str,
    proof_profile_id: &'a str,
    program_elf: &'a [u8],
    expected_image_id: [u32; 8],
    guest_input_bytes: &'a [u8],
    assumptions: &'a [ExactAssumptionV1<'a>],
    expected_journal_bytes: &'a [u8],
}

impl<'a> ExactStageExecutionRequestV1<'a> {
    pub fn new(
        stage_id: &'a str,
        proof_profile_id: &'a str,
        program_elf: &'a [u8],
        expected_image_id: [u32; 8],
        guest_input_bytes: &'a [u8],
        assumptions: &'a [ExactAssumptionV1<'a>],
        expected_journal_bytes: &'a [u8],
    ) -> Result<Self, ExecutionProfileErrorV1> {
        validate_identifier(stage_id, "stage ID")?;
        if proof_profile_id != ZRPF_PROOF_PROFILE_ID_V1 {
            return Err(ExecutionProfileErrorV1::reject(
                "execution-profile proof profile is not governed",
            ));
        }
        if program_elf.is_empty() {
            return Err(ExecutionProfileErrorV1::reject(
                "execution-profile program ELF is empty",
            ));
        }
        if expected_image_id.iter().all(|word| *word == 0) {
            return Err(ExecutionProfileErrorV1::reject(
                "execution-profile image ID is zero",
            ));
        }
        if guest_input_bytes.is_empty() {
            return Err(ExecutionProfileErrorV1::reject(
                "execution-profile guest input is empty",
            ));
        }
        if expected_journal_bytes.is_empty() {
            return Err(ExecutionProfileErrorV1::reject(
                "execution-profile expected journal is empty",
            ));
        }
        Ok(Self {
            stage_id,
            proof_profile_id,
            program_elf,
            expected_image_id,
            guest_input_bytes,
            assumptions,
            expected_journal_bytes,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExecutionObservationV1 {
    exit_system: u32,
    exit_user: u32,
    journal_bytes: Vec<u8>,
    receipt_claim_sha256: String,
    segments: Vec<SegmentMeasurementV1>,
    duration_milliseconds: u64,
}

impl ExecutionObservationV1 {
    pub fn new(
        exit_system: u32,
        exit_user: u32,
        journal_bytes: Vec<u8>,
        receipt_claim_sha256: String,
        segments: Vec<SegmentMeasurementV1>,
        duration_milliseconds: u64,
    ) -> Self {
        Self {
            exit_system,
            exit_user,
            journal_bytes,
            receipt_claim_sha256,
            segments,
            duration_milliseconds,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ArtifactIdentityV1 {
    sha256: String,
    size_bytes: u64,
}

impl ArtifactIdentityV1 {
    pub fn from_bytes(bytes: &[u8]) -> Result<Self, ExecutionProfileErrorV1> {
        let size_bytes = u64::try_from(bytes.len())
            .map_err(|_| ExecutionProfileErrorV1::reject("artifact size does not fit in u64"))?;
        Ok(Self {
            sha256: sha256_hex(bytes),
            size_bytes,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ProgramIdentityV1 {
    artifact: ArtifactIdentityV1,
    image_id: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct AssumptionIdentityV1 {
    ordinal: u32,
    receipt: ArtifactIdentityV1,
    expected_image_id: String,
    journal_sha256: String,
    journal_bytes: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SegmentMeasurementV1 {
    ordinal: u32,
    po2: u32,
    user_cycles: u64,
    padded_cycle_capacity: u64,
}

impl SegmentMeasurementV1 {
    pub fn new(ordinal: u32, po2: u32, user_cycles: u64) -> Result<Self, ExecutionProfileErrorV1> {
        let padded_cycle_capacity = 1u64.checked_shl(po2).ok_or_else(|| {
            ExecutionProfileErrorV1::reject("segment po2 overflows padded cycle capacity")
        })?;
        if !(MIN_SEGMENT_PO2_V1..=MAX_SEGMENT_PO2_V1).contains(&po2) {
            return Err(ExecutionProfileErrorV1::reject(
                "segment po2 is outside the governed range",
            ));
        }
        if user_cycles > padded_cycle_capacity {
            return Err(ExecutionProfileErrorV1::reject(
                "segment user cycles exceed padded capacity",
            ));
        }
        Ok(Self {
            ordinal,
            po2,
            user_cycles,
            padded_cycle_capacity,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ExecutionAuthorityV1 {
    proof_generated: bool,
    accelerator_execution_verified: bool,
    proof_authority: bool,
    release_authority: bool,
    settlement_authority: bool,
    production_authority: bool,
}

impl ExecutionAuthorityV1 {
    fn all_false() -> Self {
        Self {
            proof_generated: false,
            accelerator_execution_verified: false,
            proof_authority: false,
            release_authority: false,
            settlement_authority: false,
            production_authority: false,
        }
    }

    fn is_all_false(&self) -> bool {
        !self.proof_generated
            && !self.accelerator_execution_verified
            && !self.proof_authority
            && !self.release_authority
            && !self.settlement_authority
            && !self.production_authority
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct StageExecutionProfileV1 {
    schema: String,
    status: String,
    profile_record_id: String,
    stage_id: String,
    proof_profile_id: String,
    prover_compute_profile_id: String,
    program: ProgramIdentityV1,
    r0vm: ArtifactIdentityV1,
    guest_input: ArtifactIdentityV1,
    assumptions: Vec<AssumptionIdentityV1>,
    expected_journal: ArtifactIdentityV1,
    observed_journal: ArtifactIdentityV1,
    receipt_claim_sha256: String,
    segment_limit_po2: u32,
    segments: Vec<SegmentMeasurementV1>,
    segment_count: u32,
    total_user_cycles: u64,
    total_padded_cycle_capacity: u64,
    exit_system: u32,
    exit_user: u32,
    duration_milliseconds: u64,
    authority: ExecutionAuthorityV1,
    non_claims: Vec<String>,
}

impl StageExecutionProfileV1 {
    pub fn profile_record_id(&self) -> &str {
        &self.profile_record_id
    }

    pub fn stage_id(&self) -> &str {
        &self.stage_id
    }

    pub fn prover_compute_profile_id(&self) -> &str {
        &self.prover_compute_profile_id
    }

    pub const fn segment_count(&self) -> u32 {
        self.segment_count
    }

    pub const fn total_user_cycles(&self) -> u64 {
        self.total_user_cycles
    }

    pub const fn total_padded_cycle_capacity(&self) -> u64 {
        self.total_padded_cycle_capacity
    }

    pub const fn duration_milliseconds(&self) -> u64 {
        self.duration_milliseconds
    }
}

pub fn build_exact_framed_executor_env_v1(
    guest_input_bytes: &[u8],
    assumptions: &[Receipt],
) -> Result<ExecutorEnv<'static>, ExecutionProfileErrorV1> {
    let input_length = u32::try_from(guest_input_bytes.len()).map_err(|_| {
        ExecutionProfileErrorV1::reject("execution-profile guest input exceeds u32")
    })?;
    let mut builder = ExecutorEnv::builder();
    builder
        .write_slice(&[input_length])
        .write_slice(guest_input_bytes)
        .segment_limit_po2(ZRPF_SEGMENT_LIMIT_PO2_V1);
    for receipt in assumptions {
        builder.add_assumption(receipt.clone());
    }
    builder.build().map_err(|error| {
        ExecutionProfileErrorV1::reject(format!(
            "execution-profile executor environment rejected: {error}"
        ))
    })
}

pub fn execute_exact_stage_v1(
    request: &ExactStageExecutionRequestV1<'_>,
) -> Result<StageExecutionProfileV1, ExecutionProfileErrorV1> {
    if env::var_os("RISC0_DEV_MODE").is_some() {
        return Err(ExecutionProfileErrorV1::reject(
            "ambient RISC0_DEV_MODE is forbidden",
        ));
    }
    let prover_compute_profile_id = governed_compute_profile_from_environment()?;
    let r0vm_path = governed_r0vm_path_from_environment()?;
    let r0vm_before = stable_regular_file_bytes(&r0vm_path, MAX_R0VM_BYTES_V1, "r0vm")?;
    let computed_image_id = compute_image_id(request.program_elf).map_err(|error| {
        ExecutionProfileErrorV1::reject(format!("compute execution-profile image ID: {error}"))
    })?;
    if computed_image_id != Digest::from(request.expected_image_id) {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile program image ID mismatch",
        ));
    }
    let mut assumption_receipts = Vec::with_capacity(request.assumptions.len());
    for assumption in request.assumptions {
        assumption
            .receipt
            .verify(assumption.expected_image_id)
            .map_err(|error| {
                ExecutionProfileErrorV1::reject(format!(
                    "execution-profile assumption verification failed: {error}"
                ))
            })?;
        assumption_receipts.push(assumption.receipt.clone());
    }
    let executor_env =
        build_exact_framed_executor_env_v1(request.guest_input_bytes, &assumption_receipts)?;
    let started = Instant::now();
    let session = default_executor()
        .execute(executor_env, request.program_elf)
        .map_err(|error| {
            ExecutionProfileErrorV1::reject(format!(
                "execution-profile guest execution failed: {error:#}"
            ))
        })?;
    let duration_milliseconds = u64::try_from(started.elapsed().as_millis())
        .map_err(|_| ExecutionProfileErrorV1::reject("execution-profile duration exceeds u64"))?;
    let r0vm_after = stable_regular_file_bytes(&r0vm_path, MAX_R0VM_BYTES_V1, "r0vm")?;
    if r0vm_before != r0vm_after {
        return Err(ExecutionProfileErrorV1::reject(
            "r0vm bytes changed across execution",
        ));
    }
    let (exit_system, exit_user) = exit_pair(session.exit_code)?;
    let receipt_claim = session.receipt_claim.ok_or_else(|| {
        ExecutionProfileErrorV1::reject("execution-profile session omitted its receipt claim")
    })?;
    let segments = session
        .segments
        .iter()
        .enumerate()
        .map(|(ordinal, segment)| {
            let ordinal = u32::try_from(ordinal).map_err(|_| {
                ExecutionProfileErrorV1::reject("execution-profile segment ordinal exceeds u32")
            })?;
            SegmentMeasurementV1::new(ordinal, segment.po2, u64::from(segment.cycles))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let observation = ExecutionObservationV1::new(
        exit_system,
        exit_user,
        session.journal.bytes,
        receipt_claim.digest().to_string(),
        segments,
        duration_milliseconds,
    );
    build_profile_from_observation_v1(
        request,
        &prover_compute_profile_id,
        &r0vm_before,
        observation,
    )
}

pub fn encode_canonical_profile_v1(
    profile: &StageExecutionProfileV1,
) -> Result<Vec<u8>, ExecutionProfileErrorV1> {
    validate_profile_v1(profile)?;
    serde_json::to_vec(profile).map_err(|error| {
        ExecutionProfileErrorV1::reject(format!("execution-profile JSON encode failed: {error}"))
    })
}

pub fn decode_canonical_profile_v1(
    bytes: &[u8],
) -> Result<StageExecutionProfileV1, ExecutionProfileErrorV1> {
    if bytes.is_empty() || bytes.len() > MAX_PROFILE_BYTES_V1 {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile bytes are empty or oversized",
        ));
    }
    let profile: StageExecutionProfileV1 = serde_json::from_slice(bytes).map_err(|error| {
        ExecutionProfileErrorV1::reject(format!("execution-profile JSON decode failed: {error}"))
    })?;
    validate_profile_v1(&profile)?;
    let canonical = serde_json::to_vec(&profile).map_err(|error| {
        ExecutionProfileErrorV1::reject(format!("execution-profile JSON encode failed: {error}"))
    })?;
    if canonical != bytes {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile JSON is not canonical",
        ));
    }
    Ok(profile)
}

pub fn build_profile_from_observation_v1(
    request: &ExactStageExecutionRequestV1<'_>,
    prover_compute_profile_id: &str,
    r0vm_bytes: &[u8],
    observation: ExecutionObservationV1,
) -> Result<StageExecutionProfileV1, ExecutionProfileErrorV1> {
    validate_compute_profile(prover_compute_profile_id)?;
    if r0vm_bytes.is_empty() {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile r0vm is empty",
        ));
    }
    if observation.exit_system != 0 || observation.exit_user != 0 {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile guest did not halt successfully",
        ));
    }
    if observation.journal_bytes != request.expected_journal_bytes {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile journal differs from exact host recomposition",
        ));
    }
    validate_sha256(
        &observation.receipt_claim_sha256,
        "execution-profile receipt claim",
    )?;
    if observation.receipt_claim_sha256 == ZERO_SHA256 {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile receipt claim is zero",
        ));
    }
    let mut assumption_identities = Vec::with_capacity(request.assumptions.len());
    for (ordinal, assumption) in request.assumptions.iter().enumerate() {
        let receipt_bytes = serde_json::to_vec(assumption.receipt).map_err(|error| {
            ExecutionProfileErrorV1::reject(format!(
                "execution-profile assumption encode failed: {error}"
            ))
        })?;
        let ordinal = u32::try_from(ordinal).map_err(|_| {
            ExecutionProfileErrorV1::reject("execution-profile assumption ordinal exceeds u32")
        })?;
        assumption_identities.push(AssumptionIdentityV1 {
            ordinal,
            receipt: ArtifactIdentityV1::from_bytes(&receipt_bytes)?,
            expected_image_id: Digest::from(assumption.expected_image_id).to_string(),
            journal_sha256: sha256_hex(&assumption.receipt.journal.bytes),
            journal_bytes: u64::try_from(assumption.receipt.journal.bytes.len()).map_err(|_| {
                ExecutionProfileErrorV1::reject("execution-profile assumption journal exceeds u64")
            })?,
        });
    }
    let segment_count = u32::try_from(observation.segments.len()).map_err(|_| {
        ExecutionProfileErrorV1::reject("execution-profile segment count exceeds u32")
    })?;
    let total_user_cycles =
        checked_segment_sum(&observation.segments, |segment| segment.user_cycles)?;
    let total_padded_cycle_capacity = checked_segment_sum(&observation.segments, |segment| {
        segment.padded_cycle_capacity
    })?;
    let mut profile = StageExecutionProfileV1 {
        schema: STAGE_EXECUTION_PROFILE_SCHEMA_V1.to_owned(),
        status: STAGE_EXECUTION_PROFILE_STATUS_V1.to_owned(),
        profile_record_id: ZERO_SHA256.to_owned(),
        stage_id: request.stage_id.to_owned(),
        proof_profile_id: request.proof_profile_id.to_owned(),
        prover_compute_profile_id: prover_compute_profile_id.to_owned(),
        program: ProgramIdentityV1 {
            artifact: ArtifactIdentityV1::from_bytes(request.program_elf)?,
            image_id: Digest::from(request.expected_image_id).to_string(),
        },
        r0vm: ArtifactIdentityV1::from_bytes(r0vm_bytes)?,
        guest_input: ArtifactIdentityV1::from_bytes(request.guest_input_bytes)?,
        assumptions: assumption_identities,
        expected_journal: ArtifactIdentityV1::from_bytes(request.expected_journal_bytes)?,
        observed_journal: ArtifactIdentityV1::from_bytes(&observation.journal_bytes)?,
        receipt_claim_sha256: observation.receipt_claim_sha256,
        segment_limit_po2: ZRPF_SEGMENT_LIMIT_PO2_V1,
        segments: observation.segments,
        segment_count,
        total_user_cycles,
        total_padded_cycle_capacity,
        exit_system: observation.exit_system,
        exit_user: observation.exit_user,
        duration_milliseconds: observation.duration_milliseconds,
        authority: ExecutionAuthorityV1::all_false(),
        non_claims: NON_CLAIMS_V1
            .iter()
            .map(|item| (*item).to_owned())
            .collect(),
    };
    profile.profile_record_id = derive_profile_record_id_v1(&profile)?;
    validate_profile_v1(&profile)?;
    Ok(profile)
}

pub fn validate_profile_v1(
    profile: &StageExecutionProfileV1,
) -> Result<(), ExecutionProfileErrorV1> {
    if profile.schema != STAGE_EXECUTION_PROFILE_SCHEMA_V1
        || profile.status != STAGE_EXECUTION_PROFILE_STATUS_V1
    {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile schema or status mismatch",
        ));
    }
    validate_identifier(&profile.stage_id, "execution-profile stage ID")?;
    if profile.proof_profile_id != ZRPF_PROOF_PROFILE_ID_V1 {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile proof profile is not governed",
        ));
    }
    validate_compute_profile(&profile.prover_compute_profile_id)?;
    validate_artifact(&profile.program.artifact, "execution-profile program")?;
    validate_sha256(&profile.program.image_id, "execution-profile image ID")?;
    validate_artifact(&profile.r0vm, "execution-profile r0vm")?;
    validate_artifact(&profile.guest_input, "execution-profile guest input")?;
    validate_artifact(
        &profile.expected_journal,
        "execution-profile expected journal",
    )?;
    validate_artifact(
        &profile.observed_journal,
        "execution-profile observed journal",
    )?;
    if profile.expected_journal != profile.observed_journal {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile expected and observed journals differ",
        ));
    }
    validate_sha256(
        &profile.receipt_claim_sha256,
        "execution-profile receipt claim",
    )?;
    if profile.receipt_claim_sha256 == ZERO_SHA256 {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile receipt claim is zero",
        ));
    }
    if profile.segment_limit_po2 != ZRPF_SEGMENT_LIMIT_PO2_V1 {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile segment policy mismatch",
        ));
    }
    if profile.segments.is_empty() || profile.segments.len() > MAX_SEGMENTS_V1 {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile segment set is empty or oversized",
        ));
    }
    for (ordinal, segment) in profile.segments.iter().enumerate() {
        let expected_ordinal = u32::try_from(ordinal).map_err(|_| {
            ExecutionProfileErrorV1::reject("execution-profile segment ordinal exceeds u32")
        })?;
        if segment.ordinal != expected_ordinal
            || !(MIN_SEGMENT_PO2_V1..=profile.segment_limit_po2).contains(&segment.po2)
            || segment.padded_cycle_capacity != 1u64.checked_shl(segment.po2).unwrap_or(0)
            || segment.user_cycles > segment.padded_cycle_capacity
        {
            return Err(ExecutionProfileErrorV1::reject(
                "execution-profile segment row is inconsistent",
            ));
        }
    }
    let expected_segment_count = u32::try_from(profile.segments.len()).map_err(|_| {
        ExecutionProfileErrorV1::reject("execution-profile segment count exceeds u32")
    })?;
    if profile.segment_count != expected_segment_count
        || profile.total_user_cycles
            != checked_segment_sum(&profile.segments, |segment| segment.user_cycles)?
        || profile.total_padded_cycle_capacity
            != checked_segment_sum(&profile.segments, |segment| segment.padded_cycle_capacity)?
    {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile aggregate segment facts mismatch",
        ));
    }
    for (ordinal, assumption) in profile.assumptions.iter().enumerate() {
        let expected_ordinal = u32::try_from(ordinal).map_err(|_| {
            ExecutionProfileErrorV1::reject("execution-profile assumption ordinal exceeds u32")
        })?;
        if assumption.ordinal != expected_ordinal {
            return Err(ExecutionProfileErrorV1::reject(
                "execution-profile assumption ordering mismatch",
            ));
        }
        validate_artifact(&assumption.receipt, "execution-profile assumption receipt")?;
        validate_sha256(
            &assumption.expected_image_id,
            "execution-profile assumption image ID",
        )?;
        validate_sha256(
            &assumption.journal_sha256,
            "execution-profile assumption journal",
        )?;
        if assumption.journal_bytes == 0 {
            return Err(ExecutionProfileErrorV1::reject(
                "execution-profile assumption journal is empty",
            ));
        }
    }
    if profile.exit_system != 0 || profile.exit_user != 0 {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile exit status is not successful",
        ));
    }
    if !profile.authority.is_all_false() {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile authority must remain false",
        ));
    }
    let expected_non_claims = NON_CLAIMS_V1
        .iter()
        .map(|item| (*item).to_owned())
        .collect::<Vec<_>>();
    if profile.non_claims != expected_non_claims {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile non-claims mismatch",
        ));
    }
    if profile.profile_record_id != derive_profile_record_id_v1(profile)? {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile record ID mismatch",
        ));
    }
    Ok(())
}

fn derive_profile_record_id_v1(
    profile: &StageExecutionProfileV1,
) -> Result<String, ExecutionProfileErrorV1> {
    let mut candidate = profile.clone();
    candidate.profile_record_id = ZERO_SHA256.to_owned();
    let payload = serde_json::to_vec(&candidate).map_err(|error| {
        ExecutionProfileErrorV1::reject(format!(
            "execution-profile record-ID encode failed: {error}"
        ))
    })?;
    let mut hasher = Sha256::new();
    hasher.update(RECORD_ID_DOMAIN_V1);
    hasher.update(
        u64::try_from(payload.len())
            .map_err(|_| ExecutionProfileErrorV1::reject("profile payload exceeds u64"))?
            .to_be_bytes(),
    );
    hasher.update(payload);
    Ok(hex::encode(hasher.finalize()))
}

fn governed_compute_profile_from_environment() -> Result<String, ExecutionProfileErrorV1> {
    let prover = env::var("RISC0_PROVER").unwrap_or_default();
    let executor = env::var("RISC0_EXECUTOR").unwrap_or_default();
    let cuda = env::var("CUDA_VISIBLE_DEVICES").unwrap_or_default();
    match (prover.as_str(), executor.as_str(), cuda.as_str()) {
        ("ipc", "ipc", "-1") => Ok(CPU_COMPUTE_PROFILE_ID_V1.to_owned()),
        ("ipc", "ipc", "0") => Ok(CUDA_COMPUTE_PROFILE_ID_V1.to_owned()),
        _ => Err(ExecutionProfileErrorV1::reject(
            "execution-profile environment differs from a governed compute profile",
        )),
    }
}

fn validate_compute_profile(value: &str) -> Result<(), ExecutionProfileErrorV1> {
    if !matches!(
        value,
        CPU_COMPUTE_PROFILE_ID_V1 | CUDA_COMPUTE_PROFILE_ID_V1
    ) {
        return Err(ExecutionProfileErrorV1::reject(
            "execution-profile compute profile is not governed",
        ));
    }
    Ok(())
}

fn governed_r0vm_path_from_environment() -> Result<std::path::PathBuf, ExecutionProfileErrorV1> {
    let path = env::var_os("RISC0_SERVER_PATH")
        .map(std::path::PathBuf::from)
        .filter(|path| path.is_absolute())
        .ok_or_else(|| {
            ExecutionProfileErrorV1::reject(
                "RISC0_SERVER_PATH must name an absolute execution-profile r0vm",
            )
        })?;
    Ok(path)
}

fn stable_regular_file_bytes(
    path: &Path,
    maximum_bytes: u64,
    label: &str,
) -> Result<Vec<u8>, ExecutionProfileErrorV1> {
    let path_metadata = fs::symlink_metadata(path).map_err(|error| {
        ExecutionProfileErrorV1::reject(format!("{label} metadata failed: {error}"))
    })?;
    if !path_metadata.is_file()
        || path_metadata.file_type().is_symlink()
        || path_metadata.len() == 0
        || path_metadata.len() > maximum_bytes
        || path_metadata.mode() & 0o111 == 0
    {
        return Err(ExecutionProfileErrorV1::reject(format!(
            "{label} is not a bounded executable regular file"
        )));
    }
    let mut file = fs::File::open(path).map_err(|error| {
        ExecutionProfileErrorV1::reject(format!("{label} open failed: {error}"))
    })?;
    let opened_metadata = file.metadata().map_err(|error| {
        ExecutionProfileErrorV1::reject(format!("{label} opened metadata failed: {error}"))
    })?;
    if !same_file_version(&path_metadata, &opened_metadata) {
        return Err(ExecutionProfileErrorV1::reject(format!(
            "{label} path changed while opened"
        )));
    }
    let read_limit = maximum_bytes
        .checked_add(1)
        .ok_or_else(|| ExecutionProfileErrorV1::reject(format!("{label} read limit overflow")))?;
    let mut bytes = Vec::new();
    (&mut file)
        .take(read_limit)
        .read_to_end(&mut bytes)
        .map_err(|error| {
            ExecutionProfileErrorV1::reject(format!("{label} read failed: {error}"))
        })?;
    let final_metadata = file.metadata().map_err(|error| {
        ExecutionProfileErrorV1::reject(format!("{label} final metadata failed: {error}"))
    })?;
    if !same_file_version(&opened_metadata, &final_metadata)
        || u64::try_from(bytes.len()).ok() != Some(opened_metadata.len())
        || bytes.is_empty()
        || u64::try_from(bytes.len()).map_or(true, |size| size > maximum_bytes)
    {
        return Err(ExecutionProfileErrorV1::reject(format!(
            "{label} changed while read"
        )));
    }
    Ok(bytes)
}

fn same_file_version(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file()
        && right.is_file()
        && left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.mode() == right.mode()
        && left.len() == right.len()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

fn exit_pair(exit_code: ExitCode) -> Result<(u32, u32), ExecutionProfileErrorV1> {
    match exit_code {
        ExitCode::Halted(0) => Ok((0, 0)),
        _ => Err(ExecutionProfileErrorV1::reject(
            "execution-profile guest did not halt with code zero",
        )),
    }
}

fn checked_segment_sum(
    segments: &[SegmentMeasurementV1],
    project: impl Fn(&SegmentMeasurementV1) -> u64,
) -> Result<u64, ExecutionProfileErrorV1> {
    segments.iter().try_fold(0u64, |total, segment| {
        total.checked_add(project(segment)).ok_or_else(|| {
            ExecutionProfileErrorV1::reject("execution-profile segment sum overflow")
        })
    })
}

fn validate_identifier(value: &str, label: &str) -> Result<(), ExecutionProfileErrorV1> {
    if value.is_empty()
        || value.len() > 128
        || !value.bytes().all(|byte| {
            byte.is_ascii_lowercase()
                || byte.is_ascii_digit()
                || matches!(byte, b'_' | b'-' | b'.' | b'/')
        })
    {
        return Err(ExecutionProfileErrorV1::reject(format!(
            "{label} is not a bounded canonical identifier"
        )));
    }
    Ok(())
}

fn validate_artifact(
    artifact: &ArtifactIdentityV1,
    label: &str,
) -> Result<(), ExecutionProfileErrorV1> {
    validate_sha256(&artifact.sha256, label)?;
    if artifact.size_bytes == 0 {
        return Err(ExecutionProfileErrorV1::reject(format!("{label} is empty")));
    }
    Ok(())
}

fn validate_sha256(value: &str, label: &str) -> Result<(), ExecutionProfileErrorV1> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(ExecutionProfileErrorV1::reject(format!(
            "{label} is not lowercase SHA-256"
        )));
    }
    Ok(())
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn fixture_request<'a>(
        elf: &'a [u8],
        input: &'a [u8],
        journal: &'a [u8],
    ) -> ExactStageExecutionRequestV1<'a> {
        ExactStageExecutionRequestV1::new(
            "spot_v7_profile_fixture",
            ZRPF_PROOF_PROFILE_ID_V1,
            elf,
            [
                0x1234_5678,
                0x90ab_cdef,
                0x2345_6789,
                0xabcd_ef01,
                0x3456_7890,
                0xbcde_f012,
                0x4567_8901,
                0xcdef_0123,
            ],
            input,
            &[],
            journal,
        )
        .expect("fixture request")
    }

    fn fixture_elf() -> Vec<u8> {
        let mut bytes = Vec::with_capacity(603);
        for ordinal in 0..603u16 {
            bytes.push(((ordinal * 73 + 19) % 251) as u8);
        }
        bytes[0] = 0x7f;
        bytes[1] = b'E';
        bytes[2] = b'L';
        bytes[3] = b'F';
        bytes[602] = 0xa7;
        assert_ne!(bytes, bytes.iter().copied().rev().collect::<Vec<_>>());
        bytes
    }

    fn fixture_profile() -> StageExecutionProfileV1 {
        let elf = fixture_elf();
        let input = b"position-distinct-input-603-active-witness";
        let journal = b"position-distinct-journal-947-active-witness";
        let request = fixture_request(&elf, input, journal);
        let segments = vec![
            SegmentMeasurementV1::new(0, 18, 123_457).expect("segment zero"),
            SegmentMeasurementV1::new(1, 19, 234_569).expect("segment one"),
            SegmentMeasurementV1::new(2, 20, 345_679).expect("segment two"),
        ];
        build_profile_from_observation_v1(
            &request,
            CPU_COMPUTE_PROFILE_ID_V1,
            b"position-distinct-r0vm-fixture",
            ExecutionObservationV1::new(
                0,
                0,
                journal.to_vec(),
                "1234567890abcdef1234567890abcdef1234567890abcdef1234567890abcdef".to_owned(),
                segments,
                117,
            ),
        )
        .expect("fixture profile")
    }

    fn reanchor(profile: &mut StageExecutionProfileV1) {
        profile.profile_record_id = derive_profile_record_id_v1(profile).expect("record ID");
    }

    #[test]
    fn exact_profile_round_trips_canonical_bytes() {
        let profile = fixture_profile();
        let bytes = encode_canonical_profile_v1(&profile).expect("encode profile");
        let decoded = decode_canonical_profile_v1(&bytes).expect("decode profile");
        assert_eq!(decoded, profile);
        assert_eq!(profile.segment_count, 3);
        assert_eq!(profile.total_user_cycles, 703_705);
        assert_eq!(profile.total_padded_cycle_capacity, 1_835_008);
        assert!(profile.authority.is_all_false());
    }

    #[test]
    fn swapped_position_distinct_segments_reject_after_reanchoring() {
        let mut profile = fixture_profile();
        profile.segments.swap(0, 2);
        reanchor(&mut profile);
        let error = validate_profile_v1(&profile).expect_err("swapped rows must reject");
        assert!(error.to_string().contains("segment row"));
    }

    #[test]
    fn changed_segment_totals_reject_after_reanchoring() {
        let mut profile = fixture_profile();
        profile.total_user_cycles += 1;
        reanchor(&mut profile);
        let error = validate_profile_v1(&profile).expect_err("wrong total must reject");
        assert!(error.to_string().contains("aggregate segment facts"));
    }

    #[test]
    fn authority_promotion_rejects_after_reanchoring() {
        let mut profile = fixture_profile();
        profile.authority.proof_generated = true;
        reanchor(&mut profile);
        let error = validate_profile_v1(&profile).expect_err("authority must reject");
        assert!(error.to_string().contains("authority"));
    }

    #[test]
    fn proof_and_compute_profile_substitution_reject_after_reanchoring() {
        let mut profile = fixture_profile();
        profile.proof_profile_id = "risc0_succinct_future".to_owned();
        reanchor(&mut profile);
        let error = validate_profile_v1(&profile).expect_err("proof profile must reject");
        assert!(error.to_string().contains("proof profile"));

        let mut profile = fixture_profile();
        profile.prover_compute_profile_id = "risc0_ipc_unbounded".to_owned();
        reanchor(&mut profile);
        let error = validate_profile_v1(&profile).expect_err("compute profile must reject");
        assert!(error.to_string().contains("compute profile"));
    }

    #[test]
    fn journal_substitution_rejects_after_reanchoring() {
        let mut profile = fixture_profile();
        profile.observed_journal.sha256 =
            "abcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcdefabcd".to_owned();
        reanchor(&mut profile);
        let error = validate_profile_v1(&profile).expect_err("journal must reject");
        assert!(error.to_string().contains("journals differ"));
    }

    #[test]
    fn noncanonical_json_and_unknown_fields_reject() {
        let profile = fixture_profile();
        let canonical = encode_canonical_profile_v1(&profile).expect("encode profile");
        let mut spaced = b" ".to_vec();
        spaced.extend_from_slice(&canonical);
        assert!(decode_canonical_profile_v1(&spaced)
            .expect_err("whitespace must reject")
            .to_string()
            .contains("not canonical"));

        let mut value: serde_json::Value = serde_json::from_slice(&canonical).expect("JSON value");
        value
            .as_object_mut()
            .expect("profile object")
            .insert("unknown".to_owned(), serde_json::Value::Bool(false));
        let unknown = serde_json::to_vec(&value).expect("unknown-field JSON");
        assert!(decode_canonical_profile_v1(&unknown)
            .expect_err("unknown field must reject")
            .to_string()
            .contains("unknown field"));
    }

    #[test]
    fn integer_for_boolean_and_float_for_integer_reject() {
        let profile = fixture_profile();
        let canonical = encode_canonical_profile_v1(&profile).expect("encode profile");
        let mut value: serde_json::Value = serde_json::from_slice(&canonical).expect("JSON value");
        value["authority"]["proof_generated"] = serde_json::Value::from(0);
        assert!(decode_canonical_profile_v1(
            &serde_json::to_vec(&value).expect("integer Boolean JSON")
        )
        .expect_err("integer Boolean must reject")
        .to_string()
        .contains("invalid type"));

        let mut value: serde_json::Value = serde_json::from_slice(&canonical).expect("JSON value");
        value["duration_milliseconds"] = serde_json::json!(1.5);
        assert!(decode_canonical_profile_v1(
            &serde_json::to_vec(&value).expect("float integer JSON")
        )
        .expect_err("float integer must reject")
        .to_string()
        .contains("invalid type"));
    }
}
