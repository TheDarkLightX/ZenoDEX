use std::io::Write;

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine as _};
use risc0_zkvm::Digest;
use serde::Serialize;
use sha2::Digest as _;

use super::{
    artifact_io::{canonical_receipt_bytes, sha256_hex, PersistedBundle},
    cli::Mode,
    ProgramSpec, ProvedReceipts,
};

const MAX_REPORT_BYTES: usize = 32 * 1_024;
const MAX_BUNDLE_BYTES: usize = 32 * 1_024 * 1_024;
const NONCLAIMS: [&str; 14] = [
    "retained program source-to-binary provenance is not re-established by this harness",
    "the retained programs are not rebuilt by this harness",
    "the SDK-selected IPC transport name does not authenticate r0vm locality or executable identity",
    "RISC0_SERVER_PATH and SDK rzup or PATH resolution remain ambient",
    "Cargo can rebuild optional method crates before the runtime no-default-feature check",
    "create-new bundle persistence is not crash-atomic release publication",
    "the caller-controlled output directory may change after the final path-identity check",
    "cross-host or path-independent reproducibility is not established",
    "the V5 proposal proves bounded composition and no settlement semantics",
    "data availability, schedule, message, carry, and source finality remain unverified",
    "durable atomic ZenoLedger admission is not implemented by this harness",
    "release authority is false",
    "settlement authority is false",
    "production authority is false",
];

#[derive(Serialize)]
struct ReceiptBundleClaims {
    retained_program_identity_rechecked: bool,
    child_receipt_authenticated: bool,
    level_one_receipt_generated_and_verified: bool,
    level_two_receipt_generated_and_verified: bool,
    retained_program_source_to_binary_verified: bool,
    prover_binary_identity_verified: bool,
    cross_host_reproducible_build: bool,
    settlement_semantics_verified: bool,
    durable_atomic_admission_verified: bool,
    release_authority: bool,
    settlement_authority: bool,
    production_authority: bool,
}

#[derive(Serialize)]
struct ReceiptBundle<'a> {
    schema: &'static str,
    level_one_receipt_base64: String,
    level_one_receipt_bytes: usize,
    level_one_receipt_sha256: String,
    level_two_receipt_base64: String,
    level_two_receipt_bytes: usize,
    level_two_receipt_sha256: String,
    claims: ReceiptBundleClaims,
    nonclaims: &'a [&'static str],
}

#[derive(Serialize)]
struct HarnessReport<'a> {
    schema: &'static str,
    status: &'static str,
    mode: &'static str,
    ok: bool,
    build_record_sha256: &'static str,
    child_image_id: String,
    level_one_program_bytes: usize,
    level_one_program_sha256: String,
    level_one_image_id: String,
    level_two_program_bytes: usize,
    level_two_program_sha256: String,
    level_two_image_id: String,
    level_one_receipt_sha256: Option<String>,
    level_two_receipt_sha256: Option<String>,
    persisted_bundle_bytes: Option<usize>,
    persisted_bundle_sha256: Option<String>,
    persisted_bundle_final_path_identity_checked: bool,
    proof_generation_executed: bool,
    retained_program_source_to_binary_verified: bool,
    prover_binary_identity_verified: bool,
    cross_host_reproducible_build: bool,
    settlement_semantics_verified: bool,
    durable_atomic_admission_verified: bool,
    release_authority: bool,
    settlement_authority: bool,
    production_authority: bool,
    nonclaims: &'a [&'static str],
}

pub(super) struct EncodedReceiptBundle {
    bytes: Vec<u8>,
    level_one_receipt_sha256: String,
    level_two_receipt_sha256: String,
    sha256: [u8; 32],
}

impl EncodedReceiptBundle {
    pub(super) fn bytes(&self) -> &[u8] {
        &self.bytes
    }

    pub(super) fn level_one_receipt_sha256(&self) -> &str {
        &self.level_one_receipt_sha256
    }

    pub(super) fn level_two_receipt_sha256(&self) -> &str {
        &self.level_two_receipt_sha256
    }

    pub(super) const fn sha256(&self) -> [u8; 32] {
        self.sha256
    }
}

pub(super) fn encode_receipt_bundle(
    proved: &ProvedReceipts,
) -> Result<EncodedReceiptBundle, String> {
    if proved.level_one.proposal().aggregate_level() != 1
        || proved.level_two.proposal().aggregate_level() != 2
    {
        return Err("sealed V5 receipt pair has the wrong aggregate levels".to_owned());
    }
    let level_one_receipt = canonical_receipt_bytes(proved.level_one.receipt())?;
    let level_two_receipt = canonical_receipt_bytes(proved.level_two.receipt())?;
    let level_one_receipt_sha256 = sha256_hex(&level_one_receipt);
    let level_two_receipt_sha256 = sha256_hex(&level_two_receipt);
    let bytes = serde_json::to_vec(&ReceiptBundle {
        schema: "zenodex/zrpf_retained_value_aggregate_v5_receipt_bundle/v1",
        level_one_receipt_base64: BASE64_STANDARD.encode(&level_one_receipt),
        level_one_receipt_bytes: level_one_receipt.len(),
        level_one_receipt_sha256: level_one_receipt_sha256.clone(),
        level_two_receipt_base64: BASE64_STANDARD.encode(&level_two_receipt),
        level_two_receipt_bytes: level_two_receipt.len(),
        level_two_receipt_sha256: level_two_receipt_sha256.clone(),
        claims: ReceiptBundleClaims {
            retained_program_identity_rechecked: true,
            child_receipt_authenticated: true,
            level_one_receipt_generated_and_verified: true,
            level_two_receipt_generated_and_verified: true,
            retained_program_source_to_binary_verified: false,
            prover_binary_identity_verified: false,
            cross_host_reproducible_build: false,
            settlement_semantics_verified: false,
            durable_atomic_admission_verified: false,
            release_authority: false,
            settlement_authority: false,
            production_authority: false,
        },
        nonclaims: &NONCLAIMS,
    })
    .map_err(|error| format!("encode V5 receipt bundle: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_BUNDLE_BYTES {
        return Err("encoded V5 receipt bundle exceeds governed bound".to_owned());
    }
    Ok(EncodedReceiptBundle {
        sha256: sha2::Sha256::digest(&bytes).into(),
        bytes,
        level_one_receipt_sha256,
        level_two_receipt_sha256,
    })
}

pub(super) struct ReportInput<'a> {
    pub(super) mode: Mode,
    pub(super) build_record_sha256: &'static str,
    pub(super) child: &'a ProgramSpec,
    pub(super) level_one: &'a ProgramSpec,
    pub(super) level_two: &'a ProgramSpec,
    pub(super) bundle: Option<&'a EncodedReceiptBundle>,
    pub(super) persisted: Option<&'a PersistedBundle>,
}

pub(super) fn write_report(input: ReportInput<'_>) -> Result<(), String> {
    let proof_generation_executed = match (input.mode, input.bundle, input.persisted) {
        (Mode::Preflight, None, None) => false,
        (Mode::Prove, Some(bundle), Some(persisted)) => {
            if bundle.bytes().len() != persisted.byte_length()
                || bundle.sha256() != persisted.sha256()
            {
                return Err("reported V5 bundle differs from persisted same-fd bytes".to_owned());
            }
            true
        }
        _ => return Err("V5 report evidence does not match execution mode".to_owned()),
    };
    let status = if proof_generation_executed {
        "retained_value_aggregate_v5_l1_l2_succinct_receipts_verified"
    } else {
        "retained_value_aggregate_v5_preflight_verified"
    };
    let report = HarnessReport {
        schema: "zenodex/zrpf_retained_value_aggregate_v5_harness_report/v1",
        status,
        mode: input.mode.as_str(),
        ok: true,
        build_record_sha256: input.build_record_sha256,
        child_image_id: Digest::from(input.child.image_id).to_string(),
        level_one_program_bytes: input.level_one.size_bytes,
        level_one_program_sha256: hex::encode(input.level_one.sha256),
        level_one_image_id: Digest::from(input.level_one.image_id).to_string(),
        level_two_program_bytes: input.level_two.size_bytes,
        level_two_program_sha256: hex::encode(input.level_two.sha256),
        level_two_image_id: Digest::from(input.level_two.image_id).to_string(),
        level_one_receipt_sha256: input
            .bundle
            .map(|bundle| bundle.level_one_receipt_sha256().to_owned()),
        level_two_receipt_sha256: input
            .bundle
            .map(|bundle| bundle.level_two_receipt_sha256().to_owned()),
        persisted_bundle_bytes: input.persisted.map(PersistedBundle::byte_length),
        persisted_bundle_sha256: input
            .persisted
            .map(|persisted| hex::encode(persisted.sha256())),
        persisted_bundle_final_path_identity_checked: input.persisted.is_some(),
        proof_generation_executed,
        retained_program_source_to_binary_verified: false,
        prover_binary_identity_verified: false,
        cross_host_reproducible_build: false,
        settlement_semantics_verified: false,
        durable_atomic_admission_verified: false,
        release_authority: false,
        settlement_authority: false,
        production_authority: false,
        nonclaims: &NONCLAIMS,
    };
    let bytes = serde_json::to_vec(&report)
        .map_err(|error| format!("encode V5 harness report: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_REPORT_BYTES {
        return Err("V5 harness report exceeds canonical bound".to_owned());
    }
    let mut output = std::io::stdout().lock();
    output
        .write_all(&bytes)
        .and_then(|()| output.write_all(b"\n"))
        .map_err(|error| format!("write V5 harness report: {error}"))
}
