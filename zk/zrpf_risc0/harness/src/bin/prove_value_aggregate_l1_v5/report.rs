use std::io::Write;

use risc0_zkvm::Digest;
use serde::Serialize;
use zenodex_zrpf_protocol_v3::encode_value_aggregate_proposal_v5;
use zenodex_zrpf_risc0_verifier::VerifiedValueAggregateReceiptV5;

use super::artifact_io::sha256_hex;
use super::cli::Mode;

const MAX_REPORT_BYTES: usize = 16 * 1_024;
const NONCLAIMS: [&str; 5] = [
    "the expected profile and program manifest are caller-supplied outer metadata, not fields of the V5 guest journal",
    "a consuming certificate or release manifest must commit certificate_identity_binding before the outer identity carries authority",
    "the V5 proposal authenticates bounded child composition and grants no settlement authority",
    "operational commitments do not prove data availability, schedule, message, or carry semantics",
    "no durable atomic ZenoLedger admission or production authority is established",
];

#[derive(Serialize)]
struct ValueAggregateProofReport<'a> {
    schema: &'static str,
    status: &'static str,
    mode: &'static str,
    ok: bool,
    child_count: usize,
    child_receipts_authenticated: usize,
    child_image_id: String,
    parent_image_id: String,
    expected_aggregate_level: u8,
    proposal_aggregate_level: u8,
    proposal_bytes: usize,
    proposal_sha256: String,
    proposal_commitment: String,
    receipt_bytes: usize,
    receipt_sha256: String,
    receipt_profile_id: &'static str,
    receipt_written: bool,
    exact_expected_proposal_bound: bool,
    verified_program_id: String,
    bound_proof_profile_id: String,
    bound_program_manifest_root: String,
    claim_binding: String,
    certificate_identity_binding: String,
    settlement_authority: bool,
    release_authority: bool,
    production_authority: bool,
    nonclaims: &'a [&'static str],
}

pub(super) fn write_report(
    mode: Mode,
    verified: &VerifiedValueAggregateReceiptV5,
    child_count: usize,
    child_image_id: [u32; 8],
    parent_image_id: [u32; 8],
    receipt_bytes: &[u8],
    receipt_written: bool,
) -> Result<(), String> {
    let proposal_bytes = encode_value_aggregate_proposal_v5(verified.proposal())
        .map_err(|error| format!("report proposal encode: {error}"))?;
    let identity = verified.bound_identity();
    let report = ValueAggregateProofReport {
        schema: "zenodex/zrpf_value_aggregate_l1_v5_proof_report/v1",
        status: "bounded_v5_value_aggregate_l1_succinct_receipt_verified",
        mode: mode.as_str(),
        ok: true,
        child_count,
        child_receipts_authenticated: child_count,
        child_image_id: Digest::from(child_image_id).to_string(),
        parent_image_id: Digest::from(parent_image_id).to_string(),
        expected_aggregate_level: identity.aggregate_level().get(),
        proposal_aggregate_level: verified.proposal().aggregate_level(),
        proposal_bytes: proposal_bytes.len(),
        proposal_sha256: sha256_hex(&proposal_bytes),
        proposal_commitment: hex::encode(verified.proposal().proposal_commitment().as_bytes()),
        receipt_bytes: receipt_bytes.len(),
        receipt_sha256: sha256_hex(receipt_bytes),
        receipt_profile_id: verified.receipt_profile().profile_id(),
        receipt_written,
        exact_expected_proposal_bound: true,
        verified_program_id: hex::encode(verified.verified_program_id().as_bytes()),
        bound_proof_profile_id: hex::encode(identity.proof_profile_id().as_bytes()),
        bound_program_manifest_root: hex::encode(identity.program_manifest_root().as_bytes()),
        claim_binding: hex::encode(verified.claim_binding().as_bytes()),
        certificate_identity_binding: hex::encode(
            verified.certificate_identity_binding().as_bytes(),
        ),
        settlement_authority: false,
        release_authority: false,
        production_authority: false,
        nonclaims: &NONCLAIMS,
    };
    let bytes = serde_json::to_vec(&report)
        .map_err(|error| format!("aggregate proof report encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_REPORT_BYTES {
        return Err("aggregate proof report exceeds canonical bound".to_owned());
    }
    let mut output = std::io::stdout().lock();
    output
        .write_all(&bytes)
        .and_then(|()| output.write_all(b"\n"))
        .map_err(|error| format!("write aggregate proof report: {error}"))
}
