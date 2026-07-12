use std::io::Write;

use risc0_zkvm::Digest;
use serde::Serialize;
use zenodex_zrpf_protocol_v3::encode_value_aggregate_proposal_v5;
use zenodex_zrpf_risc0_value_aggregate_l2_policy::pinned_value_aggregate_level_one_identity_v5;
use zenodex_zrpf_risc0_value_aggregate_root_policy::PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5;
use zenodex_zrpf_risc0_verifier::VerifiedValueAggregateReceiptV5;

use super::artifact_io::sha256_hex;
use super::cli::Mode;

const MAX_REPORT_BYTES: usize = 16 * 1_024;
const NONCLAIMS: [&str; 6] = [
    "the pinned L1 and L2 identities are source-governed experimental policy and carry no release authority",
    "the V5 proposal authenticates bounded child composition and grants no ledger or settlement authority",
    "operational commitments do not prove data availability, schedule, message, carry, or external finality semantics",
    "no durable atomic ZenoLedger admission or economic effect application is established",
    "this local report does not establish source-built or cross-host reproducible proof-generation evidence",
    "witness privacy and zero-knowledge privacy are outside this receipt profile claim",
];

#[derive(Serialize)]
struct ValueAggregateRootProofReport<'a> {
    schema: &'static str,
    status: &'static str,
    mode: &'static str,
    ok: bool,
    child_count: usize,
    child_receipts_authenticated: usize,
    child_image_id: String,
    child_proof_profile_id: String,
    child_program_manifest_root: String,
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
    bound_root_proof_profile_id: String,
    bound_root_program_manifest_root: String,
    claim_binding: String,
    certificate_identity_binding: String,
    data_availability_verified: bool,
    ledger_admission_authority: bool,
    settlement_authority: bool,
    release_authority: bool,
    production_authority: bool,
    nonclaims: &'a [&'static str],
}

pub(super) fn write_report(
    mode: Mode,
    verified: &VerifiedValueAggregateReceiptV5,
    child_count: usize,
    receipt_bytes: &[u8],
    receipt_written: bool,
) -> Result<(), String> {
    let proposal_bytes = encode_value_aggregate_proposal_v5(verified.proposal())
        .map_err(|error| format!("report L2 proposal encode: {error}"))?;
    let root_identity = verified.bound_identity();
    let child_identity = pinned_value_aggregate_level_one_identity_v5()
        .map_err(|error| format!("report governed L1 identity: {error}"))?;
    let report = ValueAggregateRootProofReport {
        schema: "zenodex/zrpf_value_aggregate_l2_v5_proof_report/v1",
        status: "bounded_v5_value_aggregate_l2_succinct_receipt_verified",
        mode: mode.as_str(),
        ok: true,
        child_count,
        child_receipts_authenticated: child_count,
        child_image_id: Digest::from(child_identity.expected_image_id()).to_string(),
        child_proof_profile_id: hex::encode(child_identity.expected_profile_id().as_bytes()),
        child_program_manifest_root: hex::encode(
            child_identity.expected_manifest_root().as_bytes(),
        ),
        parent_image_id: Digest::from(PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5).to_string(),
        expected_aggregate_level: root_identity.aggregate_level().get(),
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
        bound_root_proof_profile_id: hex::encode(root_identity.proof_profile_id().as_bytes()),
        bound_root_program_manifest_root: hex::encode(
            root_identity.program_manifest_root().as_bytes(),
        ),
        claim_binding: hex::encode(verified.claim_binding().as_bytes()),
        certificate_identity_binding: hex::encode(
            verified.certificate_identity_binding().as_bytes(),
        ),
        data_availability_verified: false,
        ledger_admission_authority: false,
        settlement_authority: false,
        release_authority: false,
        production_authority: false,
        nonclaims: &NONCLAIMS,
    };
    let bytes = serde_json::to_vec(&report)
        .map_err(|error| format!("L2 root proof report encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_REPORT_BYTES {
        return Err("L2 root proof report exceeds canonical bound".to_owned());
    }
    let mut output = std::io::stdout().lock();
    output
        .write_all(&bytes)
        .and_then(|()| output.write_all(b"\n"))
        .map_err(|error| format!("write L2 root proof report: {error}"))
}
