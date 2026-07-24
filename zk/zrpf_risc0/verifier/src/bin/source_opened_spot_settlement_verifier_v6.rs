//! Strict external verifier for one source-opened ordinary-Spot V6 settlement.
//!
//! This binary authenticates one canonical Succinct receipt and recomposes its
//! journal from the exact guest input. Its output remains a proof-to-admission
//! projection. It grants no durable ledger, release, or production authority.

use std::io::{self, Read, Write};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_settlement_effect_plan_v2, AssetEffectKindV2, SettlementEffectPlanV2,
    SettlementSemanticRootV1,
};
use zenodex_zrpf_risc0_spot_settlement_root_policy_v6::pinned_source_opened_spot_settlement_identity_v6;
use zenodex_zrpf_risc0_spot_settlement_v6_shared::MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3;
use zenodex_zrpf_risc0_verifier::{
    VerifiedSourceOpenedSpotSettlementAdmissionV6, MAX_CANONICAL_RECEIPT_BYTES_V3,
};

const REQUEST_SCHEMA: &str = "zenodex.source_opened_spot_settlement_verifier_v6.request.v1";
const RESPONSE_SCHEMA: &str = "zenodex.source_opened_spot_settlement_verifier_v6.response.v1";
const ERROR_SCHEMA: &str = "zenodex.source_opened_spot_settlement_verifier_v6.error.v1";
const MAX_REQUEST_BYTES: usize = 40 * 1_024 * 1_024;
const MAX_RESPONSE_BYTES: usize = 16 * 1_024 * 1_024;
const EXPECTED_ACTION_COUNT: usize = 1;
const EXPECTED_CELL_WRITE_COUNT: usize = 1;
const EXPECTED_ORDINARY_ASSET_ROW_COUNT: usize = 2;

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct VerifyRequestV1 {
    schema: String,
    receipt_hex: String,
    guest_input_hex: String,
}

#[derive(Debug, Serialize)]
struct VerifyResponseV1 {
    ok: bool,
    schema: &'static str,
    verified_settlement_admission: VerifiedSettlementAdmissionV1,
}

#[derive(Debug, Serialize)]
struct VerifiedSettlementAdmissionV1 {
    receipt_bytes: usize,
    receipt_sha256: String,
    guest_input_bytes: usize,
    guest_input_sha256: String,
    admission_journal_bytes: usize,
    admission_journal_hex: String,
    admission_journal_sha256: String,
    certificate_bytes: usize,
    certificate_hex: String,
    certificate_sha256: String,
    effect_plan_bytes: usize,
    effect_plan_hex: String,
    effect_plan_sha256: String,
    governed_settlement_program_id: String,
    governed_settlement_profile_id: String,
    governed_settlement_manifest_root: String,
    settlement_claim_binding: String,
    receipt_security_profile: ReceiptSecurityProfileV1,
    admission_projection: AdmissionProjectionV1,
    execution_projection: ExecutionProjectionV1,
}

#[derive(Debug, Serialize)]
struct ReceiptSecurityProfileV1 {
    profile_id: String,
    receipt_kind: String,
    verifier_parameters: String,
    hashfn: String,
    control_id: String,
}

#[derive(Debug, Serialize)]
struct AdmissionProjectionV1 {
    journal_version: u16,
    certificate_version: u16,
    effect_plan_version: u16,
    application_id: String,
    chain_or_domain_id: String,
    epoch_id: u64,
    semantic_profile_id: String,
    semantic_journal_hash: String,
    semantic_claim_binding: String,
    proof_tree_root: String,
    semantic_root_kind: &'static str,
    semantic_root: String,
    dependency_manifest_root: String,
    public_policy_hash: String,
    economic_action_batch_commitment: String,
    settlement_effect_plan_commitment: String,
    economic_action_ids_root: String,
    action_authorization_bindings_root: String,
    authorization_grant_spends_root: String,
    consumed_object_ids_root: String,
    action_count: u32,
    consumed_object_count: u32,
    pre_state_root: String,
    post_state_root: String,
    cell_writes_root: String,
    asset_effects_root: String,
    messages_root: String,
    carries_root: String,
    rewards_root: String,
    data_availability_certificate_root: String,
    schedule_certificate_root: String,
    carry_continuity_certificate_root: String,
    settlement_certificate_id: String,
    certificate_commitment: String,
}

#[derive(Debug, Serialize)]
struct ExecutionProjectionV1 {
    application_id: String,
    chain_or_domain_id: String,
    epoch_id: u64,
    pre_state_root: String,
    post_state_root: String,
    action: ActionProjectionV1,
    cell_write: CellWriteProjectionV1,
    ordinary_asset_rows: Vec<OrdinaryAssetProjectionV1>,
}

#[derive(Debug, Serialize)]
struct ActionProjectionV1 {
    action_id: String,
    action_type_id: String,
    authorization_subject_id: String,
    authorization_scope_id: String,
    authorization_nonce: u64,
    authorization_grant_id: String,
    action_authorization_binding: String,
    authorization_grant_spend_nullifier: String,
    valid_from_epoch: u64,
    valid_through_epoch: u64,
    pre_state_root: String,
    action_semantics_hash: String,
    effect_commitment: String,
    consumed_object_ids: Vec<String>,
}

#[derive(Debug, Serialize)]
struct CellWriteProjectionV1 {
    economic_action_id: String,
    cell_key: String,
    pre_value_hash: String,
    post_value_hash: String,
}

#[derive(Debug, Serialize)]
struct OrdinaryAssetProjectionV1 {
    economic_action_id: String,
    asset_id: String,
    debit_atoms: String,
    credit_atoms: String,
}

#[derive(Debug, Serialize)]
struct ErrorResponseV1 {
    ok: bool,
    schema: &'static str,
    error_code: &'static str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct CliError {
    code: &'static str,
}

impl CliError {
    const fn new(code: &'static str) -> Self {
        Self { code }
    }
}

fn main() {
    match run() {
        Ok(response) => {
            if write_response(&response).is_err() {
                emit_error_and_exit(CliError::new("response_write_failed"));
            }
        }
        Err(error) => emit_error_and_exit(error),
    }
}

fn run() -> Result<VerifyResponseV1, CliError> {
    let request_bytes = read_bounded_stdin()?;
    let request = decode_exact_request(&request_bytes)?;
    let receipt_bytes = decode_exact_lower_hex(
        &request.receipt_hex,
        MAX_CANONICAL_RECEIPT_BYTES_V3,
        "receipt_hex_empty",
        "receipt_hex_too_large",
        "receipt_hex_invalid",
    )?;
    let guest_input_bytes = decode_exact_lower_hex(
        &request.guest_input_hex,
        MAX_SOURCE_OPENED_SPOT_SETTLEMENT_GUEST_INPUT_BYTES_V3,
        "guest_input_hex_empty",
        "guest_input_hex_too_large",
        "guest_input_hex_invalid",
    )?;

    // This is the sole cryptographic receipt verification call in the CLI.
    let admission =
        VerifiedSourceOpenedSpotSettlementAdmissionV6::verify(&receipt_bytes, &guest_input_bytes)
            .map_err(|error| CliError::new(error.code()))?;
    let projection = project_verified_admission(&receipt_bytes, &admission)?;
    Ok(VerifyResponseV1 {
        ok: true,
        schema: RESPONSE_SCHEMA,
        verified_settlement_admission: projection,
    })
}

fn read_bounded_stdin() -> Result<Vec<u8>, CliError> {
    let maximum_plus_one = MAX_REQUEST_BYTES
        .checked_add(1)
        .ok_or_else(|| CliError::new("request_bound_overflow"))?;
    let limit =
        u64::try_from(maximum_plus_one).map_err(|_| CliError::new("request_bound_overflow"))?;
    let mut bytes = Vec::new();
    io::stdin()
        .lock()
        .take(limit)
        .read_to_end(&mut bytes)
        .map_err(|_| CliError::new("request_read_failed"))?;
    if bytes.is_empty() {
        return Err(CliError::new("request_empty"));
    }
    if bytes.len() > MAX_REQUEST_BYTES {
        return Err(CliError::new("request_too_large"));
    }
    Ok(bytes)
}

fn decode_exact_request(bytes: &[u8]) -> Result<VerifyRequestV1, CliError> {
    let request: VerifyRequestV1 =
        serde_json::from_slice(bytes).map_err(|_| CliError::new("request_json_invalid"))?;
    if request.schema != REQUEST_SCHEMA {
        return Err(CliError::new("request_schema_mismatch"));
    }
    let canonical =
        serde_json::to_vec(&request).map_err(|_| CliError::new("request_json_encode_failed"))?;
    if canonical != bytes {
        return Err(CliError::new("request_json_noncanonical"));
    }
    Ok(request)
}

fn decode_exact_lower_hex(
    value: &str,
    maximum_decoded_bytes: usize,
    empty_code: &'static str,
    too_large_code: &'static str,
    invalid_code: &'static str,
) -> Result<Vec<u8>, CliError> {
    if value.is_empty() {
        return Err(CliError::new(empty_code));
    }
    let maximum_hex_len = maximum_decoded_bytes
        .checked_mul(2)
        .ok_or_else(|| CliError::new(too_large_code))?;
    if value.len() > maximum_hex_len {
        return Err(CliError::new(too_large_code));
    }
    let bytes = value.as_bytes();
    if !bytes.len().is_multiple_of(2) {
        return Err(CliError::new(invalid_code));
    }
    let mut decoded = Vec::with_capacity(bytes.len() / 2);
    for pair in bytes.chunks_exact(2) {
        let high = decode_lower_hex_nibble(pair[0]).ok_or_else(|| CliError::new(invalid_code))?;
        let low = decode_lower_hex_nibble(pair[1]).ok_or_else(|| CliError::new(invalid_code))?;
        decoded.push((high << 4) | low);
    }
    Ok(decoded)
}

const fn decode_lower_hex_nibble(value: u8) -> Option<u8> {
    match value {
        b'0'..=b'9' => Some(value - b'0'),
        b'a'..=b'f' => Some(value - b'a' + 10),
        _ => None,
    }
}

fn project_verified_admission(
    receipt_bytes: &[u8],
    admission: &VerifiedSourceOpenedSpotSettlementAdmissionV6,
) -> Result<VerifiedSettlementAdmissionV1, CliError> {
    let verified = admission.verified_receipt();
    let journal = verified.journal();
    let journal_bytes = &verified.receipt().journal.bytes;
    let plan = decode_exact_settlement_effect_plan_v2(journal.effect_plan_bytes())
        .map_err(|_| CliError::new("verified_effect_plan_decode_failed"))?;
    let identity = pinned_source_opened_spot_settlement_identity_v6()
        .map_err(|_| CliError::new("governed_settlement_identity_failed"))?;
    if verified.verified_program_id() != identity.expected_program_id()
        || verified.verified_program_manifest_root() != identity.expected_manifest_root()
    {
        return Err(CliError::new("governed_settlement_identity_mismatch"));
    }
    let execution_projection = project_execution(&plan)?;
    let (semantic_root_kind, semantic_root) = match journal.semantic_root() {
        SettlementSemanticRootV1::SemanticEpoch(root) => ("semantic_epoch", hex32(root.as_bytes())),
        SettlementSemanticRootV1::ValueSubtree(root) => ("value_subtree", hex32(root.as_bytes())),
    };
    let profile = verified.receipt_profile();
    Ok(VerifiedSettlementAdmissionV1 {
        receipt_bytes: receipt_bytes.len(),
        receipt_sha256: hex32(&sha256(receipt_bytes)),
        guest_input_bytes: admission.exact_guest_input_bytes().len(),
        guest_input_sha256: hex32(&sha256(admission.exact_guest_input_bytes())),
        admission_journal_bytes: journal_bytes.len(),
        admission_journal_hex: hex_encode(journal_bytes),
        admission_journal_sha256: hex32(&sha256(journal_bytes)),
        certificate_bytes: journal.certificate_bytes().len(),
        certificate_hex: hex_encode(journal.certificate_bytes()),
        certificate_sha256: hex32(&journal.certificate_sha256()),
        effect_plan_bytes: journal.effect_plan_bytes().len(),
        effect_plan_hex: hex_encode(journal.effect_plan_bytes()),
        effect_plan_sha256: hex32(&journal.effect_plan_sha256()),
        governed_settlement_program_id: hex32(verified.verified_program_id().as_bytes()),
        governed_settlement_profile_id: hex32(identity.expected_profile_id().as_bytes()),
        governed_settlement_manifest_root: hex32(
            verified.verified_program_manifest_root().as_bytes(),
        ),
        settlement_claim_binding: hex32(verified.settlement_claim_binding().as_bytes()),
        receipt_security_profile: ReceiptSecurityProfileV1 {
            profile_id: profile.profile_id().to_owned(),
            receipt_kind: profile.receipt_kind().to_owned(),
            verifier_parameters: profile.verifier_parameters().to_owned(),
            hashfn: profile.hashfn().to_owned(),
            control_id: profile.control_id().to_owned(),
        },
        admission_projection: AdmissionProjectionV1 {
            journal_version: journal.journal_version(),
            certificate_version: journal.certificate_version(),
            effect_plan_version: journal.effect_plan_version(),
            application_id: hex32(journal.application_id().as_bytes()),
            chain_or_domain_id: hex32(journal.chain_or_domain_id().as_bytes()),
            epoch_id: journal.epoch_id(),
            semantic_profile_id: hex32(journal.semantic_profile_id().as_bytes()),
            semantic_journal_hash: hex32(journal.semantic_journal_hash().as_bytes()),
            semantic_claim_binding: hex32(journal.semantic_claim_binding().as_bytes()),
            proof_tree_root: hex32(journal.proof_tree_root().as_bytes()),
            semantic_root_kind,
            semantic_root,
            dependency_manifest_root: hex32(journal.dependency_manifest_root().as_bytes()),
            public_policy_hash: hex32(journal.public_policy_hash().as_bytes()),
            economic_action_batch_commitment: hex32(
                journal.economic_action_batch_commitment().as_bytes(),
            ),
            settlement_effect_plan_commitment: hex32(
                journal.settlement_effect_plan_commitment().as_bytes(),
            ),
            economic_action_ids_root: hex32(journal.economic_action_ids_root().as_bytes()),
            action_authorization_bindings_root: hex32(
                journal.action_authorization_bindings_root().as_bytes(),
            ),
            authorization_grant_spends_root: hex32(
                journal.authorization_grant_spends_root().as_bytes(),
            ),
            consumed_object_ids_root: hex32(journal.consumed_object_ids_root().as_bytes()),
            action_count: journal.action_count(),
            consumed_object_count: journal.consumed_object_count(),
            pre_state_root: hex32(journal.pre_state_root().as_bytes()),
            post_state_root: hex32(journal.post_state_root().as_bytes()),
            cell_writes_root: hex32(journal.cell_writes_root().as_bytes()),
            asset_effects_root: hex32(journal.asset_effects_root().as_bytes()),
            messages_root: hex32(journal.messages_root().as_bytes()),
            carries_root: hex32(journal.carries_root().as_bytes()),
            rewards_root: hex32(journal.rewards_root().as_bytes()),
            data_availability_certificate_root: hex32(
                journal.data_availability_certificate_root().as_bytes(),
            ),
            schedule_certificate_root: hex32(journal.schedule_certificate_root().as_bytes()),
            carry_continuity_certificate_root: hex32(
                journal.carry_continuity_certificate_root().as_bytes(),
            ),
            settlement_certificate_id: hex32(journal.settlement_certificate_id().as_bytes()),
            certificate_commitment: hex32(journal.certificate_commitment().as_bytes()),
        },
        execution_projection,
    })
}

fn project_execution(plan: &SettlementEffectPlanV2) -> Result<ExecutionProjectionV1, CliError> {
    if !plan.message_effects().is_empty() {
        return Err(CliError::new("unsupported_message_effects"));
    }
    if !plan.carry_effects().is_empty() {
        return Err(CliError::new("unsupported_carry_effects"));
    }
    if !plan.reward_effects().is_empty() {
        return Err(CliError::new("unsupported_reward_effects"));
    }
    let batch = plan.economic_action_batch();
    if batch.actions().len() != EXPECTED_ACTION_COUNT {
        return Err(CliError::new("unsupported_action_count"));
    }
    if plan.ledger_cell_writes().len() != EXPECTED_CELL_WRITE_COUNT {
        return Err(CliError::new("unsupported_cell_write_count"));
    }
    if plan.asset_effects().len() != EXPECTED_ORDINARY_ASSET_ROW_COUNT {
        return Err(CliError::new("unsupported_asset_effect_count"));
    }

    let authorized_action = &batch.actions()[0];
    let record = authorized_action.record();
    let action_id = authorized_action
        .action_id()
        .map_err(|_| CliError::new("economic_action_id_derivation_failed"))?;
    if record.consumed_object_ids().len() != 1 {
        return Err(CliError::new("unsupported_consumed_object_count"));
    }
    let cell_write = &plan.ledger_cell_writes()[0];
    if cell_write.economic_action_id() != action_id {
        return Err(CliError::new("cell_write_action_mismatch"));
    }

    let mut ordinary_asset_rows = Vec::with_capacity(plan.asset_effects().len());
    for row in plan.asset_effects() {
        if row.kind() != AssetEffectKindV2::OrdinaryTransfer {
            return Err(CliError::new("unsupported_nonordinary_asset_effect"));
        }
        if row.economic_action_id() != action_id {
            return Err(CliError::new("asset_effect_action_mismatch"));
        }
        if row.authorized_mint_atoms() != 0 || row.authorized_burn_atoms() != 0 {
            return Err(CliError::new("unsupported_supply_effect"));
        }
        if row.authority_scope_id().is_some() || row.action_authorization_binding().is_some() {
            return Err(CliError::new("unexpected_asset_effect_authority"));
        }
        if row.debit_atoms() == 0 || row.debit_atoms() != row.credit_atoms() {
            return Err(CliError::new("ordinary_asset_effect_not_conserved"));
        }
        ordinary_asset_rows.push(OrdinaryAssetProjectionV1 {
            economic_action_id: hex32(row.economic_action_id().as_bytes()),
            asset_id: hex32(row.asset_id().as_bytes()),
            debit_atoms: row.debit_atoms().to_string(),
            credit_atoms: row.credit_atoms().to_string(),
        });
    }

    let authorization_binding = authorized_action
        .action_authorization_binding()
        .map_err(|_| CliError::new("action_authorization_binding_derivation_failed"))?;
    let grant_spend = authorized_action
        .authorization_grant_spend()
        .map_err(|_| CliError::new("authorization_grant_spend_derivation_failed"))?;
    Ok(ExecutionProjectionV1 {
        application_id: hex32(batch.application_id().as_bytes()),
        chain_or_domain_id: hex32(batch.chain_or_domain_id().as_bytes()),
        epoch_id: batch.epoch_id(),
        pre_state_root: hex32(batch.pre_state_root().as_bytes()),
        post_state_root: hex32(plan.post_state_root().as_bytes()),
        action: ActionProjectionV1 {
            action_id: hex32(action_id.as_bytes()),
            action_type_id: hex32(record.action_type_id().as_bytes()),
            authorization_subject_id: hex32(record.authorization_subject_id().as_bytes()),
            authorization_scope_id: hex32(record.authorization_scope_id().as_bytes()),
            authorization_nonce: record.authorization_nonce(),
            authorization_grant_id: hex32(authorized_action.authorization_grant_id().as_bytes()),
            action_authorization_binding: hex32(authorization_binding.as_bytes()),
            authorization_grant_spend_nullifier: hex32(grant_spend.as_bytes()),
            valid_from_epoch: record.valid_from_epoch(),
            valid_through_epoch: record.valid_through_epoch(),
            pre_state_root: hex32(record.pre_state_root().as_bytes()),
            action_semantics_hash: hex32(record.action_semantics_hash().as_bytes()),
            effect_commitment: hex32(record.effect_commitment().as_bytes()),
            consumed_object_ids: record
                .consumed_object_ids()
                .iter()
                .map(|value| hex32(value.as_bytes()))
                .collect(),
        },
        cell_write: CellWriteProjectionV1 {
            economic_action_id: hex32(cell_write.economic_action_id().as_bytes()),
            cell_key: hex32(cell_write.cell_key().as_bytes()),
            pre_value_hash: hex32(cell_write.pre_value_hash().as_bytes()),
            post_value_hash: hex32(cell_write.post_value_hash().as_bytes()),
        },
        ordinary_asset_rows,
    })
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn hex32(bytes: &[u8; 32]) -> String {
    hex_encode(bytes)
}

fn hex_encode(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut encoded = String::with_capacity(bytes.len().saturating_mul(2));
    for value in bytes {
        encoded.push(char::from(DIGITS[usize::from(value >> 4)]));
        encoded.push(char::from(DIGITS[usize::from(value & 0x0f)]));
    }
    encoded
}

fn write_response(response: &VerifyResponseV1) -> Result<(), CliError> {
    let bytes =
        serde_json::to_vec(response).map_err(|_| CliError::new("response_json_encode_failed"))?;
    if bytes.len() > MAX_RESPONSE_BYTES {
        return Err(CliError::new("response_too_large"));
    }
    let mut stdout = io::stdout().lock();
    stdout
        .write_all(&bytes)
        .and_then(|()| stdout.flush())
        .map_err(|_| CliError::new("response_write_failed"))
}

fn emit_error_and_exit(error: CliError) -> ! {
    let response = ErrorResponseV1 {
        ok: false,
        schema: ERROR_SCHEMA,
        error_code: error.code,
    };
    if let Ok(bytes) = serde_json::to_vec(&response) {
        let mut stderr = io::stderr().lock();
        let _ = stderr.write_all(&bytes);
        let _ = stderr.flush();
    }
    std::process::exit(1)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn request(receipt_hex: &str, guest_input_hex: &str) -> VerifyRequestV1 {
        VerifyRequestV1 {
            schema: REQUEST_SCHEMA.to_owned(),
            receipt_hex: receipt_hex.to_owned(),
            guest_input_hex: guest_input_hex.to_owned(),
        }
    }

    #[test]
    fn canonical_request_round_trips_exactly() {
        let request = request("00ff", "1020");
        let bytes = serde_json::to_vec(&request).expect("serialize request");
        let decoded = decode_exact_request(&bytes).expect("canonical request");
        assert_eq!(decoded.receipt_hex, "00ff");
        assert_eq!(decoded.guest_input_hex, "1020");
    }

    #[test]
    fn request_rejects_unknown_duplicate_and_noncanonical_forms() {
        let unknown = br#"{"schema":"zenodex.source_opened_spot_settlement_verifier_v6.request.v1","receipt_hex":"00","guest_input_hex":"11","extra":true}"#;
        assert_eq!(
            decode_exact_request(unknown)
                .expect_err("unknown field")
                .code,
            "request_json_invalid"
        );
        let duplicate = br#"{"schema":"zenodex.source_opened_spot_settlement_verifier_v6.request.v1","receipt_hex":"00","receipt_hex":"11","guest_input_hex":"22"}"#;
        assert_eq!(
            decode_exact_request(duplicate)
                .expect_err("duplicate field")
                .code,
            "request_json_invalid"
        );
        let mut noncanonical = serde_json::to_vec(&request("00", "11")).expect("request");
        noncanonical.push(b'\n');
        assert_eq!(
            decode_exact_request(&noncanonical)
                .expect_err("trailing whitespace")
                .code,
            "request_json_noncanonical"
        );
    }

    #[test]
    fn lowercase_hex_is_exact_and_bounded() {
        assert_eq!(
            decode_exact_lower_hex("00af", 2, "empty", "large", "invalid").expect("lower hex"),
            vec![0, 0xaf]
        );
        for invalid in ["0", "0A", "0x00", "gg"] {
            assert_eq!(
                decode_exact_lower_hex(invalid, 16, "empty", "large", "invalid")
                    .expect_err("invalid hex")
                    .code,
                "invalid"
            );
        }
        assert_eq!(
            decode_exact_lower_hex("0000", 1, "empty", "large", "invalid")
                .expect_err("oversized")
                .code,
            "large"
        );
    }

    #[test]
    fn verifier_boundary_is_called_once_in_binary_source() {
        let source = include_str!("source_opened_spot_settlement_verifier_v6.rs");
        let call = ["VerifiedSourceOpenedSpotSettlementAdmissionV6", "::verify("].concat();
        assert_eq!(source.matches(&call).count(), 1);
    }
}
