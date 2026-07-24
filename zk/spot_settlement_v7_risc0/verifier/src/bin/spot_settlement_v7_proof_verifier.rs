//! Strict external verifier for one source-opened ordinary-Spot V7 proof.
//!
//! The binary accepts exactly three canonical byte artifacts.  It invokes the
//! sealed V7 verifier once, then projects only values derived from the
//! authenticated receipt and its retained V6 child. Its canonical JSON output
//! remains authority-neutral until an atomic consumer binds this exact
//! executable and manifest to the transaction-locked current release.

use std::io::{self, Read, Write};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::AssetEffectKindV2;
use zenodex_zrpf_risc0_spot_settlement_v7_shared::MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1;
use zenodex_zrpf_risc0_spot_settlement_v7_verifier::{
    encode_spot_settlement_v7_verifier_output_v1,
    verify_spot_settlement_v7_canonical_succinct_bytes, VerifiedSpotSettlementV7ReceiptV1,
    MAX_CANONICAL_SPOT_SETTLEMENT_V7_RECEIPT_BYTES_V1,
};

const REQUEST_SCHEMA: &str = "zenodex.zrpf_spot_v7_proof_verifier.request.v1";
const RESPONSE_SCHEMA: &str = "zenodex.zrpf_spot_v7_proof_verifier.response.v1";
const ERROR_SCHEMA: &str = "zenodex.zrpf_spot_v7_proof_verifier.error.v1";
const MAX_SOURCE_V6_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_REQUEST_BYTES: usize = 128 * 1_024 * 1_024;
const MAX_RESPONSE_BYTES: usize = 256 * 1_024;

#[derive(Debug, Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct VerifyRequestV1 {
    schema: String,
    v7_receipt_hex: String,
    guest_input_hex: String,
    source_v6_receipt_hex: String,
}

#[derive(Debug, Serialize)]
struct VerifyResponseV1 {
    ok: bool,
    schema: &'static str,
    authenticated_projection: AuthenticatedProjectionV1,
}

#[derive(Debug, Serialize)]
struct AuthenticatedProjectionV1 {
    request_bytes: usize,
    request_sha256: String,
    v7_receipt_bytes: usize,
    v7_receipt_sha256: String,
    guest_input_bytes: usize,
    guest_input_sha256: String,
    source_v6_receipt_bytes: usize,
    source_v6_receipt_sha256: String,
    verifier_output_bytes: usize,
    verifier_output_hex: String,
    verifier_output_sha256: String,
    journal_bytes: usize,
    journal_sha256: String,
    plan_b_bytes: usize,
    plan_b_sha256: String,
    verified_program_id: String,
    verified_profile_id: String,
    verified_program_manifest_root: String,
    receipt_security_profile: ReceiptSecurityProfileV1,
    source_child_program_id: String,
    required_source_child_receipt_security_profile_id: String,
    source_child_claim_binding: String,
    source_child_journal_sha256: String,
    application_id: String,
    chain_or_domain_id: String,
    epoch_id: u64,
    data_availability_certificate_root: String,
    data_root: String,
    settlement_effect_plan_commitment: String,
    economic_action_id: String,
    authorization_nullifier: String,
    authorization_grant_spend_nullifier: String,
    consumed_object_ids: Vec<String>,
    action_ids_root: String,
    action_authorization_bindings_root: String,
    authorization_grant_spends_root: String,
    consumed_object_ids_root: String,
    cell_transitions_root: String,
    pre_state_root: String,
    post_state_root: String,
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
    let v7_receipt = decode_exact_lower_hex(
        &request.v7_receipt_hex,
        MAX_CANONICAL_SPOT_SETTLEMENT_V7_RECEIPT_BYTES_V1,
        "v7_receipt_empty",
        "v7_receipt_too_large",
        "v7_receipt_invalid",
    )?;
    let guest_input = decode_exact_lower_hex(
        &request.guest_input_hex,
        MAX_SPOT_SETTLEMENT_V7_GUEST_ENVELOPE_BYTES_V1,
        "guest_input_empty",
        "guest_input_too_large",
        "guest_input_invalid",
    )?;
    let source_v6_receipt = decode_exact_lower_hex(
        &request.source_v6_receipt_hex,
        MAX_SOURCE_V6_RECEIPT_BYTES,
        "source_v6_receipt_empty",
        "source_v6_receipt_too_large",
        "source_v6_receipt_invalid",
    )?;

    // This is the sole V7 receipt-verifier invocation in this executable.  The
    // sealed verifier also authenticates the exact retained V6 child receipt.
    let verified = verify_spot_settlement_v7_canonical_succinct_bytes(
        &v7_receipt,
        &guest_input,
        &source_v6_receipt,
    )
    .map_err(|error| CliError::new(error.code()))?;
    let projection = project_verified(
        &request_bytes,
        &v7_receipt,
        &guest_input,
        &source_v6_receipt,
        &verified,
    )?;
    Ok(VerifyResponseV1 {
        ok: true,
        schema: RESPONSE_SCHEMA,
        authenticated_projection: projection,
    })
}

fn project_verified(
    request_bytes: &[u8],
    v7_receipt: &[u8],
    guest_input: &[u8],
    source_v6_receipt: &[u8],
    verified: &VerifiedSpotSettlementV7ReceiptV1,
) -> Result<AuthenticatedProjectionV1, CliError> {
    let verifier_output = verified
        .firecracker_output()
        .map_err(|_| CliError::new("verifier_output_failed"))?;
    let verifier_output_bytes = encode_spot_settlement_v7_verifier_output_v1(&verifier_output)
        .map_err(|_| CliError::new("verifier_output_encode_failed"))?;
    let plan = verified.plan_b();
    let batch = plan.economic_action_batch();
    let [action] = batch.actions() else {
        return Err(CliError::new("verified_action_count_unsupported"));
    };
    if plan.asset_effects().len() != 2
        || plan
            .asset_effects()
            .iter()
            .any(|effect| effect.kind() != AssetEffectKindV2::OrdinaryTransfer)
        || !plan.message_effects().is_empty()
        || !plan.carry_effects().is_empty()
        || !plan.reward_effects().is_empty()
    {
        return Err(CliError::new("verified_effect_profile_unsupported"));
    }
    let action_id = action
        .action_id()
        .map_err(|_| CliError::new("economic_action_id_failed"))?;
    let authorization_nullifier = action
        .action_authorization_binding()
        .map_err(|_| CliError::new("authorization_nullifier_failed"))?;
    let grant_spend = action
        .authorization_grant_spend()
        .map_err(|_| CliError::new("authorization_grant_spend_failed"))?;
    let profile = verified.receipt_profile();
    let journal = verified.journal();
    let plan_bytes = verifier_output
        .exact_plan_b_bytes()
        .map_err(|_| CliError::new("verified_plan_encode_failed"))?;
    Ok(AuthenticatedProjectionV1 {
        request_bytes: request_bytes.len(),
        request_sha256: hex32(&sha256(request_bytes)),
        v7_receipt_bytes: v7_receipt.len(),
        v7_receipt_sha256: hex32(&sha256(v7_receipt)),
        guest_input_bytes: guest_input.len(),
        guest_input_sha256: hex32(&sha256(guest_input)),
        source_v6_receipt_bytes: source_v6_receipt.len(),
        source_v6_receipt_sha256: hex32(&sha256(source_v6_receipt)),
        verifier_output_bytes: verifier_output_bytes.len(),
        verifier_output_hex: hex_encode(&verifier_output_bytes),
        verifier_output_sha256: hex32(&sha256(&verifier_output_bytes)),
        journal_bytes: verifier_output.journal_bytes().len(),
        journal_sha256: hex32(verified.journal_sha256().as_bytes()),
        plan_b_bytes: plan_bytes.len(),
        plan_b_sha256: hex32(&sha256(&plan_bytes)),
        verified_program_id: hex32(verified.verified_program_id().as_bytes()),
        verified_profile_id: hex32(verified.verified_profile_id().as_bytes()),
        verified_program_manifest_root: hex32(verified.verified_program_manifest_root().as_bytes()),
        receipt_security_profile: ReceiptSecurityProfileV1 {
            profile_id: profile.profile_id().to_owned(),
            receipt_kind: profile.receipt_kind().to_owned(),
            verifier_parameters: profile.verifier_parameters().to_owned(),
            hashfn: profile.hashfn().to_owned(),
            control_id: profile.control_id().to_owned(),
        },
        source_child_program_id: hex32(journal.source_child_program_id().as_bytes()),
        required_source_child_receipt_security_profile_id: hex32(
            journal
                .required_source_child_receipt_security_profile_id()
                .as_bytes(),
        ),
        source_child_claim_binding: hex32(journal.source_child_claim_binding().as_bytes()),
        source_child_journal_sha256: hex32(journal.source_child_journal_sha256().as_bytes()),
        application_id: hex32(batch.application_id().as_bytes()),
        chain_or_domain_id: hex32(batch.chain_or_domain_id().as_bytes()),
        epoch_id: batch.epoch_id(),
        data_availability_certificate_root: hex32(
            journal.data_availability_certificate_root().as_bytes(),
        ),
        data_root: hex32(journal.data_root().as_bytes()),
        settlement_effect_plan_commitment: hex32(
            journal.settlement_effect_plan_commitment().as_bytes(),
        ),
        economic_action_id: hex32(action_id.as_bytes()),
        authorization_nullifier: hex32(authorization_nullifier.as_bytes()),
        authorization_grant_spend_nullifier: hex32(grant_spend.as_bytes()),
        consumed_object_ids: action
            .record()
            .consumed_object_ids()
            .iter()
            .map(|value| hex32(value.as_bytes()))
            .collect(),
        action_ids_root: hex32(batch.action_ids_root().as_bytes()),
        action_authorization_bindings_root: hex32(
            batch.action_authorization_bindings_root().as_bytes(),
        ),
        authorization_grant_spends_root: hex32(batch.authorization_grant_spends_root().as_bytes()),
        consumed_object_ids_root: hex32(batch.consumed_object_ids_root().as_bytes()),
        cell_transitions_root: hex32(verified.cell_transitions_root().as_bytes()),
        pre_state_root: hex32(plan.economic_action_batch().pre_state_root().as_bytes()),
        post_state_root: hex32(plan.post_state_root().as_bytes()),
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

    fn request(v7: &str, guest: &str, child: &str) -> VerifyRequestV1 {
        VerifyRequestV1 {
            schema: REQUEST_SCHEMA.to_owned(),
            v7_receipt_hex: v7.to_owned(),
            guest_input_hex: guest.to_owned(),
            source_v6_receipt_hex: child.to_owned(),
        }
    }

    #[test]
    fn canonical_request_round_trips_exactly() {
        let value = request("00ff", "1020", "aabb");
        let bytes = serde_json::to_vec(&value).unwrap();
        let decoded = decode_exact_request(&bytes).unwrap();
        assert_eq!(decoded.v7_receipt_hex, "00ff");
        assert_eq!(decoded.guest_input_hex, "1020");
        assert_eq!(decoded.source_v6_receipt_hex, "aabb");
    }

    #[test]
    fn request_rejects_unknown_duplicate_and_noncanonical_forms() {
        let unknown = br#"{"schema":"zenodex.zrpf_spot_v7_proof_verifier.request.v1","v7_receipt_hex":"00","guest_input_hex":"11","source_v6_receipt_hex":"22","extra":true}"#;
        assert_eq!(
            decode_exact_request(unknown).unwrap_err().code,
            "request_json_invalid"
        );
        let duplicate = br#"{"schema":"zenodex.zrpf_spot_v7_proof_verifier.request.v1","v7_receipt_hex":"00","v7_receipt_hex":"11","guest_input_hex":"22","source_v6_receipt_hex":"33"}"#;
        assert_eq!(
            decode_exact_request(duplicate).unwrap_err().code,
            "request_json_invalid"
        );
        let mut noncanonical = serde_json::to_vec(&request("00", "11", "22")).unwrap();
        noncanonical.push(b'\n');
        assert_eq!(
            decode_exact_request(&noncanonical).unwrap_err().code,
            "request_json_noncanonical"
        );
    }

    #[test]
    fn lowercase_hex_is_exact_and_bounded() {
        assert_eq!(
            decode_exact_lower_hex("00af", 2, "empty", "large", "invalid").unwrap(),
            vec![0, 0xaf]
        );
        for invalid in ["0", "0A", "0x00", "gg"] {
            assert_eq!(
                decode_exact_lower_hex(invalid, 16, "empty", "large", "invalid")
                    .unwrap_err()
                    .code,
                "invalid"
            );
        }
    }

    #[test]
    fn sealed_v7_verifier_is_invoked_once_in_binary_source() {
        let source = include_str!("spot_settlement_v7_proof_verifier.rs");
        let call = ["verify_spot_settlement_v7_canonical_", "succinct_bytes("].concat();
        assert_eq!(source.matches(&call).count(), 1);
    }
}
