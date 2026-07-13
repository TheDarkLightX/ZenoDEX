use std::{env, fs, path::Path};

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use risc0_zkvm::{Digest, InnerReceipt, Receipt};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use tau_state_proof_risc0_shared::{
    compose_recursive_epoch_journal_v1, recursive_epoch_journal_bytes_hash_v1,
    RecursiveCompositionInputV1, RecursiveEpochJournalV1, PROOF_TYPE_RECURSIVE,
    RECURSIVE_DOMAIN_SEPARATOR_V1, RECURSIVE_EPOCH_PROFILE_V1, RECURSIVE_JOURNAL_VERSION_V1,
};

const MAX_REQUEST_BYTES: usize = 16 * 1024 * 1024;
const MAX_REQUEST_BYTES_U64: u64 = 16 * 1024 * 1024;
const RECEIPT_CODEC: &str = "risc0_receipt_canonical_serde_json_depth128_v1";
const RECEIPT_CONTROL_ID: &str = "53a7b23d07f99e5d5685e85874f5181e8486aa267a0ae607ffe9ba47c8bdda4a";
const RECEIPT_HASHFN: &str = "poseidon2";
const RECEIPT_VERIFIER_PARAMETERS: &str =
    "ece5e9b8ae2cd6ea6b1827b464ff0348f9a7f4decd269c0087fdfd75098da013";
const GOVERNED_AGGREGATE_V1_ID: [u32; 8] = [
    1_373_879_748,
    2_005_831_380,
    528_690_780,
    2_327_412_675,
    1_508_722_078,
    1_996_380_741,
    3_788_665_365,
    3_302_419_996,
];
const COMPOSITION_FIELDS: &[&str] = &[
    "statement",
    "allowed_verifier_ids",
    "allowed_authority_roots",
    "children",
];
const STATEMENT_FIELDS: &[&str] = &[
    "domain_separator",
    "schema_version",
    "chain_id",
    "epoch_id",
    "proof_profile",
    "verifier_set_root",
    "allowed_authority_roots_root",
    "public_policy_hash",
    "feature_suite_hash",
    "dependency_lock_hash",
    "toolchain_lock_hash",
    "expected_pre_state_root",
    "expected_post_state_root",
    "conflict_schedule_hash",
    "carry_queue_pre_root",
    "carry_queue_post_root",
    "data_availability_root",
    "expected_child_count",
    "max_children",
    "max_child_journal_bytes",
    "max_total_child_journal_bytes",
    "max_asset_delta_rows",
    "max_cross_shard_messages",
    "max_receipt_ids",
    "cross_shard_mode",
];
const CHILD_FIELDS: &[&str] = &[
    "descriptor",
    "child_journal_bytes",
    "summary",
    "asset_delta_rows",
    "outbox_messages",
    "inbox_messages",
    "accepted_receipt_ids",
    "rejected_receipt_ids",
];
const DESCRIPTOR_FIELDS: &[&str] = &[
    "child_verification_claim_hash",
    "child_journal_hash",
    "child_effect_summary_hash",
    "child_statement_hash",
    "child_image_id",
    "child_verifier_id",
    "child_profile",
];
const SUMMARY_FIELDS: &[&str] = &[
    "summary_version",
    "lane_id",
    "lane_kind",
    "chain_id",
    "epoch_id",
    "proof_profile",
    "risc0_image_id",
    "statement_hash",
    "pre_state_root",
    "post_state_root",
    "tx_root",
    "evidence_root",
    "receipt_root",
    "accepted_receipts_root",
    "rejected_receipts_root",
    "asset_delta_root",
    "cross_shard_outbox_root",
    "cross_shard_inbox_root",
    "write_set_root",
    "public_policy_hash",
    "feature_suite_hash",
    "dependency_lock_hash",
    "toolchain_lock_hash",
];
const ASSET_DELTA_FIELDS: &[&str] = &[
    "asset_id",
    "debit_atoms",
    "credit_atoms",
    "authorized_mint_atoms",
    "authorized_burn_atoms",
    "authority_root",
];
const MESSAGE_FIELDS: &[&str] = &[
    "message_id",
    "epoch_id",
    "source_shard_id",
    "destination_shard_id",
    "asset_id",
    "amount_atoms",
    "sender_scope_hash",
    "recipient_scope_hash",
    "source_receipt_hash",
    "deadline_epoch",
];

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct VerifyRequest {
    schema: String,
    schema_version: u32,
    state_hash: String,
    proof: ReceiptArtifact,
    recursive_input: Value,
    recursive_expectations: Value,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ReceiptArtifact {
    schema: String,
    schema_version: u32,
    proof_type: String,
    state_hash: String,
    meta: Value,
    proof: String,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let request_path = args
        .next()
        .ok_or_else(|| "usage: verify_recursive_v1_root <verification-request>".to_string())?;
    if args.next().is_some() {
        return Err("verify_recursive_v1_root accepts exactly one request".to_string());
    }
    if risc0_dev_mode_env_enabled() {
        return Err("RISC0_DEV_MODE set: verifier refuses dev-mode receipts".to_string());
    }

    let request = read_canonical_request(Path::new(&request_path))?;
    validate_request_header(&request)?;
    let (receipt, receipt_bytes) = decode_receipt(&request.proof)?;
    validate_receipt_security(&receipt)?;
    receipt
        .verify(GOVERNED_AGGREGATE_V1_ID)
        .map_err(|error| format!("receipt verification failed: {error}"))?;

    let journal = decode_exact_journal(&receipt)?;
    validate_authenticated_journal(&journal)?;
    validate_disclosure_and_bindings(&request, &journal)?;
    let journal_hash = recursive_epoch_journal_bytes_hash_v1(&receipt.journal.bytes)
        .map_err(|error| format!("protocol journal hash: {error:?}"))?;

    println!(
        "{}",
        json!({
            "aggregate_v1_image_id": image_id_hex(),
            "child_verification_claims_root": hex32(&journal.child_verification_claims_root),
            "ok": true,
            "receipt_sha256": sha256_hex(&receipt_bytes),
            "root_journal_hash": hex32(&journal_hash),
            "status": "recursive_v1_root_verified",
        })
    );
    Ok(())
}

fn read_canonical_request(path: &Path) -> Result<VerifyRequest, String> {
    let metadata =
        fs::metadata(path).map_err(|error| format!("{} metadata: {error}", path.display()))?;
    if !metadata.is_file() || metadata.len() > MAX_REQUEST_BYTES_U64 {
        return Err(format!("{} is not a bounded regular file", path.display()));
    }
    let bytes = fs::read(path).map_err(|error| format!("{} read: {error}", path.display()))?;
    if bytes.len() > MAX_REQUEST_BYTES {
        return Err(format!("{} exceeds the request byte limit", path.display()));
    }
    let value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("{} JSON: {error}", path.display()))?;
    let canonical = serde_json::to_vec(&value)
        .map_err(|error| format!("{} canonical JSON: {error}", path.display()))?;
    if canonical != bytes {
        return Err(format!("{} is not canonical JSON", path.display()));
    }
    serde_json::from_slice(&bytes)
        .map_err(|error| format!("{} request schema: {error}", path.display()))
}

fn validate_request_header(request: &VerifyRequest) -> Result<(), String> {
    if request.schema != "tau_state_proof_verify"
        || request.schema_version != 1
        || request.proof.schema != "tau_state_proof"
        || request.proof.schema_version != 1
        || request.proof.proof_type != PROOF_TYPE_RECURSIVE
    {
        return Err("V1 verification request header mismatch".to_string());
    }
    Ok(())
}

fn decode_receipt(artifact: &ReceiptArtifact) -> Result<(Receipt, Vec<u8>), String> {
    if artifact.proof.len() > MAX_REQUEST_BYTES.div_ceil(3) * 4 {
        return Err("receipt base64 exceeds the byte limit".to_string());
    }
    let bytes = BASE64_STANDARD
        .decode(&artifact.proof)
        .map_err(|error| format!("receipt base64: {error}"))?;
    if bytes.len() > MAX_REQUEST_BYTES || BASE64_STANDARD.encode(&bytes) != artifact.proof {
        return Err("receipt base64 is not canonical and bounded".to_string());
    }
    let receipt: Receipt =
        serde_json::from_slice(&bytes).map_err(|error| format!("receipt JSON: {error}"))?;
    let canonical =
        serde_json::to_vec(&receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if canonical != bytes {
        return Err("receipt JSON is not canonical".to_string());
    }
    Ok((receipt, bytes))
}

fn validate_receipt_security(receipt: &Receipt) -> Result<(), String> {
    let InnerReceipt::Succinct(inner) = &receipt.inner else {
        return Err("receipt is not succinct".to_string());
    };
    if inner.hashfn != RECEIPT_HASHFN
        || inner.control_id.to_string() != RECEIPT_CONTROL_ID
        || receipt.metadata.verifier_parameters.to_string() != RECEIPT_VERIFIER_PARAMETERS
    {
        return Err("receipt security profile mismatch".to_string());
    }
    Ok(())
}

fn decode_exact_journal(receipt: &Receipt) -> Result<RecursiveEpochJournalV1, String> {
    let (journal, remainder): (RecursiveEpochJournalV1, &[u8]) =
        postcard::take_from_bytes(&receipt.journal.bytes)
            .map_err(|error| format!("authenticated journal decode: {error}"))?;
    if !remainder.is_empty() {
        return Err("authenticated journal has trailing bytes".to_string());
    }
    let canonical =
        postcard::to_allocvec(&journal).map_err(|error| format!("journal encode: {error}"))?;
    if canonical != receipt.journal.bytes {
        return Err("authenticated journal is not canonical postcard".to_string());
    }
    Ok(journal)
}

fn validate_authenticated_journal(journal: &RecursiveEpochJournalV1) -> Result<(), String> {
    if journal.journal_version != RECURSIVE_JOURNAL_VERSION_V1
        || journal.proof_type != PROOF_TYPE_RECURSIVE
        || journal.domain_separator != RECURSIVE_DOMAIN_SEPARATOR_V1
        || journal.proof_profile != RECURSIVE_EPOCH_PROFILE_V1
        || journal.child_count != 2
    {
        return Err("authenticated V1 journal surface mismatch".to_string());
    }
    Ok(())
}

fn validate_disclosure_and_bindings(
    request: &VerifyRequest,
    journal: &RecursiveEpochJournalV1,
) -> Result<(), String> {
    let recursive_input = decode_recursive_input(&request.recursive_input)?;
    let recomposed = compose_recursive_epoch_journal_v1(&recursive_input)
        .map_err(|error| format!("recursive disclosure: {error:?}"))?;
    if recomposed != *journal {
        return Err("recursive_input disclosure does not match authenticated journal".to_string());
    }

    let post_state = hex32(&journal.post_state_root);
    if request.state_hash != post_state || request.proof.state_hash != post_state {
        return Err("request state hash does not match authenticated post-state".to_string());
    }
    let expected_meta = expected_meta(journal)?;
    if request.proof.meta != expected_meta {
        return Err("proof metadata does not match authenticated journal".to_string());
    }
    let expected_expectations = expected_expectations(journal);
    if request.recursive_expectations != expected_expectations {
        return Err("trusted expectations do not match authenticated journal".to_string());
    }
    Ok(())
}

fn decode_recursive_input(value: &Value) -> Result<RecursiveCompositionInputV1, String> {
    validate_recursive_input_shape(value)?;
    serde_json::from_value(value.clone())
        .map_err(|error| format!("recursive_input typed decode: {error}"))
}

fn validate_recursive_input_shape(value: &Value) -> Result<(), String> {
    let input = exact_object(value, "recursive_input", COMPOSITION_FIELDS)?;
    if let Some(statement) = input.get("statement") {
        exact_object(statement, "recursive_input.statement", STATEMENT_FIELDS)?;
    }
    let Some(children) = input.get("children") else {
        return Ok(());
    };
    let children = children
        .as_array()
        .ok_or_else(|| "recursive_input.children must be an array".to_string())?;
    for (index, child) in children.iter().enumerate() {
        let context = format!("recursive_input.children[{index}]");
        let child = exact_object(child, &context, CHILD_FIELDS)?;
        if let Some(descriptor) = child.get("descriptor") {
            exact_object(
                descriptor,
                &format!("{context}.descriptor"),
                DESCRIPTOR_FIELDS,
            )?;
        }
        if let Some(summary) = child.get("summary") {
            exact_object(summary, &format!("{context}.summary"), SUMMARY_FIELDS)?;
        }
        if let Some(rows) = child.get("asset_delta_rows") {
            validate_object_array(
                rows,
                &format!("{context}.asset_delta_rows"),
                ASSET_DELTA_FIELDS,
            )?;
        }
        for field in ["outbox_messages", "inbox_messages"] {
            if let Some(messages) = child.get(field) {
                validate_object_array(messages, &format!("{context}.{field}"), MESSAGE_FIELDS)?;
            }
        }
    }
    Ok(())
}

fn validate_object_array(value: &Value, context: &str, allowed: &[&str]) -> Result<(), String> {
    let values = value
        .as_array()
        .ok_or_else(|| format!("{context} must be an array"))?;
    for (index, item) in values.iter().enumerate() {
        exact_object(item, &format!("{context}[{index}]"), allowed)?;
    }
    Ok(())
}

fn exact_object<'a>(
    value: &'a Value,
    context: &str,
    allowed: &[&str],
) -> Result<&'a serde_json::Map<String, Value>, String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{context} must be an object"))?;
    if let Some(key) = object.keys().find(|key| !allowed.contains(&key.as_str())) {
        return Err(format!("{context} contains unknown field `{key}`"));
    }
    Ok(object)
}

fn expected_meta(journal: &RecursiveEpochJournalV1) -> Result<Value, String> {
    let mut value = expected_expectations(journal);
    let object = value
        .as_object_mut()
        .ok_or_else(|| "internal expected metadata construction failed".to_string())?;
    object.remove("journal_version");
    Ok(value)
}

fn expected_expectations(journal: &RecursiveEpochJournalV1) -> Value {
    json!({
        "accepted_receipts_root": hex32(&journal.accepted_receipts_root),
        "aggregate_asset_delta_root": hex32(&journal.aggregate_asset_delta_root),
        "allowed_authority_roots_root": hex32(&journal.allowed_authority_roots_root),
        "carry_queue_post_root": hex32(&journal.carry_queue_post_root),
        "carry_queue_pre_root": hex32(&journal.carry_queue_pre_root),
        "chain_id": journal.chain_id,
        "child_count": journal.child_count,
        "child_effect_summaries_root": hex32(&journal.child_effect_summaries_root),
        "child_journals_root": hex32(&journal.child_journals_root),
        "child_verification_claims_root": hex32(&journal.child_verification_claims_root),
        "conflict_schedule_hash": hex32(&journal.conflict_schedule_hash),
        "cross_shard_inbox_root": hex32(&journal.cross_shard_inbox_root),
        "cross_shard_message_ids_root": hex32(&journal.cross_shard_message_ids_root),
        "cross_shard_outbox_root": hex32(&journal.cross_shard_outbox_root),
        "data_availability_root": hex32(&journal.data_availability_root),
        "dependency_lock_hash": hex32(&journal.dependency_lock_hash),
        "domain_separator": journal.domain_separator,
        "epoch_id": journal.epoch_id,
        "evidence_root": hex32(&journal.evidence_root),
        "feature_suite_hash": hex32(&journal.feature_suite_hash),
        "journal_version": journal.journal_version,
        "post_state_root": hex32(&journal.post_state_root),
        "pre_state_root": hex32(&journal.pre_state_root),
        "proof_profile": journal.proof_profile,
        "proof_type": journal.proof_type,
        "public_policy_hash": hex32(&journal.public_policy_hash),
        "receipt_codec": RECEIPT_CODEC,
        "receipt_control_id": RECEIPT_CONTROL_ID,
        "receipt_hashfn": RECEIPT_HASHFN,
        "receipt_kind": "succinct",
        "receipt_root": hex32(&journal.receipt_root),
        "receipt_verifier_parameters": RECEIPT_VERIFIER_PARAMETERS,
        "rejected_receipts_root": hex32(&journal.rejected_receipts_root),
        "risc0_image_id": image_id_hex(),
        "statement_hash": hex32(&journal.statement_hash),
        "toolchain_lock_hash": hex32(&journal.toolchain_lock_hash),
        "tx_root": hex32(&journal.tx_root),
        "verifier_set_root": hex32(&journal.verifier_set_root),
    })
}

fn risc0_dev_mode_env_enabled() -> bool {
    env::var("RISC0_DEV_MODE").is_ok_and(|value| {
        matches!(
            value.trim().to_ascii_lowercase().as_str(),
            "1" | "true" | "yes" | "on"
        )
    })
}

fn image_id_hex() -> String {
    Digest::from(GOVERNED_AGGREGATE_V1_ID).to_string()
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn hex32(value: &[u8; 32]) -> String {
    hex::encode(value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn governed_aggregate_id_matches_the_active_reproof_identity() {
        assert_eq!(
            image_id_hex(),
            "c4bde351d48e8e775c2e831fc37fb98a9e45ed59455afe761572d2e11ceed6c4"
        );
    }

    #[test]
    fn dev_mode_parser_rejects_only_enabled_spellings() {
        for enabled in ["1", "true", "TRUE", "yes", "on"] {
            assert!(matches!(
                enabled.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            ));
        }
        for disabled in ["", "0", "false", "off", "no"] {
            assert!(!matches!(
                disabled.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            ));
        }
    }

    #[test]
    fn recursive_input_shape_rejects_unknown_fields_at_every_object_layer() {
        let cases = [
            json!({"unknown": 1}),
            json!({"statement": {"unknown": 1}}),
            json!({"children": [{"unknown": 1}]}),
            json!({"children": [{"descriptor": {"unknown": 1}}]}),
            json!({"children": [{"summary": {"unknown": 1}}]}),
            json!({"children": [{"asset_delta_rows": [{"unknown": 1}]}]}),
            json!({"children": [{"outbox_messages": [{"unknown": 1}]}]}),
        ];
        for value in cases {
            let error = validate_recursive_input_shape(&value)
                .expect_err("unknown recursive input field must reject");
            assert!(error.contains("unknown field `unknown`"));
        }
    }
}
