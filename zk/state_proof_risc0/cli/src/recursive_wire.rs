use serde_json::{Map, Value};
use tau_state_proof_risc0_shared::PROOF_TYPE_RECURSIVE;

mod application;

pub(super) const RECURSIVE_VERIFY_REQUEST_FIELDS_V1: &[&str] = &[
    "schema",
    "schema_version",
    "state_hash",
    "proof",
    "recursive_input",
    "recursive_expectations",
];

pub(super) const RECURSIVE_PROOF_FIELDS_V1: &[&str] = &[
    "schema",
    "schema_version",
    "state_hash",
    "proof_type",
    "proof",
    "meta",
];

pub(super) const RECURSIVE_PROOF_META_FIELDS_V1: &[&str] = &[
    "risc0_image_id",
    "receipt_kind",
    "proof_type",
    "domain_separator",
    "chain_id",
    "epoch_id",
    "proof_profile",
    "statement_hash",
    "verifier_set_root",
    "allowed_authority_roots_root",
    "child_verification_claims_root",
    "child_journals_root",
    "child_effect_summaries_root",
    "child_count",
    "pre_state_root",
    "post_state_root",
    "tx_root",
    "evidence_root",
    "receipt_root",
    "accepted_receipts_root",
    "rejected_receipts_root",
    "aggregate_asset_delta_root",
    "cross_shard_outbox_root",
    "cross_shard_inbox_root",
    "cross_shard_message_ids_root",
    "carry_queue_pre_root",
    "carry_queue_post_root",
    "conflict_schedule_hash",
    "data_availability_root",
    "public_policy_hash",
    "feature_suite_hash",
    "dependency_lock_hash",
    "toolchain_lock_hash",
    "receipt_codec",
    "receipt_verifier_parameters",
    "receipt_hashfn",
    "receipt_control_id",
];

pub(super) const COMPOSITION_FIELDS: &[&str] = &[
    "statement",
    "allowed_verifier_ids",
    "allowed_authority_roots",
    "children",
];

pub(super) const STATEMENT_FIELDS: &[&str] = &[
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

pub(super) const CHILD_FIELDS: &[&str] = &[
    "descriptor",
    "child_journal_bytes",
    "summary",
    "asset_delta_rows",
    "outbox_messages",
    "inbox_messages",
    "accepted_receipt_ids",
    "rejected_receipt_ids",
];

pub(super) const DESCRIPTOR_FIELDS: &[&str] = &[
    "child_verification_claim_hash",
    "child_journal_hash",
    "child_effect_summary_hash",
    "child_statement_hash",
    "child_image_id",
    "child_verifier_id",
    "child_profile",
];

pub(super) const SUMMARY_FIELDS: &[&str] = &[
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

pub(super) const ASSET_DELTA_FIELDS: &[&str] = &[
    "asset_id",
    "debit_atoms",
    "credit_atoms",
    "authorized_mint_atoms",
    "authorized_burn_atoms",
    "authority_root",
];

pub(super) const MESSAGE_FIELDS: &[&str] = &[
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

pub(super) const LEAF_WRAPPER_FIELDS: &[&str] = &[
    "chain_id",
    "epoch_id",
    "lane_id",
    "risc0_image_id",
    "public_policy_hash",
    "feature_suite_hash",
    "dependency_lock_hash",
    "toolchain_lock_hash",
];

pub(super) fn validate_recursive_verify_v1(request: &Value, proof: &Value) -> Result<(), String> {
    let request_context = "recursive_verify_request";
    let request_object =
        exact_required_object(request, request_context, RECURSIVE_VERIFY_REQUEST_FIELDS_V1)?;
    expect_exact_string(
        request_object,
        request_context,
        "schema",
        "tau_state_proof_verify",
    )?;
    expect_exact_u64(request_object, request_context, "schema_version", 1)?;
    require_string(request_object, request_context, "state_hash")?;
    require_object(request_object, request_context, "recursive_input")?;
    require_object(request_object, request_context, "recursive_expectations")?;

    require_object(request_object, request_context, "proof")?;
    if request_object.get("proof") != Some(proof) {
        return Err("recursive_verify_request.proof argument mismatch".to_string());
    }
    let proof_context = "recursive_verify_request.proof";
    let proof_object = exact_required_object(proof, proof_context, RECURSIVE_PROOF_FIELDS_V1)?;
    expect_exact_string(proof_object, proof_context, "schema", "tau_state_proof")?;
    expect_exact_u64(proof_object, proof_context, "schema_version", 1)?;
    require_string(proof_object, proof_context, "state_hash")?;
    expect_exact_string(
        proof_object,
        proof_context,
        "proof_type",
        PROOF_TYPE_RECURSIVE,
    )?;
    require_string(proof_object, proof_context, "proof")?;

    let meta_context = "recursive_verify_request.proof.meta";
    let meta = exact_required_object(
        proof_object
            .get("meta")
            .ok_or_else(|| format!("{proof_context} missing required field `meta`"))?,
        meta_context,
        RECURSIVE_PROOF_META_FIELDS_V1,
    )?;
    for field in RECURSIVE_PROOF_META_FIELDS_V1 {
        match *field {
            "epoch_id" | "child_count" => {
                require_u64(meta, meta_context, field)?;
            }
            _ => {
                require_string(meta, meta_context, field)?;
            }
        }
    }
    expect_exact_string(meta, meta_context, "proof_type", PROOF_TYPE_RECURSIVE)?;
    Ok(())
}

pub(super) fn validate_composition(value: &Value) -> Result<(), String> {
    let object = exact_object(value, "recursive_input", COMPOSITION_FIELDS)?;
    if let Some(statement) = object.get("statement") {
        exact_object(statement, "recursive_input.statement", STATEMENT_FIELDS)?;
    }
    if let Some(children) = object.get("children") {
        for (index, child) in exact_array(children, "recursive_input.children")?
            .iter()
            .enumerate()
        {
            validate_child(child, index)?;
        }
    }
    Ok(())
}

pub(super) fn validate_summary(value: &Value, context: &str) -> Result<(), String> {
    exact_object(value, context, SUMMARY_FIELDS).map(|_| ())
}

pub(super) fn validate_spot_leaf(value: &Value) -> Result<(), String> {
    validate_leaf_wrapper(
        value,
        "spot_recursive_leaf_input",
        "spot_input",
        application::validate_spot,
    )
}

pub(super) fn validate_perps_leaf(value: &Value) -> Result<(), String> {
    validate_leaf_wrapper(
        value,
        "perps_np_recursive_leaf_input",
        "perps_input",
        application::validate_perps,
    )
}

pub(super) fn validate_zusd_leaf(value: &Value) -> Result<(), String> {
    validate_leaf_wrapper(
        value,
        "zusd_recursive_leaf_input",
        "zusd_input",
        application::validate_zusd,
    )
}

fn validate_leaf_wrapper(
    value: &Value,
    context: &str,
    payload_field: &str,
    validate_payload: fn(&Value, &str) -> Result<(), String>,
) -> Result<(), String> {
    let mut allowed = LEAF_WRAPPER_FIELDS.to_vec();
    allowed.push(payload_field);
    let object = exact_required_object(value, context, &allowed)?;
    application::require_string_field(object, context, "chain_id")?;
    application::require_u64_field(object, context, "epoch_id")?;
    application::require_string_field(object, context, "lane_id")?;
    application::require_u32_words_field(object, context, "risc0_image_id")?;
    for field in [
        "public_policy_hash",
        "feature_suite_hash",
        "dependency_lock_hash",
        "toolchain_lock_hash",
    ] {
        application::require_bytes32_field(object, context, field)?;
    }
    let payload = application::required_field(object, context, payload_field)?;
    validate_payload(payload, &format!("{context}.{payload_field}"))
}

fn validate_child(value: &Value, index: usize) -> Result<(), String> {
    let context = format!("recursive_input.children[{index}]");
    let object = exact_object(value, &context, CHILD_FIELDS)?;
    if let Some(descriptor) = object.get("descriptor") {
        exact_object(
            descriptor,
            &format!("{context}.descriptor"),
            DESCRIPTOR_FIELDS,
        )?;
    }
    if let Some(summary) = object.get("summary") {
        validate_summary(summary, &format!("{context}.summary"))?;
    }
    if let Some(rows) = object.get("asset_delta_rows") {
        validate_array_objects(
            rows,
            &format!("{context}.asset_delta_rows"),
            ASSET_DELTA_FIELDS,
        )?;
    }
    for field in ["outbox_messages", "inbox_messages"] {
        if let Some(messages) = object.get(field) {
            validate_array_objects(messages, &format!("{context}.{field}"), MESSAGE_FIELDS)?;
        }
    }
    Ok(())
}

fn validate_array_objects(value: &Value, context: &str, allowed: &[&str]) -> Result<(), String> {
    for (index, item) in exact_array(value, context)?.iter().enumerate() {
        exact_object(item, &format!("{context}[{index}]"), allowed)?;
    }
    Ok(())
}

fn exact_array<'a>(value: &'a Value, context: &str) -> Result<&'a [Value], String> {
    value
        .as_array()
        .map(Vec::as_slice)
        .ok_or_else(|| format!("{context} must be a list"))
}

fn exact_object<'a>(
    value: &'a Value,
    context: &str,
    allowed: &[&str],
) -> Result<&'a Map<String, Value>, String> {
    let object = value
        .as_object()
        .ok_or_else(|| format!("{context} must be an object"))?;
    for key in object.keys() {
        if !allowed.contains(&key.as_str()) {
            return Err(format!("{context} contains unknown field `{key}`"));
        }
    }
    Ok(object)
}

fn exact_required_object<'a>(
    value: &'a Value,
    context: &str,
    allowed: &[&str],
) -> Result<&'a Map<String, Value>, String> {
    let object = exact_object(value, context, allowed)?;
    if let Some(field) = allowed.iter().find(|field| !object.contains_key(**field)) {
        return Err(format!("{context} missing required field `{field}`"));
    }
    Ok(object)
}

fn require_object<'a>(
    object: &'a Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<&'a Map<String, Value>, String> {
    object
        .get(field)
        .and_then(Value::as_object)
        .ok_or_else(|| format!("{context}.{field} must be an object"))
}

fn require_string<'a>(
    object: &'a Map<String, Value>,
    context: &str,
    field: &str,
) -> Result<&'a str, String> {
    object
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{context}.{field} must be a string"))
}

fn require_u64(object: &Map<String, Value>, context: &str, field: &str) -> Result<u64, String> {
    object
        .get(field)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("{context}.{field} must be an unsigned 64-bit integer"))
}

fn expect_exact_string(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
    expected: &str,
) -> Result<(), String> {
    let actual = require_string(object, context, field)?;
    if actual != expected {
        return Err(format!("{context}.{field} must equal `{expected}`"));
    }
    Ok(())
}

fn expect_exact_u64(
    object: &Map<String, Value>,
    context: &str,
    field: &str,
    expected: u64,
) -> Result<(), String> {
    if require_u64(object, context, field)? != expected {
        return Err(format!("{context}.{field} must equal {expected}"));
    }
    Ok(())
}
