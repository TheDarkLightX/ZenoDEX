use serde_json::{Map, Value};

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

const LEAF_WRAPPER_FIELDS: &[&str] = &[
    "chain_id",
    "epoch_id",
    "lane_id",
    "risc0_image_id",
    "public_policy_hash",
    "feature_suite_hash",
    "dependency_lock_hash",
    "toolchain_lock_hash",
];

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
    validate_leaf_wrapper(value, "spot_recursive_leaf_input", "spot_input")
}

pub(super) fn validate_perps_leaf(value: &Value) -> Result<(), String> {
    validate_leaf_wrapper(value, "perps_np_recursive_leaf_input", "perps_input")
}

pub(super) fn validate_zusd_leaf(value: &Value) -> Result<(), String> {
    validate_leaf_wrapper(value, "zusd_recursive_leaf_input", "zusd_input")
}

fn validate_leaf_wrapper(value: &Value, context: &str, payload_field: &str) -> Result<(), String> {
    let mut allowed = LEAF_WRAPPER_FIELDS.to_vec();
    allowed.push(payload_field);
    exact_object(value, context, &allowed).map(|_| ())
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
