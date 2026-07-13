//! Strict, scoped Spot proof authority binding for ZenoLedger integration.
//!
//! The ordinary `tau_state_proof_verify` schema remains a diagnostic verifier
//! with optional outer bindings. This module requires every currently
//! checkable outer binding and returns facts only after consuming the private
//! `VerifiedSpotReceipt` minted by the single cryptographic verification path.
//! It deliberately does not equate the Spot application hash with the
//! ZenoLedger state root; that relation needs a future typed state bridge.

use base64::Engine;
use serde_json::{json, Map, Value};
use sha2::{Digest as ShaDigest, Sha256};

use super::{
    hex_lower, hex_prefixed, hex_u32_words, parse_block_txs, parse_hex32, try_verify_spot,
    txs_commitment_v1, ProofReceiptKind, ReceiptSecurityProfile, VerifiedSpotReceipt, PROOF_TYPE,
    RECEIPT_CODEC_V1, TAU_STATE_PROOF_GUEST_ID,
};

pub(super) const SPOT_AUTHORITY_REQUEST_SCHEMA_V1: &str =
    "zenodex.zeno_ledger.risc0_spot_authority_verify.v1";
pub(super) const SPOT_AUTHORITY_RESULT_SCHEMA_V1: &str =
    "zenodex.zeno_ledger.authenticated_spot_proof_facts.v1";
const AUTHORITY_EXPECTATIONS_SCHEMA_V1: &str =
    "zenodex.zeno_ledger.risc0_spot_authority_expectations.v1";
const SPOT_PROOF_PROFILE_V1: &str = "risc0_spot_state_transition_v1";
const HEADER_SCHEMA_V0: &str = "zenodex/zeno_ledger/header/v0";
const REPLAY_CONFIG_SCHEMA_V0: &str = "zenodex/zeno_ledger/replay_engine_config/v0";
const REPLAY_CONFIG_PROFILE_V0: &str = "bounded_dex_engine_v0";

const REQUEST_KEYS: &[&str] = &[
    "schema",
    "schema_version",
    "state_hash",
    "proof",
    "block",
    "tau_state",
    "context",
    "trusted_route_price_interval_authority_policy_root",
    "ledger_header",
    "replay_config",
    "authority_expectations",
];
const CONTEXT_KEYS: &[&str] = &[
    "app_hash_pre",
    "block_timestamp",
    "pre_nonces",
    "protocol_fee_share_bps",
    "protocol_fee_recipient_pubkey",
    "tx_execution_order",
    "route_price_intervals",
    "route_price_interval_authority",
    "route_price_interval_authority_policy",
    "route_price_interval_max_width_bps",
    "shared_pool_frontier_signature_certificates",
];
const PROOF_KEYS: &[&str] = &[
    "schema",
    "schema_version",
    "state_hash",
    "proof_type",
    "proof",
    "meta",
];
const SPOT_META_KEYS: &[&str] = &[
    "risc0_image_id",
    "txs_commitment",
    "tx_execution_order_commitment",
    "ingress_commitment",
    "pre_nonce_root",
    "post_nonce_root",
    "accepted_receipts_root",
    "pre_app_hash",
    "post_app_hash",
    "protocol_fee_share_bps",
    "protocol_fee_recipient_pubkey",
    "route_price_interval_count",
    "route_price_intervals_root",
    "route_price_interval_authority_root",
    "route_price_interval_authority_policy_root",
    "route_price_interval_max_width_bps",
    "shared_pool_frontier_signature_certificate_count",
    "shared_pool_frontier_signature_certificates_root",
    "receipt_codec",
    "receipt_kind",
    "receipt_verifier_parameters",
    "receipt_hashfn",
    "receipt_control_id",
];
const HEADER_ROOT_KEYS: &[&str] = &[
    "prev_header_hash",
    "sequencer_set_hash",
    "ingress_root",
    "tx_root",
    "pre_state_root",
    "post_state_root",
    "app_hash",
    "evidence_root",
    "body_root",
    "data_availability_root",
    "proof_journal_hash",
    "config_digest",
    "module_versions_digest",
    "signature_set_root",
];
const EXPECTATION_KEYS: &[&str] = &[
    "schema",
    "authority_manifest_sha256",
    "verifier_registry_id",
    "verifier_registry_entry_id",
    "strict_result_schema",
    "policy_id",
    "chain_id",
    "height",
    "valid_from_height",
    "valid_until_height",
    "proof_profile",
    "expected_image_id",
    "receipt_codec",
    "receipt_kind",
    "receipt_verifier_parameters",
    "receipt_hashfn",
    "receipt_control_id",
    "canonical_header_hash",
    "proof_metadata_hash",
    "proof_commitment",
    "config_digest",
    "module_versions_digest",
    "data_availability_root",
    "public_policy_hash",
    "feature_suite_hash",
    "dependency_lock_hash",
    "toolchain_lock_hash",
    "block_timestamp",
];
const FACT_KEYS: &[&str] = &[
    "schema",
    "authority_scope",
    "authority_manifest_sha256",
    "verifier_registry_id",
    "verifier_registry_entry_id",
    "policy_id",
    "chain_id",
    "height",
    "valid_from_height",
    "valid_until_height",
    "proof_profile",
    "actual_image_id",
    "receipt_codec",
    "receipt_kind",
    "receipt_verifier_parameters",
    "receipt_hashfn",
    "receipt_control_id",
    "canonical_receipt_sha256",
    "canonical_journal_sha256",
    "canonical_journal_base64",
    "state_hash",
    "spot_pre_app_hash",
    "spot_post_app_hash",
    "spot_pre_nonce_root",
    "spot_post_nonce_root",
    "spot_ingress_commitment",
    "spot_accepted_receipts_root",
    "spot_tx_execution_order_commitment",
    "spot_route_price_intervals_root",
    "spot_route_price_interval_authority_root",
    "spot_route_price_interval_authority_policy_root",
    "spot_shared_pool_frontier_signature_certificates_root",
    "block_timestamp",
    "ledger_header_time_ms",
    "canonical_header_hash",
    "proof_metadata_hash",
    "proof_commitment",
    "ledger_pre_state_root",
    "ledger_post_state_root",
    "ledger_app_hash",
    "ledger_evidence_root",
    "ledger_body_root",
    "ledger_data_availability_root",
    "ledger_proof_journal_hash",
    "config_digest",
    "module_versions_digest",
    "public_policy_hash",
    "feature_suite_hash",
    "dependency_lock_hash",
    "toolchain_lock_hash",
    "transaction_domain_bridge",
    "block_timestamp_directly_committed_in_spot_journal",
    "chain_and_height_directly_committed_in_spot_journal",
    "spot_app_hash_equals_zeno_ledger_state_root_verified",
    "data_availability_verified",
    "proof_metadata_object_verified",
    "serialized_facts_are_opaque_capability",
    "governed_policy_registry_join_verified",
    "settlement_authority",
    "production_authority",
];

#[derive(Clone, Debug, PartialEq, Eq)]
struct TransactionDomainBridgeV1 {
    tx_count: usize,
    canonical_transaction_batch_sha256: String,
    spot_txs_commitment: String,
    zeno_ledger_tx_root: String,
}

#[derive(Clone, Debug)]
struct AuthorityExpectationsV1 {
    authority_manifest_sha256: String,
    verifier_registry_id: String,
    verifier_registry_entry_id: String,
    policy_id: String,
    chain_id: String,
    height: u64,
    valid_from_height: u64,
    valid_until_height: u64,
    expected_image_id: String,
    receipt_kind: ProofReceiptKind,
    receipt_verifier_parameters: String,
    receipt_hashfn: Option<String>,
    receipt_control_id: Option<String>,
    canonical_header_hash: String,
    proof_metadata_hash: String,
    proof_commitment: String,
    config_digest: String,
    module_versions_digest: String,
    data_availability_root: String,
    public_policy_hash: String,
    feature_suite_hash: String,
    dependency_lock_hash: String,
    toolchain_lock_hash: String,
    block_timestamp: u64,
}

pub(super) fn verification_response(req: &Value) -> Value {
    match verify(req) {
        Ok(facts) => json!({
            "schema": SPOT_AUTHORITY_RESULT_SCHEMA_V1,
            "schema_version": 1,
            "ok": true,
            "authenticated_spot_proof_facts": facts,
        }),
        Err(error) => json!({
            "schema": SPOT_AUTHORITY_RESULT_SCHEMA_V1,
            "schema_version": 1,
            "ok": false,
            "error": error,
        }),
    }
}

fn verify(req: &Value) -> Result<Value, String> {
    let request = exact_object(req, "request", REQUEST_KEYS)?;
    expect_string(
        request,
        "schema",
        SPOT_AUTHORITY_REQUEST_SCHEMA_V1,
        "request",
    )?;
    expect_u64(request, "schema_version", 1, "request")?;
    let state_hash = canonical_root(request.get("state_hash"), "state_hash")?;
    validate_strict_proof_shape(request_value(request, "proof")?, &state_hash)?;
    exact_object(
        request_value(request, "block")?,
        "block",
        &["header", "transactions"],
    )?;
    exact_object(
        request_value(request, "block")?
            .get("header")
            .ok_or_else(|| "block.header missing".to_string())?,
        "block.header",
        &["timestamp"],
    )?;
    exact_object(
        request_value(request, "tau_state")?,
        "tau_state",
        &["app_hash"],
    )?;
    let context = exact_object(request_value(request, "context")?, "context", CONTEXT_KEYS)?;
    validate_strict_context_shape(context)?;

    let expectations = parse_expectations(request_value(request, "authority_expectations")?)?;
    let header = validate_header(request_value(request, "ledger_header")?)?;
    let config_digest = validate_replay_config(
        request_value(request, "replay_config")?,
        &expectations.chain_id,
    )?;
    let canonical_header_hash = hash_v0("header_v0", request_value(request, "ledger_header")?)?;
    bind_outer_expectations(
        &expectations,
        header,
        &canonical_header_hash,
        &config_digest,
    )?;

    let proof = request_value(request, "proof")?;
    let expected_state_hash = parse_hex32(&state_hash)?;
    let verified = try_verify_spot(req, proof, expected_state_hash)?;
    bind_verified_spot(req, verified, expectations, header, config_digest)
}

fn bind_verified_spot(
    req: &Value,
    verified: VerifiedSpotReceipt,
    expectations: AuthorityExpectationsV1,
    header: &Map<String, Value>,
    config_digest: String,
) -> Result<Value, String> {
    let VerifiedSpotReceipt {
        receipt,
        journal,
        security_profile,
    } = verified;
    bind_receipt_profile(&expectations, &security_profile)?;

    let block = req
        .get("block")
        .and_then(Value::as_object)
        .ok_or_else(|| "block must be an object".to_string())?;
    let block_timestamp = block
        .get("header")
        .and_then(Value::as_object)
        .and_then(|value| value.get("timestamp"))
        .and_then(Value::as_u64)
        .ok_or_else(|| "block.header.timestamp missing/invalid".to_string())?;
    if block_timestamp != expectations.block_timestamp {
        return Err("authority expectations block_timestamp mismatch".to_string());
    }
    let context_timestamp = req
        .get("context")
        .and_then(Value::as_object)
        .and_then(|value| value.get("block_timestamp"))
        .and_then(Value::as_u64)
        .ok_or_else(|| "context.block_timestamp missing/invalid".to_string())?;
    if context_timestamp != block_timestamp {
        return Err("context.block_timestamp mismatch".to_string());
    }

    let transactions = block
        .get("transactions")
        .and_then(Value::as_array)
        .ok_or_else(|| "block.transactions must be a list".to_string())?;
    validate_strict_transactions(transactions, block_timestamp)?;
    let bridge = transaction_domain_bridge(transactions)?;
    if bridge.spot_txs_commitment != hex_prefixed(&journal.txs_commitment) {
        return Err("Spot transaction commitment bridge mismatch".to_string());
    }
    if header_string(header, "tx_root")? != bridge.zeno_ledger_tx_root {
        return Err("ledger_header.tx_root mismatch".to_string());
    }

    let trusted_route_policy_root = canonical_root(
        req.get("trusted_route_price_interval_authority_policy_root"),
        "trusted_route_price_interval_authority_policy_root",
    )?;
    if trusted_route_policy_root
        != hex_prefixed(&journal.route_price_interval_authority_policy_root)
    {
        return Err("trusted route price authority policy root mismatch".to_string());
    }

    let receipt_bytes = serde_json::to_vec(&receipt)
        .map_err(|error| format!("failed to canonicalize verified receipt: {error}"))?;
    let journal_bytes = receipt.journal.bytes.as_ref();
    let canonical_header_hash = hash_v0("header_v0", &Value::Object(header.clone()))?;
    let proof_commitment = hash_v0(
        "risc0_tau_state_proof_envelope_v0",
        req.get("proof")
            .ok_or_else(|| "proof missing after strict verification".to_string())?,
    )?;
    if proof_commitment != expectations.proof_commitment {
        return Err("authority proof_commitment mismatch".to_string());
    }

    let mut facts = object_from_json(json!({
        "schema": SPOT_AUTHORITY_RESULT_SCHEMA_V1,
        "authority_scope": "source_receipt_and_exact_outer_binding_v1",
        "authority_manifest_sha256": expectations.authority_manifest_sha256,
        "verifier_registry_id": expectations.verifier_registry_id,
        "verifier_registry_entry_id": expectations.verifier_registry_entry_id,
        "policy_id": expectations.policy_id,
        "chain_id": expectations.chain_id,
        "height": expectations.height,
        "valid_from_height": expectations.valid_from_height,
        "valid_until_height": expectations.valid_until_height,
        "proof_profile": SPOT_PROOF_PROFILE_V1,
        "actual_image_id": compiled_image_id(),
        "receipt_codec": RECEIPT_CODEC_V1,
        "receipt_kind": security_profile.kind.as_str(),
        "receipt_verifier_parameters": security_profile.verifier_parameters,
        "receipt_hashfn": security_profile.hashfn,
        "receipt_control_id": security_profile.control_id,
        "canonical_receipt_sha256": sha256_hex(&receipt_bytes),
        "canonical_journal_sha256": sha256_hex(journal_bytes),
        "canonical_journal_base64": base64::engine::general_purpose::STANDARD.encode(journal_bytes),
    }))?;
    facts.extend(object_from_json(json!({
        "state_hash": hex_prefixed(&journal.state_hash),
        "spot_pre_app_hash": hex_prefixed(&journal.pre_app_hash),
        "spot_post_app_hash": hex_prefixed(&journal.post_app_hash),
        "spot_pre_nonce_root": hex_prefixed(&journal.pre_nonce_root),
        "spot_post_nonce_root": hex_prefixed(&journal.post_nonce_root),
        "spot_ingress_commitment": hex_prefixed(&journal.ingress_commitment),
        "spot_accepted_receipts_root": hex_prefixed(&journal.accepted_receipts_root),
        "spot_tx_execution_order_commitment": hex_prefixed(&journal.tx_execution_order_commitment),
        "spot_route_price_intervals_root": hex_prefixed(&journal.route_price_intervals_root),
        "spot_route_price_interval_authority_root": hex_prefixed(&journal.route_price_interval_authority_root),
        "spot_route_price_interval_authority_policy_root": hex_prefixed(&journal.route_price_interval_authority_policy_root),
        "spot_shared_pool_frontier_signature_certificates_root": hex_prefixed(&journal.shared_pool_frontier_signature_certificates_root),
        "block_timestamp": block_timestamp,
        "ledger_header_time_ms": header_u64(header, "time_ms")?,
    }))?);
    facts.extend(object_from_json(json!({
        "canonical_header_hash": canonical_header_hash,
        "proof_metadata_hash": expectations.proof_metadata_hash,
        "proof_commitment": proof_commitment,
        "ledger_pre_state_root": header_string(header, "pre_state_root")?,
        "ledger_post_state_root": header_string(header, "post_state_root")?,
        "ledger_app_hash": header_string(header, "app_hash")?,
        "ledger_evidence_root": header_string(header, "evidence_root")?,
        "ledger_body_root": header_string(header, "body_root")?,
        "ledger_data_availability_root": header_string(header, "data_availability_root")?,
        "ledger_proof_journal_hash": header_string(header, "proof_journal_hash")?,
        "config_digest": config_digest,
        "module_versions_digest": expectations.module_versions_digest,
        "public_policy_hash": expectations.public_policy_hash,
        "feature_suite_hash": expectations.feature_suite_hash,
        "dependency_lock_hash": expectations.dependency_lock_hash,
        "toolchain_lock_hash": expectations.toolchain_lock_hash,
        "transaction_domain_bridge": {
            "schema": "zenodex.zeno_ledger.spot_transaction_domain_bridge.v1",
            "tx_count": bridge.tx_count,
            "canonical_transaction_batch_sha256": bridge.canonical_transaction_batch_sha256,
            "spot_txs_commitment": bridge.spot_txs_commitment,
            "zeno_ledger_tx_root": bridge.zeno_ledger_tx_root,
            "roots_are_domain_distinct": true,
        },
    }))?);
    facts.extend(object_from_json(json!({
        "block_timestamp_directly_committed_in_spot_journal": false,
        "chain_and_height_directly_committed_in_spot_journal": false,
        "spot_app_hash_equals_zeno_ledger_state_root_verified": false,
        "data_availability_verified": false,
        "proof_metadata_object_verified": false,
        "serialized_facts_are_opaque_capability": false,
        "governed_policy_registry_join_verified": false,
        "settlement_authority": false,
        "production_authority": false,
    }))?);
    let value = Value::Object(facts);
    exact_object(&value, "authenticated_spot_proof_facts", FACT_KEYS)?;
    Ok(value)
}

fn validate_strict_proof_shape(value: &Value, expected_state_hash: &str) -> Result<(), String> {
    let proof = exact_object(value, "proof", PROOF_KEYS)?;
    expect_string(proof, "schema", "tau_state_proof", "proof")?;
    expect_u64(proof, "schema_version", 1, "proof")?;
    expect_string(proof, "proof_type", PROOF_TYPE, "proof")?;
    required_nonempty_string(proof, "proof", "proof")?;
    let proof_state_hash = proof
        .get("state_hash")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof.state_hash must be a string".to_string())?;
    if parse_hex32(proof_state_hash)? != parse_hex32(expected_state_hash)? {
        return Err("proof.state_hash mismatch".to_string());
    }
    exact_object(
        proof
            .get("meta")
            .ok_or_else(|| "proof.meta missing".to_string())?,
        "proof.meta",
        SPOT_META_KEYS,
    )?;
    Ok(())
}

fn validate_strict_context_shape(context: &Map<String, Value>) -> Result<(), String> {
    require_array(
        context.get("tx_execution_order"),
        "context.tx_execution_order",
    )?;
    let intervals = require_array(
        context.get("route_price_intervals"),
        "context.route_price_intervals",
    )?;
    for (index, interval) in intervals.iter().enumerate() {
        exact_object(
            interval,
            &format!("context.route_price_intervals[{index}]"),
            &["asset", "low_e8", "point_e8", "high_e8"],
        )?;
    }
    validate_optional_exact_object(
        context.get("route_price_interval_authority"),
        "context.route_price_interval_authority",
        &[
            "schema",
            "source_id",
            "source_root",
            "price_timestamp",
            "max_staleness_seconds",
            "route_price_intervals_root",
        ],
    )?;
    if let Some(policy_value) = context.get("route_price_interval_authority_policy") {
        if !policy_value.is_null() {
            let policy = exact_object(
                policy_value,
                "context.route_price_interval_authority_policy",
                &["schema", "policy_id", "sources"],
            )?;
            let sources = require_array(
                policy.get("sources"),
                "context.route_price_interval_authority_policy.sources",
            )?;
            for (index, source) in sources.iter().enumerate() {
                exact_object(
                    source,
                    &format!("context.route_price_interval_authority_policy.sources[{index}]"),
                    &[
                        "source_id",
                        "source_root",
                        "verification_root",
                        "verification_status",
                    ],
                )?;
            }
        }
    }
    let certificates = require_array(
        context.get("shared_pool_frontier_signature_certificates"),
        "context.shared_pool_frontier_signature_certificates",
    )?;
    for (index, certificate) in certificates.iter().enumerate() {
        validate_frontier_certificate_shape(certificate, index)?;
    }
    Ok(())
}

fn validate_strict_transactions(
    transactions: &[Value],
    block_timestamp: u64,
) -> Result<(), String> {
    for (index, transaction) in transactions.iter().enumerate() {
        let name = format!("block.transactions[{index}]");
        let tx = transaction
            .as_object()
            .ok_or_else(|| format!("{name} must be an object"))?;
        reject_unknown_keys(
            tx,
            &name,
            &[
                "tx_id",
                "block_timestamp",
                "tx_sender_pubkey",
                "sender_pubkey",
                "nonce",
                "operations",
            ],
        )?;
        if !tx.contains_key("tx_sender_pubkey") && !tx.contains_key("sender_pubkey") {
            return Err(format!("{name} sender identity missing"));
        }
        if !tx.contains_key("nonce") || !tx.contains_key("operations") {
            return Err(format!("{name} nonce/operations missing"));
        }
        if let Some(timestamp) = tx.get("block_timestamp") {
            if timestamp.as_u64() != Some(block_timestamp) {
                return Err(format!("{name}.block_timestamp mismatch"));
            }
        }
        let operations = tx
            .get("operations")
            .and_then(Value::as_object)
            .ok_or_else(|| format!("{name}.operations must be an object"))?;
        reject_unknown_keys(operations, &format!("{name}.operations"), &["2", "4"])?;
        if let Some(intents) = operations.get("2") {
            validate_strict_intents(intents, &format!("{name}.operations['2']"))?;
        }
        if let Some(faucet) = operations.get("4") {
            validate_strict_faucet(faucet, &format!("{name}.operations['4']"))?;
        }
    }
    Ok(())
}

fn validate_strict_intents(value: &Value, name: &str) -> Result<(), String> {
    let intents = value
        .as_array()
        .ok_or_else(|| format!("{name} must be a list"))?;
    for (index, entry) in intents.iter().enumerate() {
        let entry_name = format!("{name}[{index}]");
        let intent_value = if let Some(pair) = entry.as_array() {
            if pair.len() != 2 || !(pair[1].is_null() || pair[1].is_string()) {
                return Err(format!("{entry_name} signed pair schema mismatch"));
            }
            &pair[0]
        } else {
            entry
        };
        let intent = intent_value
            .as_object()
            .ok_or_else(|| format!("{entry_name} intent must be an object"))?;
        let kind = intent
            .get("kind")
            .and_then(Value::as_str)
            .ok_or_else(|| format!("{entry_name}.kind missing"))?;
        let mut allowed = vec![
            "module",
            "version",
            "kind",
            "intent_id",
            "sender_pubkey",
            "deadline",
            "salt",
        ];
        match kind {
            "CREATE_POOL" => allowed.extend(["asset0", "asset1", "fee_bps", "amount0", "amount1"]),
            "SWAP_EXACT_IN" => allowed.extend([
                "pool_id",
                "asset_in",
                "asset_out",
                "amount_in",
                "min_amount_out",
                "recipient",
            ]),
            "ADD_LIQUIDITY" => allowed.extend([
                "pool_id",
                "amount0_desired",
                "amount1_desired",
                "amount0_min",
                "amount1_min",
                "recipient",
            ]),
            "REMOVE_LIQUIDITY" => allowed.extend([
                "pool_id",
                "lp_amount",
                "amount0_min",
                "amount1_min",
                "recipient",
            ]),
            "SWAP_EXACT_OUT" => allowed.extend([
                "pool_id",
                "asset_in",
                "asset_out",
                "amount_out",
                "max_amount_in",
                "recipient",
            ]),
            "ROUTE_EXACT_IN" | "ROUTE_EXACT_OUT" => allowed.extend([
                "quote_receipt_hash",
                "asset_in",
                "asset_out",
                "leg_indices",
                "legs",
                "total_amount_in",
                "total_min_amount_out",
                "total_amount_out",
                "total_max_amount_in",
                "recipient",
            ]),
            _ => return Err(format!("{entry_name}.kind unsupported")),
        }
        reject_unknown_keys(intent, &entry_name, &allowed)?;
        if matches!(kind, "ROUTE_EXACT_IN" | "ROUTE_EXACT_OUT") {
            validate_route_legs(intent.get("legs"), &format!("{entry_name}.legs"))?;
        }
    }
    Ok(())
}

fn validate_route_legs(value: Option<&Value>, name: &str) -> Result<(), String> {
    let legs = require_array(value, name)?;
    for (leg_index, leg) in legs.iter().enumerate() {
        let leg_name = format!("{name}[{leg_index}]");
        let leg = exact_object(leg, &leg_name, &["hops"])?;
        let hops = require_array(leg.get("hops"), &format!("{leg_name}.hops"))?;
        for (hop_index, hop) in hops.iter().enumerate() {
            exact_object(hop, &format!("{leg_name}.hops[{hop_index}]"), &["pool_id"])?;
        }
    }
    Ok(())
}

fn validate_strict_faucet(value: &Value, name: &str) -> Result<(), String> {
    let faucet = exact_object(value, name, &["mint"])?;
    let mint = require_array(faucet.get("mint"), &format!("{name}.mint"))?;
    for (index, entry) in mint.iter().enumerate() {
        if let Some(tuple) = entry.as_array() {
            if tuple.len() != 3 {
                return Err(format!("{name}.mint[{index}] tuple length mismatch"));
            }
        } else {
            exact_object(
                entry,
                &format!("{name}.mint[{index}]"),
                &["pubkey", "asset", "amount"],
            )?;
        }
    }
    Ok(())
}

fn reject_unknown_keys(
    object: &Map<String, Value>,
    name: &str,
    allowed: &[&str],
) -> Result<(), String> {
    if let Some(unknown) = object.keys().find(|key| !allowed.contains(&key.as_str())) {
        return Err(format!("{name} unknown field {unknown}"));
    }
    Ok(())
}

fn validate_frontier_certificate_shape(value: &Value, index: usize) -> Result<(), String> {
    let name = format!("context.shared_pool_frontier_signature_certificates[{index}]");
    let certificate = exact_object(
        value,
        &name,
        &[
            "schema",
            "pool_id",
            "fee_bps",
            "row_states",
            "victims",
            "signatures",
            "claimed_frontier_states",
        ],
    )?;
    for key in ["row_states", "claimed_frontier_states"] {
        let states = require_array(certificate.get(key), &format!("{name}.{key}"))?;
        for (state_index, state) in states.iter().enumerate() {
            exact_object(
                state,
                &format!("{name}.{key}[{state_index}]"),
                &["reserve_a_atoms", "reserve_b_atoms"],
            )?;
        }
    }
    let victims = require_array(certificate.get("victims"), &format!("{name}.victims"))?;
    for (victim_index, victim) in victims.iter().enumerate() {
        exact_object(
            victim,
            &format!("{name}.victims[{victim_index}]"),
            &["direction", "amount_in_atoms", "min_out_atoms"],
        )?;
    }
    let signatures = require_array(certificate.get("signatures"), &format!("{name}.signatures"))?;
    for (signature_index, signature) in signatures.iter().enumerate() {
        let signature_name = format!("{name}.signatures[{signature_index}]");
        let signature = exact_object(
            signature,
            &signature_name,
            &["state", "suffix_signature_masks"],
        )?;
        exact_object(
            signature
                .get("state")
                .ok_or_else(|| format!("{signature_name}.state missing"))?,
            &format!("{signature_name}.state"),
            &["reserve_a_atoms", "reserve_b_atoms"],
        )?;
        require_array(
            signature.get("suffix_signature_masks"),
            &format!("{signature_name}.suffix_signature_masks"),
        )?;
    }
    Ok(())
}

fn validate_optional_exact_object(
    value: Option<&Value>,
    name: &str,
    keys: &[&str],
) -> Result<(), String> {
    match value {
        Some(Value::Null) => Ok(()),
        Some(value) => exact_object(value, name, keys).map(|_| ()),
        None => Err(format!("{name} missing")),
    }
}

fn require_array<'a>(value: Option<&'a Value>, name: &str) -> Result<&'a [Value], String> {
    value
        .and_then(Value::as_array)
        .map(Vec::as_slice)
        .ok_or_else(|| format!("{name} must be a list"))
}

fn parse_expectations(value: &Value) -> Result<AuthorityExpectationsV1, String> {
    let obj = exact_object(value, "authority_expectations", EXPECTATION_KEYS)?;
    expect_string(
        obj,
        "schema",
        AUTHORITY_EXPECTATIONS_SCHEMA_V1,
        "authority_expectations",
    )?;
    expect_string(
        obj,
        "strict_result_schema",
        SPOT_AUTHORITY_RESULT_SCHEMA_V1,
        "authority_expectations",
    )?;
    expect_string(
        obj,
        "proof_profile",
        SPOT_PROOF_PROFILE_V1,
        "authority_expectations",
    )?;
    expect_string(
        obj,
        "receipt_codec",
        RECEIPT_CODEC_V1,
        "authority_expectations",
    )?;
    let height = required_u64(obj, "height", "authority_expectations")?;
    let valid_from_height = required_u64(obj, "valid_from_height", "authority_expectations")?;
    let valid_until_height = required_u64(obj, "valid_until_height", "authority_expectations")?;
    if valid_from_height > valid_until_height
        || height < valid_from_height
        || height > valid_until_height
    {
        return Err("authority expectations height outside validity interval".to_string());
    }
    let receipt_kind_raw = required_nonempty_string(obj, "receipt_kind", "authority_expectations")?;
    let receipt_kind = ProofReceiptKind::parse(&receipt_kind_raw)
        .ok_or_else(|| "authority_expectations.receipt_kind unsupported".to_string())?;
    if receipt_kind == ProofReceiptKind::Fake {
        return Err("authority expectations reject fake receipt kind".to_string());
    }
    Ok(AuthorityExpectationsV1 {
        authority_manifest_sha256: canonical_bare_sha256(
            obj.get("authority_manifest_sha256"),
            "authority_expectations.authority_manifest_sha256",
        )?,
        verifier_registry_id: canonical_root(
            obj.get("verifier_registry_id"),
            "authority_expectations.verifier_registry_id",
        )?,
        verifier_registry_entry_id: canonical_root(
            obj.get("verifier_registry_entry_id"),
            "authority_expectations.verifier_registry_entry_id",
        )?,
        policy_id: canonical_root(obj.get("policy_id"), "authority_expectations.policy_id")?,
        chain_id: required_token(obj, "chain_id", "authority_expectations")?,
        height,
        valid_from_height,
        valid_until_height,
        expected_image_id: canonical_root(
            obj.get("expected_image_id"),
            "authority_expectations.expected_image_id",
        )?,
        receipt_kind,
        receipt_verifier_parameters: required_nonempty_string(
            obj,
            "receipt_verifier_parameters",
            "authority_expectations",
        )?,
        receipt_hashfn: optional_string(obj, "receipt_hashfn", "authority_expectations")?,
        receipt_control_id: optional_string(obj, "receipt_control_id", "authority_expectations")?,
        canonical_header_hash: canonical_root(
            obj.get("canonical_header_hash"),
            "authority_expectations.canonical_header_hash",
        )?,
        proof_metadata_hash: canonical_root(
            obj.get("proof_metadata_hash"),
            "authority_expectations.proof_metadata_hash",
        )?,
        proof_commitment: canonical_root(
            obj.get("proof_commitment"),
            "authority_expectations.proof_commitment",
        )?,
        config_digest: canonical_root(
            obj.get("config_digest"),
            "authority_expectations.config_digest",
        )?,
        module_versions_digest: canonical_root(
            obj.get("module_versions_digest"),
            "authority_expectations.module_versions_digest",
        )?,
        data_availability_root: canonical_root(
            obj.get("data_availability_root"),
            "authority_expectations.data_availability_root",
        )?,
        public_policy_hash: canonical_root(
            obj.get("public_policy_hash"),
            "authority_expectations.public_policy_hash",
        )?,
        feature_suite_hash: canonical_root(
            obj.get("feature_suite_hash"),
            "authority_expectations.feature_suite_hash",
        )?,
        dependency_lock_hash: canonical_root(
            obj.get("dependency_lock_hash"),
            "authority_expectations.dependency_lock_hash",
        )?,
        toolchain_lock_hash: canonical_root(
            obj.get("toolchain_lock_hash"),
            "authority_expectations.toolchain_lock_hash",
        )?,
        block_timestamp: required_u64(obj, "block_timestamp", "authority_expectations")?,
    })
}

fn validate_header(value: &Value) -> Result<&Map<String, Value>, String> {
    let mut keys = vec!["schema", "chain_id", "height", "time_ms"];
    keys.extend_from_slice(HEADER_ROOT_KEYS);
    let obj = exact_object(value, "ledger_header", &keys)?;
    expect_string(obj, "schema", HEADER_SCHEMA_V0, "ledger_header")?;
    required_token(obj, "chain_id", "ledger_header")?;
    required_u64(obj, "height", "ledger_header")?;
    required_u64(obj, "time_ms", "ledger_header")?;
    for key in HEADER_ROOT_KEYS {
        canonical_root(obj.get(*key), &format!("ledger_header.{key}"))?;
    }
    Ok(obj)
}

fn validate_replay_config(value: &Value, expected_chain_id: &str) -> Result<String, String> {
    let obj = exact_object(value, "replay_config", &["schema", "profile", "config"])?;
    expect_string(obj, "schema", REPLAY_CONFIG_SCHEMA_V0, "replay_config")?;
    expect_string(obj, "profile", REPLAY_CONFIG_PROFILE_V0, "replay_config")?;
    let config = obj
        .get("config")
        .and_then(Value::as_object)
        .ok_or_else(|| "replay_config.config must be an object".to_string())?;
    let chain_id = required_token(config, "chain_id", "replay_config.config")?;
    if chain_id != expected_chain_id {
        return Err("replay_config.config.chain_id mismatch".to_string());
    }
    hash_v0("zeno_ledger_replay_engine_config_v0", value)
}

fn bind_outer_expectations(
    expectations: &AuthorityExpectationsV1,
    header: &Map<String, Value>,
    canonical_header_hash: &str,
    config_digest: &str,
) -> Result<(), String> {
    if header_string(header, "chain_id")? != expectations.chain_id {
        return Err("authority/header chain_id mismatch".to_string());
    }
    if header_u64(header, "height")? != expectations.height {
        return Err("authority/header height mismatch".to_string());
    }
    if header_u64(header, "time_ms")? / 1_000 != expectations.block_timestamp {
        return Err("authority/header block_timestamp mismatch".to_string());
    }
    if canonical_header_hash != expectations.canonical_header_hash {
        return Err("authority canonical_header_hash mismatch".to_string());
    }
    if config_digest != expectations.config_digest
        || header_string(header, "config_digest")? != expectations.config_digest
    {
        return Err("authority/header replay config digest mismatch".to_string());
    }
    if header_string(header, "module_versions_digest")? != expectations.module_versions_digest {
        return Err("authority/header module_versions_digest mismatch".to_string());
    }
    if header_string(header, "proof_journal_hash")? != expectations.proof_metadata_hash {
        return Err("authority/header proof_metadata_hash mismatch".to_string());
    }
    if header_string(header, "data_availability_root")? != expectations.data_availability_root {
        return Err("authority/header data_availability_root mismatch".to_string());
    }
    if expectations.expected_image_id != compiled_image_id() {
        return Err("authority expected_image_id mismatch".to_string());
    }
    Ok(())
}

fn bind_receipt_profile(
    expectations: &AuthorityExpectationsV1,
    actual: &ReceiptSecurityProfile,
) -> Result<(), String> {
    if actual.kind != expectations.receipt_kind {
        return Err("authority receipt_kind mismatch".to_string());
    }
    if actual.verifier_parameters != expectations.receipt_verifier_parameters {
        return Err("authority receipt_verifier_parameters mismatch".to_string());
    }
    if actual.hashfn != expectations.receipt_hashfn {
        return Err("authority receipt_hashfn mismatch".to_string());
    }
    if actual.control_id != expectations.receipt_control_id {
        return Err("authority receipt_control_id mismatch".to_string());
    }
    Ok(())
}

fn transaction_domain_bridge(transactions: &[Value]) -> Result<TransactionDomainBridgeV1, String> {
    let transaction_value = Value::Array(transactions.to_vec());
    let parsed_spot_txs = parse_block_txs(Some(&transaction_value))?;
    let spot_commitment = txs_commitment_v1(&parsed_spot_txs);
    let tx_hashes = transactions
        .iter()
        .map(|tx| hash_v0("tx_v0", tx))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(TransactionDomainBridgeV1 {
        tx_count: transactions.len(),
        canonical_transaction_batch_sha256: sha256_hex(&canonical_json_bytes(&transaction_value)?),
        spot_txs_commitment: hex_prefixed(&spot_commitment),
        zeno_ledger_tx_root: merkle_root_v0("tx_root_v0", &tx_hashes)?,
    })
}

fn merkle_root_v0(domain: &str, leaves: &[String]) -> Result<String, String> {
    if leaves.is_empty() {
        return Ok(hex_prefixed(&sha256_bytes(&domain_sep_bytes(
            "zeno_ledger_empty_merkle",
        ))));
    }
    let mut nodes = Vec::with_capacity(leaves.len());
    for (index, leaf) in leaves.iter().enumerate() {
        let leaf_bytes = parse_hex32(leaf)?;
        let mut payload = domain_sep_bytes(&format!("zeno_ledger_leaf_index_{domain}"));
        let encoded_index =
            u64::try_from(index).map_err(|_| "transaction Merkle index exceeds u64".to_string())?;
        payload.extend(encode_uvarint(encoded_index));
        payload.extend(leaf_bytes);
        nodes.push(parse_hex32(&hash_v0(
            &format!("merkle_leaf_{domain}"),
            ValueOrBytes::Bytes(payload),
        )?)?);
    }
    let mut level = 0u64;
    while nodes.len() > 1 {
        let mut next = Vec::with_capacity(nodes.len().div_ceil(2));
        for (pair_index, pair) in nodes.chunks(2).enumerate() {
            let left = pair[0];
            let right = pair.get(1).copied().unwrap_or(left);
            let mut payload = domain_sep_bytes(&format!("zeno_ledger_node_index_{domain}"));
            payload.extend(encode_uvarint(level));
            let encoded_pair_index = u64::try_from(pair_index)
                .map_err(|_| "transaction Merkle pair index exceeds u64".to_string())?;
            payload.extend(encode_uvarint(encoded_pair_index));
            payload.extend(left);
            payload.extend(right);
            next.push(parse_hex32(&hash_v0(
                &format!("merkle_node_{domain}"),
                ValueOrBytes::Bytes(payload),
            )?)?);
        }
        nodes = next;
        level = level
            .checked_add(1)
            .ok_or_else(|| "Merkle level overflow".to_string())?;
    }
    Ok(hex_prefixed(&nodes[0]))
}

enum ValueOrBytes<'a> {
    Value(&'a Value),
    Bytes(Vec<u8>),
}

impl<'a> From<&'a Value> for ValueOrBytes<'a> {
    fn from(value: &'a Value) -> Self {
        Self::Value(value)
    }
}

fn hash_v0<'a>(domain: &str, value: impl Into<ValueOrBytes<'a>>) -> Result<String, String> {
    let mut payload = domain_sep_bytes(&format!("zeno_ledger_{domain}"));
    let bytes = match value.into() {
        ValueOrBytes::Value(value) => canonical_json_bytes(value)?,
        ValueOrBytes::Bytes(bytes) => bytes,
    };
    let encoded_len = u64::try_from(bytes.len())
        .map_err(|_| "ZenoLedger hash payload length exceeds u64".to_string())?;
    payload.extend(encode_uvarint(encoded_len));
    payload.extend(bytes);
    Ok(hex_prefixed(&sha256_bytes(&payload)))
}

fn canonical_json_bytes(value: &Value) -> Result<Vec<u8>, String> {
    reject_noncanonical_numbers(value)?;
    reject_non_ascii_strings(value)?;
    serde_json::to_vec(value).map_err(|error| format!("canonical JSON encoding failed: {error}"))
}

fn reject_noncanonical_numbers(value: &Value) -> Result<(), String> {
    match value {
        Value::Number(number) if !is_integer_number(number) => {
            Err("canonical ZenoLedger JSON rejects non-integer numbers".to_string())
        }
        Value::Array(values) => values.iter().try_for_each(reject_noncanonical_numbers),
        Value::Object(values) => values.values().try_for_each(reject_noncanonical_numbers),
        _ => Ok(()),
    }
}

fn is_integer_number(number: &serde_json::Number) -> bool {
    let raw = number.to_string();
    let digits = raw.strip_prefix('-').unwrap_or(&raw);
    !digits.is_empty() && digits.bytes().all(|byte| byte.is_ascii_digit())
}

fn reject_non_ascii_strings(value: &Value) -> Result<(), String> {
    match value {
        Value::String(value) if !value.is_ascii() => {
            Err("strict ZenoLedger bridge rejects non-ASCII strings".to_string())
        }
        Value::Array(values) => values.iter().try_for_each(reject_non_ascii_strings),
        Value::Object(values) => {
            if values.keys().any(|key| !key.is_ascii()) {
                return Err("strict ZenoLedger bridge rejects non-ASCII object keys".to_string());
            }
            values.values().try_for_each(reject_non_ascii_strings)
        }
        _ => Ok(()),
    }
}

fn domain_sep_bytes(label: &str) -> Vec<u8> {
    format!("zenodex:{label}:v1\0").into_bytes()
}

fn encode_uvarint(mut value: u64) -> Vec<u8> {
    let mut out = Vec::new();
    loop {
        let mut byte = value.to_le_bytes()[0] & 0x7f;
        value >>= 7;
        if value != 0 {
            byte |= 0x80;
        }
        out.push(byte);
        if value == 0 {
            return out;
        }
    }
}

fn sha256_bytes(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex_lower(&sha256_bytes(bytes))
}

fn compiled_image_id() -> String {
    format!(
        "0x{}",
        hex_u32_words(TAU_STATE_PROOF_GUEST_ID).trim_start_matches("0x")
    )
}

fn exact_object<'a>(
    value: &'a Value,
    name: &str,
    expected_keys: &[&str],
) -> Result<&'a Map<String, Value>, String> {
    let obj = value
        .as_object()
        .ok_or_else(|| format!("{name} must be an object"))?;
    if obj.len() != expected_keys.len() || expected_keys.iter().any(|key| !obj.contains_key(*key)) {
        return Err(format!("{name} keys mismatch"));
    }
    Ok(obj)
}

fn object_from_json(value: Value) -> Result<Map<String, Value>, String> {
    value
        .as_object()
        .cloned()
        .ok_or_else(|| "internal JSON object construction failed".to_string())
}

fn request_value<'a>(request: &'a Map<String, Value>, key: &str) -> Result<&'a Value, String> {
    request
        .get(key)
        .ok_or_else(|| format!("request.{key} missing"))
}

fn required_nonempty_string(
    obj: &Map<String, Value>,
    key: &str,
    name: &str,
) -> Result<String, String> {
    let value = obj
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{name}.{key} must be a string"))?;
    if value.is_empty() {
        return Err(format!("{name}.{key} must be non-empty"));
    }
    Ok(value.to_string())
}

fn required_token(obj: &Map<String, Value>, key: &str, name: &str) -> Result<String, String> {
    let value = required_nonempty_string(obj, key, name)?;
    if !value
        .bytes()
        .all(|byte| byte.is_ascii_alphanumeric() || b"._:/-".contains(&byte))
    {
        return Err(format!("{name}.{key} contains unsupported characters"));
    }
    Ok(value)
}

fn optional_string(
    obj: &Map<String, Value>,
    key: &str,
    name: &str,
) -> Result<Option<String>, String> {
    match obj.get(key) {
        Some(Value::Null) => Ok(None),
        Some(Value::String(value)) if !value.is_empty() => Ok(Some(value.clone())),
        _ => Err(format!("{name}.{key} must be null or a non-empty string")),
    }
}

fn required_u64(obj: &Map<String, Value>, key: &str, name: &str) -> Result<u64, String> {
    obj.get(key)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("{name}.{key} must be a u64"))
}

fn expect_u64(
    obj: &Map<String, Value>,
    key: &str,
    expected: u64,
    name: &str,
) -> Result<(), String> {
    if required_u64(obj, key, name)? != expected {
        return Err(format!("{name}.{key} mismatch"));
    }
    Ok(())
}

fn expect_string(
    obj: &Map<String, Value>,
    key: &str,
    expected: &str,
    name: &str,
) -> Result<(), String> {
    if required_nonempty_string(obj, key, name)? != expected {
        return Err(format!("{name}.{key} mismatch"));
    }
    Ok(())
}

fn canonical_root(value: Option<&Value>, name: &str) -> Result<String, String> {
    let raw = value
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{name} must be a string"))?;
    let parsed = parse_hex32(raw)?;
    let canonical = hex_prefixed(&parsed);
    if raw != canonical {
        return Err(format!(
            "{name} must be canonical lowercase 0x-prefixed hex"
        ));
    }
    Ok(canonical)
}

fn canonical_bare_sha256(value: Option<&Value>, name: &str) -> Result<String, String> {
    let raw = value
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{name} must be a string"))?;
    if raw.len() != 64
        || raw
            .bytes()
            .any(|byte| !byte.is_ascii_hexdigit() || byte.is_ascii_uppercase())
    {
        return Err(format!("{name} must be lowercase 64-character hex"));
    }
    Ok(raw.to_string())
}

fn header_string(header: &Map<String, Value>, key: &str) -> Result<String, String> {
    header
        .get(key)
        .and_then(Value::as_str)
        .map(str::to_string)
        .ok_or_else(|| format!("ledger_header.{key} must be a string"))
}

fn header_u64(header: &Map<String, Value>, key: &str) -> Result<u64, String> {
    required_u64(header, key, "ledger_header")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn transaction_bridge_matches_python_empty_root_vector() {
        let bridge = transaction_domain_bridge(&[]).unwrap();
        assert_eq!(bridge.tx_count, 0);
        assert_eq!(
            bridge.zeno_ledger_tx_root,
            "0x4e5d2c3b446d54875575d71538f8ca04efcd6279947e35ae160df966e4c184a1"
        );
        assert_ne!(bridge.spot_txs_commitment, bridge.zeno_ledger_tx_root);
    }

    #[test]
    fn canonical_ledger_tx_root_matches_python_vector() {
        let transactions = vec![json!({
            "nonce": 0,
            "operations": {},
            "tx_sender_pubkey": "alice",
        })];
        let bridge = transaction_domain_bridge(&transactions).unwrap();
        assert_eq!(
            bridge.canonical_transaction_batch_sha256,
            "b9aadaf37e24c81d1c48fcea20c396864273da583b9bb78265c8606ede9e087a"
        );
        assert_eq!(
            bridge.zeno_ledger_tx_root,
            "0x6598d05bb464bd9ef3d69049759580cb570a3fe187d1d26d6c1cc9ba54fd739a"
        );
        assert_ne!(bridge.spot_txs_commitment, bridge.zeno_ledger_tx_root);
    }

    #[test]
    fn canonical_ledger_tx_root_matches_python_odd_leaf_vector() {
        let transactions = vec![
            json!({
                "nonce": 0,
                "operations": {},
                "tx_sender_pubkey": "alice",
            }),
            json!({
                "nonce": 1,
                "operations": {},
                "tx_sender_pubkey": "bob",
            }),
            json!({
                "nonce": 2,
                "operations": {},
                "tx_sender_pubkey": "carol",
            }),
        ];
        let bridge = transaction_domain_bridge(&transactions).unwrap();
        assert_eq!(
            bridge.canonical_transaction_batch_sha256,
            "5c8fe15ff0ec665f0fdf96f736792271d4f77f403e5a8f017bf6d1634f74c8ab"
        );
        assert_eq!(
            bridge.zeno_ledger_tx_root,
            "0xc8b0a70568abe1457a94690301523a7fcfb2711e2e98cf89221e447c1e4ea96d"
        );
        assert_ne!(bridge.spot_txs_commitment, bridge.zeno_ledger_tx_root);
    }

    #[test]
    fn transaction_bridge_rejects_non_ascii_strings() {
        let transactions = vec![json!({
            "nonce": 0,
            "operations": {},
            "tx_sender_pubkey": "alïce",
        })];
        assert_eq!(
            transaction_domain_bridge(&transactions).unwrap_err(),
            "strict ZenoLedger bridge rejects non-ASCII strings"
        );
    }

    #[test]
    fn strict_transactions_reject_unknown_fields_at_each_nested_boundary() {
        let base = json!({
            "nonce": 0,
            "operations": {},
            "tx_sender_pubkey": "alice",
        });
        validate_strict_transactions(std::slice::from_ref(&base), 123).unwrap();

        let mut expanded_transaction = base.clone();
        expanded_transaction["verified"] = Value::Bool(true);
        assert_eq!(
            validate_strict_transactions(&[expanded_transaction], 123).unwrap_err(),
            "block.transactions[0] unknown field verified"
        );

        let mut expanded_operations = base.clone();
        expanded_operations["operations"]["99"] = json!([]);
        assert_eq!(
            validate_strict_transactions(&[expanded_operations], 123).unwrap_err(),
            "block.transactions[0].operations unknown field 99"
        );

        let expanded_intent = json!({
            "nonce": 0,
            "operations": {
                "2": [{
                    "module": "TauSwap",
                    "version": "0.1",
                    "kind": "CREATE_POOL",
                    "intent_id": "intent-1",
                    "sender_pubkey": "alice",
                    "deadline": 999,
                    "asset0": "A",
                    "asset1": "B",
                    "fee_bps": 30,
                    "amount0": 1,
                    "amount1": 2,
                    "verified": true,
                }],
            },
            "tx_sender_pubkey": "alice",
        });
        assert_eq!(
            validate_strict_transactions(&[expanded_intent], 123).unwrap_err(),
            "block.transactions[0].operations['2'][0] unknown field verified"
        );
    }

    #[test]
    fn strict_transactions_reject_per_transaction_timestamp_mismatch() {
        let transaction = json!({
            "block_timestamp": 124,
            "nonce": 0,
            "operations": {},
            "tx_sender_pubkey": "alice",
        });
        assert_eq!(
            validate_strict_transactions(&[transaction], 123).unwrap_err(),
            "block.transactions[0].block_timestamp mismatch"
        );
    }

    #[test]
    fn expectations_reject_boolean_or_unknown_authority_fields() {
        let mut value = test_expectations();
        value["production_authority"] = Value::Bool(true);
        assert_eq!(
            parse_expectations(&value).unwrap_err(),
            "authority_expectations keys mismatch"
        );
        let mut value = test_expectations();
        value["height"] = Value::Bool(true);
        assert_eq!(
            parse_expectations(&value).unwrap_err(),
            "authority_expectations.height must be a u64"
        );
    }

    #[test]
    fn expectations_reject_out_of_range_height_and_fake_profile() {
        let mut value = test_expectations();
        value["height"] = json!(12);
        assert_eq!(
            parse_expectations(&value).unwrap_err(),
            "authority expectations height outside validity interval"
        );
        let mut value = test_expectations();
        value["receipt_kind"] = json!("fake");
        assert_eq!(
            parse_expectations(&value).unwrap_err(),
            "authority expectations reject fake receipt kind"
        );
    }

    #[test]
    fn outer_binding_accepts_exact_header_config_and_governed_expectations() {
        let (header, config, expectations_value) = consistent_outer_fixture();
        let expectations = parse_expectations(&expectations_value).unwrap();
        let header_obj = validate_header(&header).unwrap();
        let config_digest = validate_replay_config(&config, "tau-test").unwrap();
        let header_hash = hash_v0("header_v0", &header).unwrap();
        bind_outer_expectations(&expectations, header_obj, &header_hash, &config_digest).unwrap();
    }

    #[test]
    fn outer_binding_mutations_fail_closed_at_their_named_boundary() {
        let (header, config, expectations_value) = consistent_outer_fixture();
        let expectations = parse_expectations(&expectations_value).unwrap();

        let mut wrong_chain = header.clone();
        wrong_chain["chain_id"] = json!("tau-other");
        let wrong_chain_obj = validate_header(&wrong_chain).unwrap();
        let wrong_chain_hash = hash_v0("header_v0", &wrong_chain).unwrap();
        let config_digest = validate_replay_config(&config, "tau-test").unwrap();
        assert_eq!(
            bind_outer_expectations(
                &expectations,
                wrong_chain_obj,
                &wrong_chain_hash,
                &config_digest,
            )
            .unwrap_err(),
            "authority/header chain_id mismatch"
        );

        let mut wrong_config = config.clone();
        wrong_config["config"]["chain_id"] = json!("tau-other");
        assert_eq!(
            validate_replay_config(&wrong_config, "tau-test").unwrap_err(),
            "replay_config.config.chain_id mismatch"
        );

        let mut expanded_header = header;
        expanded_header["verified"] = Value::Bool(true);
        assert_eq!(
            validate_header(&expanded_header).unwrap_err(),
            "ledger_header keys mismatch"
        );

        let (mut wrong_time_header, config, expectations_value) = consistent_outer_fixture();
        wrong_time_header["time_ms"] = json!(124000);
        let expectations = parse_expectations(&expectations_value).unwrap();
        let wrong_time_obj = validate_header(&wrong_time_header).unwrap();
        let wrong_time_hash = hash_v0("header_v0", &wrong_time_header).unwrap();
        let config_digest = validate_replay_config(&config, "tau-test").unwrap();
        assert_eq!(
            bind_outer_expectations(
                &expectations,
                wrong_time_obj,
                &wrong_time_hash,
                &config_digest,
            )
            .unwrap_err(),
            "authority/header block_timestamp mismatch"
        );
    }

    #[test]
    fn strict_spot_authority_consumes_the_single_verified_receipt_path_once() {
        let main_source = include_str!("main.rs");
        let spot_section = main_source
            .split_once("fn try_verify_spot(")
            .unwrap()
            .1
            .split_once("fn try_verify_perps_np(")
            .unwrap()
            .0;
        assert_eq!(
            spot_section
                .matches("decode_verified_receipt_from_proof(proof)?")
                .count(),
            1
        );

        let authority_source = include_str!("spot_authority.rs");
        let verification_section = authority_source
            .split_once("fn verify(req: &Value)")
            .unwrap()
            .1
            .split_once("fn bind_verified_spot(")
            .unwrap()
            .0;
        assert_eq!(verification_section.matches("try_verify_spot(").count(), 1);
        assert!(!verification_section.contains("decode_verified_receipt_from_proof"));
    }

    #[test]
    fn strict_response_and_fact_key_contracts_are_exact() {
        let rejected = verification_response(&json!({}));
        exact_object(
            &rejected,
            "response",
            &["schema", "schema_version", "ok", "error"],
        )
        .unwrap();
        assert_eq!(rejected["schema"], SPOT_AUTHORITY_RESULT_SCHEMA_V1);
        assert_eq!(rejected["ok"], false);

        let unique: std::collections::BTreeSet<_> = FACT_KEYS.iter().copied().collect();
        assert_eq!(unique.len(), FACT_KEYS.len());
        assert!(unique.contains("serialized_facts_are_opaque_capability"));
        assert!(unique.contains("governed_policy_registry_join_verified"));
    }

    #[test]
    fn strict_context_rejects_nested_unknown_fields() {
        let mut context = json!({
            "app_hash_pre": format!("0x{}", "11".repeat(32)),
            "block_timestamp": 123,
            "pre_nonces": {},
            "protocol_fee_share_bps": 0,
            "protocol_fee_recipient_pubkey": null,
            "tx_execution_order": [],
            "route_price_intervals": [{
                "asset": "USDC",
                "low_e8": 1,
                "point_e8": 1,
                "high_e8": 1,
            }],
            "route_price_interval_authority": null,
            "route_price_interval_authority_policy": null,
            "route_price_interval_max_width_bps": null,
            "shared_pool_frontier_signature_certificates": [],
        });
        validate_strict_context_shape(context.as_object().unwrap()).unwrap();
        context["route_price_intervals"][0]["verified"] = Value::Bool(true);
        assert_eq!(
            validate_strict_context_shape(context.as_object().unwrap()).unwrap_err(),
            "context.route_price_intervals[0] keys mismatch"
        );
    }

    fn consistent_outer_fixture() -> (Value, Value, Value) {
        let config = json!({
            "schema": REPLAY_CONFIG_SCHEMA_V0,
            "profile": REPLAY_CONFIG_PROFILE_V0,
            "config": {"chain_id": "tau-test"},
        });
        let config_digest = validate_replay_config(&config, "tau-test").unwrap();
        let zero = format!("0x{}", "00".repeat(32));
        let module_versions = format!("0x{}", "77".repeat(32));
        let data_availability = format!("0x{}", "88".repeat(32));
        let header = json!({
            "schema": HEADER_SCHEMA_V0,
            "chain_id": "tau-test",
            "height": 7,
            "time_ms": 123000,
            "prev_header_hash": zero,
            "sequencer_set_hash": format!("0x{}", "01".repeat(32)),
            "ingress_root": format!("0x{}", "02".repeat(32)),
            "tx_root": format!("0x{}", "03".repeat(32)),
            "pre_state_root": format!("0x{}", "04".repeat(32)),
            "post_state_root": format!("0x{}", "05".repeat(32)),
            "app_hash": format!("0x{}", "06".repeat(32)),
            "evidence_root": format!("0x{}", "07".repeat(32)),
            "body_root": format!("0x{}", "08".repeat(32)),
            "data_availability_root": data_availability,
            "proof_journal_hash": format!("0x{}", "09".repeat(32)),
            "config_digest": config_digest,
            "module_versions_digest": module_versions,
            "signature_set_root": format!("0x{}", "0a".repeat(32)),
        });
        let mut expectations = test_expectations();
        expectations["expected_image_id"] = json!(compiled_image_id());
        expectations["canonical_header_hash"] = json!(hash_v0("header_v0", &header).unwrap());
        expectations["config_digest"] = json!(header["config_digest"].clone());
        expectations["module_versions_digest"] = json!(header["module_versions_digest"].clone());
        expectations["data_availability_root"] = json!(header["data_availability_root"].clone());
        expectations["proof_metadata_hash"] = json!(header["proof_journal_hash"].clone());
        (header, config, expectations)
    }

    fn test_expectations() -> Value {
        json!({
            "schema": AUTHORITY_EXPECTATIONS_SCHEMA_V1,
            "authority_manifest_sha256": "11".repeat(32),
            "verifier_registry_id": format!("0x{}", "22".repeat(32)),
            "verifier_registry_entry_id": format!("0x{}", "33".repeat(32)),
            "strict_result_schema": SPOT_AUTHORITY_RESULT_SCHEMA_V1,
            "policy_id": format!("0x{}", "10".repeat(32)),
            "chain_id": "tau-test",
            "height": 7,
            "valid_from_height": 1,
            "valid_until_height": 10,
            "proof_profile": SPOT_PROOF_PROFILE_V1,
            "expected_image_id": format!("0x{}", "44".repeat(32)),
            "receipt_codec": RECEIPT_CODEC_V1,
            "receipt_kind": "composite",
            "receipt_verifier_parameters": "params",
            "receipt_hashfn": null,
            "receipt_control_id": null,
            "canonical_header_hash": format!("0x{}", "55".repeat(32)),
            "proof_metadata_hash": format!("0x{}", "56".repeat(32)),
            "proof_commitment": format!("0x{}", "57".repeat(32)),
            "config_digest": format!("0x{}", "66".repeat(32)),
            "module_versions_digest": format!("0x{}", "77".repeat(32)),
            "data_availability_root": format!("0x{}", "88".repeat(32)),
            "public_policy_hash": format!("0x{}", "99".repeat(32)),
            "feature_suite_hash": format!("0x{}", "aa".repeat(32)),
            "dependency_lock_hash": format!("0x{}", "bb".repeat(32)),
            "toolchain_lock_hash": format!("0x{}", "cc".repeat(32)),
            "block_timestamp": 123,
        })
    }
}
