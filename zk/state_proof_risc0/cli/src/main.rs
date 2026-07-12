use std::io::{Read, Write};

use base64::Engine;
use risc0_zkvm::{
    compute_image_id, default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt,
};
use serde::de::DeserializeOwned;
use serde_json::{json, Value};

mod recursive_wire;
mod strict_json;

use tau_state_proof_risc0_methods::{
    TAU_STATE_PROOF_RISC0_AGGREGATE_ELF as TAU_STATE_PROOF_AGGREGATE_ELF,
    TAU_STATE_PROOF_RISC0_AGGREGATE_ID as TAU_STATE_PROOF_AGGREGATE_ID,
    TAU_STATE_PROOF_RISC0_GUEST_ELF as TAU_STATE_PROOF_GUEST_ELF,
    TAU_STATE_PROOF_RISC0_GUEST_ID as TAU_STATE_PROOF_GUEST_ID,
    TAU_STATE_PROOF_RISC0_PERPS_NP_LEAF_ELF as TAU_STATE_PROOF_PERPS_NP_LEAF_ELF,
    TAU_STATE_PROOF_RISC0_PERPS_NP_LEAF_ID as TAU_STATE_PROOF_PERPS_NP_LEAF_ID,
    TAU_STATE_PROOF_RISC0_SPOT_LEAF_ELF as TAU_STATE_PROOF_SPOT_LEAF_ELF,
    TAU_STATE_PROOF_RISC0_SPOT_LEAF_ID as TAU_STATE_PROOF_SPOT_LEAF_ID,
    TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ELF as TAU_STATE_PROOF_SUMMARY_LEAF_ELF,
    TAU_STATE_PROOF_RISC0_SUMMARY_LEAF_ID as TAU_STATE_PROOF_SUMMARY_LEAF_ID,
    TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ELF as TAU_STATE_PROOF_ZUSD_LEAF_ELF,
    TAU_STATE_PROOF_RISC0_ZUSD_LEAF_ID as TAU_STATE_PROOF_ZUSD_LEAF_ID,
};
use tau_state_proof_risc0_shared::{
    accepted_receipts_root_v1, compose_perps_np_recursive_leaf_summary_v1,
    compose_recursive_epoch_journal_v1, compose_spot_recursive_leaf_summary_v1,
    compose_zusd_recursive_leaf_summary_v1, frontier_signature_certificates_root_v1,
    ingress_commitment_v1, perps_np_collateral_bindings_hash_v1, perps_np_operation_hash_v1,
    perps_np_oracle_bindings_hash_v1, perps_np_recursive_leaf_asset_delta_rows_v1,
    recursive_asset_delta_root_v1, recursive_epoch_journal_bytes_hash_v1,
    route_price_interval_authority_policy_root_v1, route_price_interval_authority_root_v1,
    route_price_intervals_root_v1, spot_recursive_leaf_asset_delta_rows_v1,
    tx_execution_order_commitment_v1, txs_commitment_v1,
    validate_recursive_effect_summary_shape_v1, zusd_operation_hash_v1,
    zusd_operation_oracle_binding_hash_v1, zusd_recursive_leaf_asset_delta_rows_v1, ChainBalanceV1,
    CollateralBindingV1, DexSnapshotV1, DexStateV1, NonceEntryV1, NonceStateV1, OracleBindingV1,
    PerpsAccountV1, PerpsIntentV1, PerpsMarketParamsV1, PerpsNpActionV1,
    PerpsNpRecursiveLeafInputV1, PerpsNpSnapshotV1, PerpsNpTransitionInputV1,
    PerpsNpTransitionJournalV1, RecursiveAssetDeltaRowV1, RecursiveCompositionInputV1,
    RecursiveEffectSummaryV1, RecursiveEpochJournalV1, RoutePriceIntervalAuthorityPolicySourceV1,
    RoutePriceIntervalAuthorityPolicyV1, RoutePriceIntervalAuthorityV1, RoutePriceIntervalV1,
    SharedPoolFrontierSignatureCertificateV1, SpotRecursiveLeafInputV1, StateProofInputV1,
    StateProofJournalV1, TauTxAppOpsV1, TauTxV1, TxIngressFactV1, ZenoProofInputV1,
    ZusdBalanceEntryV1, ZusdOperationV1, ZusdRecursiveLeafInputV1, ZusdSnapshotV1,
    ZusdTransitionInputV1, ZusdTransitionJournalV1, ZusdVaultEntryV1, PROOF_TYPE,
    PROOF_TYPE_PERPS_NP, PROOF_TYPE_RECURSIVE, PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF,
    PROOF_TYPE_RECURSIVE_SPOT_LEAF, PROOF_TYPE_RECURSIVE_SUMMARY_LEAF,
    PROOF_TYPE_RECURSIVE_ZUSD_LEAF, PROOF_TYPE_ZUSD, RECURSIVE_DOMAIN_SEPARATOR_V1,
    RECURSIVE_EPOCH_PROFILE_V1, RECURSIVE_PERPS_NP_LEAF_MAX_INPUT_BYTES,
    RECURSIVE_PERPS_NP_LEAF_PROFILE_V1, RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES,
    RECURSIVE_SPOT_LEAF_PROFILE_V1, RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES,
    RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1, RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES,
    RECURSIVE_ZUSD_LEAF_PROFILE_V1,
};

#[derive(Clone, Copy)]
struct SurfaceBindingExpectations<'a> {
    journal_chain_id: &'a str,
    pre_app_hash_present: bool,
    pre_app_hash: [u8; 32],
    post_app_hash: [u8; 32],
    operation_hash: [u8; 32],
    state_delta_hash: [u8; 32],
    oracle_binding_hash: [u8; 32],
    participant_set_hash: [u8; 32],
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ProtocolFeeFields {
    share_bps: u32,
    recipient_pubkey: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RouteTotals {
    total_amount_in: u128,
    total_min_amount_out: u128,
    total_amount_out: u128,
    total_max_amount_in: u128,
}

const MAX_RECEIPT_BYTES: usize = 16 * 1024 * 1024;
const MAX_RECEIPT_BASE64_BYTES: usize = MAX_RECEIPT_BYTES.div_ceil(3) * 4;
const MAX_REQUEST_BYTES: usize = 64 * 1024 * 1024;
const RECEIPT_CODEC_V1: &str = "risc0_receipt_canonical_serde_json_depth128_v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ProofReceiptKind {
    Composite,
    Succinct,
    Groth16,
    Fake,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReceiptSecurityProfile {
    kind: ProofReceiptKind,
    verifier_parameters: String,
    hashfn: Option<String>,
    control_id: Option<String>,
}

struct VerifiedRecursiveFacts(Value);

enum VerificationSuccess {
    Basic,
    Recursive(VerifiedRecursiveFacts),
}

impl VerifiedRecursiveFacts {
    fn into_value(self) -> Value {
        self.0
    }
}

impl ProofReceiptKind {
    fn as_str(self) -> &'static str {
        match self {
            Self::Composite => "composite",
            Self::Succinct => "succinct",
            Self::Groth16 => "groth16",
            Self::Fake => "fake",
        }
    }

    fn parse(value: &str) -> Option<Self> {
        match value {
            "composite" => Some(Self::Composite),
            "succinct" => Some(Self::Succinct),
            "groth16" => Some(Self::Groth16),
            "fake" => Some(Self::Fake),
            _ => None,
        }
    }
}

fn main() {
    let stdin = match read_bounded_utf8(std::io::stdin().lock()) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    };
    let req = match parse_request_json(&stdin) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    };

    let schema = req.get("schema").and_then(Value::as_str).unwrap_or("");
    match schema {
        "tau_state_proof_request" => handle_generate(&req),
        "tau_state_proof_verify" => handle_verify(&req),
        "tau_state_proof_txs_commitment" => handle_txs_commitment(&req),
        _ => {
            eprintln!("unexpected schema");
            std::process::exit(2);
        }
    }
}

fn read_bounded_utf8<R: Read>(reader: R) -> Result<String, String> {
    let mut stdin = String::new();
    reader
        .take((MAX_REQUEST_BYTES + 1) as u64)
        .read_to_string(&mut stdin)
        .map_err(|e| format!("failed to read UTF-8 stdin: {e}"))?;
    require_request_bytes_len(stdin.len())?;
    Ok(stdin)
}

fn require_request_bytes_len(request_len: usize) -> Result<(), String> {
    if request_len > MAX_REQUEST_BYTES {
        return Err(format!("request exceeds {MAX_REQUEST_BYTES} byte limit"));
    }
    Ok(())
}

fn parse_request_json(stdin: &str) -> Result<Value, String> {
    strict_json::parse_value(stdin).map_err(|error| format!("stdin must be valid JSON: {error}"))
}

fn handle_txs_commitment(req: &Value) {
    let out = match txs_commitment_response(req) {
        Ok(value) => value,
        Err(err) => die(&err),
    };
    println!(
        "{}",
        serde_json::to_string(&out).expect("commitment response serializes")
    );
}

fn txs_commitment_response(req: &Value) -> Result<Value, String> {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        return Err(
            "unexpected schema_version (expected tau_state_proof_txs_commitment v1)".into(),
        );
    }
    let txs = parse_txs(req.get("transactions"), "transactions")?;
    Ok(json!({
        "schema": "tau_state_proof_txs_commitment_result",
        "schema_version": 1,
        "ok": true,
        "tx_count": txs.len(),
        "txs_commitment": hex_lower(&txs_commitment_v1(&txs)),
    }))
}

fn handle_generate(req: &Value) {
    let proof_type = req
        .get("proof_type")
        .and_then(Value::as_str)
        .unwrap_or(PROOF_TYPE);
    match proof_type {
        PROOF_TYPE => handle_generate_spot(req),
        PROOF_TYPE_PERPS_NP => handle_generate_perps_np(req),
        PROOF_TYPE_ZUSD => handle_generate_zusd(req),
        PROOF_TYPE_RECURSIVE => handle_generate_recursive(req),
        PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF => handle_generate_recursive_perps_np_leaf(req),
        PROOF_TYPE_RECURSIVE_SPOT_LEAF => handle_generate_recursive_spot_leaf(req),
        PROOF_TYPE_RECURSIVE_ZUSD_LEAF => handle_generate_recursive_zusd_leaf(req),
        PROOF_TYPE_RECURSIVE_SUMMARY_LEAF => handle_generate_recursive_summary_leaf(req),
        _ => die("unsupported proof_type"),
    }
}

fn handle_generate_spot(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let state_hash = parse_hex32(&state_hash_hex).unwrap_or_else(|e| die(&e));

    let block = req.get("block").cloned().unwrap_or(Value::Null);
    let tau_state = req.get("tau_state").cloned().unwrap_or(Value::Null);
    if !block.is_object() {
        die("block must be an object");
    }
    if !tau_state.is_object() {
        die("tau_state must be an object");
    }

    let block_timestamp = block
        .get("header")
        .and_then(|h| h.get("timestamp"))
        .and_then(Value::as_u64)
        .unwrap_or_else(|| die("block.header.timestamp missing/invalid"));

    let expected_post_app_hash_hex = tau_state
        .get("app_hash")
        .and_then(Value::as_str)
        .unwrap_or("")
        .trim()
        .to_string();
    if expected_post_app_hash_hex.is_empty() {
        die("tau_state.app_hash missing/empty (app bridge not enabled?)");
    }
    let expected_post_app_hash =
        parse_hex32(&expected_post_app_hash_hex).unwrap_or_else(|e| die(&e));

    let context = req.get("context").cloned().unwrap_or(Value::Null);
    if !context.is_object() {
        die("context must be an object (required for risc0 proof)");
    }
    let context_obj = context.as_object().expect("checked object");

    let pre_app_state_json = context
        .get("app_state_pre")
        .and_then(Value::as_str)
        .unwrap_or("")
        .to_string();
    let pre_app_hash_hex = context
        .get("app_hash_pre")
        .and_then(Value::as_str)
        .unwrap_or("")
        .trim()
        .to_string();
    let (pre_app_hash_present, pre_app_hash) = if pre_app_hash_hex.is_empty() {
        (false, [0u8; 32])
    } else {
        (
            true,
            parse_hex32(&pre_app_hash_hex).unwrap_or_else(|e| die(&e)),
        )
    };

    let chain_balances_post = parse_chain_balances(
        context.get("chain_balances_post"),
        "context.chain_balances_post",
    );

    let pre_state = if pre_app_state_json.trim().is_empty() {
        DexStateV1::empty().to_snapshot()
    } else {
        parse_dex_snapshot_json(&pre_app_state_json).unwrap_or_else(|e| die(&e))
    };

    let txs = parse_block_txs(block.get("transactions")).unwrap_or_else(|e| die(&e));
    let tx_ingress =
        parse_block_ingress_facts(block.get("transactions")).unwrap_or_else(|e| die(&e));
    let pre_nonces = parse_pre_nonces(context.get("pre_nonces"), "context.pre_nonces")
        .unwrap_or_else(|e| die(&e));

    let protocol_fee_fields = parse_protocol_fee_context(context_obj).unwrap_or_else(|e| die(&e));
    let tx_execution_order =
        parse_tx_execution_order_context(context_obj).unwrap_or_else(|e| die(&e));
    let route_price_intervals =
        parse_route_price_intervals_context(context_obj).unwrap_or_else(|e| die(&e));
    let route_price_interval_authority =
        parse_route_price_interval_authority_context(context_obj).unwrap_or_else(|e| die(&e));
    let route_price_interval_authority_policy =
        parse_route_price_interval_authority_policy_context(context_obj)
            .unwrap_or_else(|e| die(&e));
    let route_price_interval_max_width_bps =
        parse_route_price_interval_max_width_bps_context(context_obj).unwrap_or_else(|e| die(&e));
    let shared_pool_frontier_signature_certificates =
        parse_frontier_signature_certificates_context(context_obj).unwrap_or_else(|e| die(&e));

    let input = StateProofInputV1 {
        state_hash,
        block_timestamp,
        pre_app_hash_present,
        pre_app_hash,
        pre_state,
        txs,
        tx_execution_order,
        route_price_intervals,
        route_price_interval_authority: route_price_interval_authority.map(Box::new),
        route_price_interval_authority_policy: route_price_interval_authority_policy.map(Box::new),
        route_price_interval_max_width_bps,
        pre_nonces,
        tx_ingress,
        chain_balances_post,
        expected_post_app_hash,
        protocol_fee_share_bps: protocol_fee_fields.share_bps,
        protocol_fee_recipient_pubkey: protocol_fee_fields.recipient_pubkey,
        shared_pool_frontier_signature_certificates,
    };

    let guest_input = ZenoProofInputV1::Spot(input);
    let (receipt, journal): (Receipt, StateProofJournalV1) = prove_guest_input(&guest_input);

    if journal.state_hash != state_hash {
        die("journal.state_hash mismatch");
    }

    let proof_b64 = encode_receipt(&receipt);

    let mut meta = serde_json::Map::new();
    meta.insert(
        "risc0_image_id".to_string(),
        Value::String(hex_u32_words(TAU_STATE_PROOF_GUEST_ID)),
    );
    meta.insert(
        "txs_commitment".to_string(),
        Value::String(hex_lower(&journal.txs_commitment)),
    );
    meta.insert(
        "tx_execution_order_commitment".to_string(),
        Value::String(hex_lower(&journal.tx_execution_order_commitment)),
    );
    meta.insert(
        "ingress_commitment".to_string(),
        Value::String(hex_lower(&journal.ingress_commitment)),
    );
    meta.insert(
        "pre_nonce_root".to_string(),
        Value::String(hex_lower(&journal.pre_nonce_root)),
    );
    meta.insert(
        "post_nonce_root".to_string(),
        Value::String(hex_lower(&journal.post_nonce_root)),
    );
    meta.insert(
        "accepted_receipts_root".to_string(),
        Value::String(hex_lower(&journal.accepted_receipts_root)),
    );
    meta.insert(
        "pre_app_hash".to_string(),
        Value::String(if journal.pre_app_hash_present {
            hex_lower(&journal.pre_app_hash)
        } else {
            "".to_string()
        }),
    );
    meta.insert(
        "post_app_hash".to_string(),
        Value::String(hex_lower(&journal.post_app_hash)),
    );
    meta.insert(
        "protocol_fee_share_bps".to_string(),
        Value::from(journal.protocol_fee_share_bps),
    );
    meta.insert(
        "protocol_fee_recipient_pubkey".to_string(),
        match &journal.protocol_fee_recipient_pubkey {
            Some(s) => Value::String(s.clone()),
            None => Value::Null,
        },
    );
    meta.insert(
        "route_price_interval_count".to_string(),
        Value::from(journal.route_price_interval_count),
    );
    meta.insert(
        "route_price_intervals_root".to_string(),
        Value::String(hex_lower(&journal.route_price_intervals_root)),
    );
    meta.insert(
        "route_price_interval_authority_root".to_string(),
        Value::String(hex_lower(&journal.route_price_interval_authority_root)),
    );
    meta.insert(
        "route_price_interval_authority_policy_root".to_string(),
        Value::String(hex_lower(
            &journal.route_price_interval_authority_policy_root,
        )),
    );
    meta.insert(
        "route_price_interval_max_width_bps".to_string(),
        match journal.route_price_interval_max_width_bps {
            Some(value) => Value::from(value),
            None => Value::Null,
        },
    );
    meta.insert(
        "shared_pool_frontier_signature_certificate_count".to_string(),
        Value::from(journal.shared_pool_frontier_signature_certificate_count),
    );
    meta.insert(
        "shared_pool_frontier_signature_certificates_root".to_string(),
        Value::String(hex_lower(
            &journal.shared_pool_frontier_signature_certificates_root,
        )),
    );
    insert_receipt_security_meta(&mut meta, &receipt).unwrap_or_else(|e| die(&e));

    let out = json!({
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": normalize_hex64(&state_hash_hex),
        "proof_type": PROOF_TYPE,
        "proof": proof_b64,
        "meta": Value::Object(meta),
    });
    write_json_stdout(&out);
}

fn handle_generate_perps_np(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }
    validate_embedded_methods();

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let state_hash = parse_hex32(&state_hash_hex).unwrap_or_else(|e| die(&e));
    let expected_post_app_hash =
        parse_hex32(&expected_post_app_hash_hex(req)).unwrap_or_else(|e| die(&e));
    let context = req.get("context").cloned().unwrap_or(Value::Null);
    if !context.is_object() {
        die("context must be an object (required for perps np risc0 proof)");
    }
    let context = context.as_object().expect("checked object");
    let chain_id = chain_id_from_request(req, &Value::Object(context.clone()));
    let (pre_app_hash_present, pre_app_hash) = parse_pre_app_hash_context(context);
    let pre_state = parse_perps_pre_state(req, &Value::Object(context.clone()));
    let actions_value = req
        .get("actions")
        .cloned()
        .unwrap_or_else(|| die("actions missing for perps np proof"));
    let actions: Vec<PerpsNpActionV1> = parse_perps_actions_value(&actions_value)
        .unwrap_or_else(|e| die(&format!("actions schema mismatch: {e}")));
    if actions.is_empty() {
        die("actions must be non-empty for perps np proof");
    }

    let input = PerpsNpTransitionInputV1 {
        state_hash,
        chain_id,
        pre_app_hash_present,
        pre_app_hash,
        pre_state,
        actions,
        expected_post_app_hash,
        risc0_image_id: TAU_STATE_PROOF_GUEST_ID,
    };
    let guest_input = ZenoProofInputV1::PerpsNp(input);
    let (receipt, journal): (Receipt, PerpsNpTransitionJournalV1) = prove_guest_input(&guest_input);
    if journal.proof_type != PROOF_TYPE_PERPS_NP {
        die("journal proof_type mismatch");
    }
    if journal.state_hash != state_hash {
        die("journal.state_hash mismatch");
    }
    if journal.post_app_hash != expected_post_app_hash {
        die("journal.post_app_hash mismatch");
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_GUEST_ID {
        die("journal.risc0_image_id mismatch");
    }
    let proof_b64 = encode_receipt(&receipt);
    let out = json!({
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": normalize_hex64(&state_hash_hex),
        "proof_type": PROOF_TYPE_PERPS_NP,
        "proof": proof_b64,
        "meta": attach_receipt_security_meta(perps_np_meta(&journal), &receipt),
    });
    write_json_stdout(&out);
}

fn handle_generate_zusd(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }
    validate_embedded_methods();

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let state_hash = parse_hex32(&state_hash_hex).unwrap_or_else(|e| die(&e));
    let expected_post_app_hash =
        parse_hex32(&expected_post_app_hash_hex(req)).unwrap_or_else(|e| die(&e));
    let context = req.get("context").cloned().unwrap_or(Value::Null);
    if !context.is_object() {
        die("context must be an object (required for zUSD risc0 proof)");
    }
    let context = context.as_object().expect("checked object");
    let chain_id = chain_id_from_request(req, &Value::Object(context.clone()));
    let (pre_app_hash_present, pre_app_hash) = parse_pre_app_hash_context(context);
    let pre_state = parse_zusd_pre_state(req, &Value::Object(context.clone()));
    let operation_value = req
        .get("operation")
        .cloned()
        .unwrap_or_else(|| die("operation missing for zUSD proof"));
    let operation: ZusdOperationV1 = parse_zusd_operation_value(&operation_value)
        .unwrap_or_else(|e| die(&format!("operation schema mismatch: {e}")));

    let input = ZusdTransitionInputV1 {
        state_hash,
        chain_id,
        pre_app_hash_present,
        pre_app_hash,
        pre_state,
        operation,
        expected_post_app_hash,
        risc0_image_id: TAU_STATE_PROOF_GUEST_ID,
    };
    let guest_input = ZenoProofInputV1::Zusd(input);
    let (receipt, journal): (Receipt, ZusdTransitionJournalV1) = prove_guest_input(&guest_input);
    if journal.proof_type != PROOF_TYPE_ZUSD {
        die("journal proof_type mismatch");
    }
    if journal.state_hash != state_hash {
        die("journal.state_hash mismatch");
    }
    if journal.post_app_hash != expected_post_app_hash {
        die("journal.post_app_hash mismatch");
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_GUEST_ID {
        die("journal.risc0_image_id mismatch");
    }
    let proof_b64 = encode_receipt(&receipt);
    let out = json!({
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": normalize_hex64(&state_hash_hex),
        "proof_type": PROOF_TYPE_ZUSD,
        "proof": proof_b64,
        "meta": attach_receipt_security_meta(zusd_meta(&journal), &receipt),
    });
    write_json_stdout(&out);
}

fn handle_generate_recursive(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }
    validate_aggregate_method();
    require_requested_receipt_kind(req, ProofReceiptKind::Succinct).unwrap_or_else(|e| die(&e));

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let state_hash = parse_hex32(&state_hash_hex).unwrap_or_else(|e| die(&e));
    let input = parse_recursive_input(req).unwrap_or_else(|e| die(&e));
    if input.statement.expected_post_state_root != state_hash {
        die("state_hash must equal recursive_input.statement.expected_post_state_root");
    }
    let child_receipts = parse_recursive_child_receipts(req, &input).unwrap_or_else(|e| die(&e));

    let (receipt, journal): (Receipt, RecursiveEpochJournalV1) =
        prove_aggregate_input_with_assumptions(&input, &child_receipts);
    let receipt_kind = receipt_kind(&receipt).unwrap_or_else(|e| die(&e));
    if journal.proof_type != PROOF_TYPE_RECURSIVE {
        die("journal proof_type mismatch");
    }
    if journal.domain_separator != RECURSIVE_DOMAIN_SEPARATOR_V1 {
        die("journal domain_separator mismatch");
    }
    if journal.post_state_root != state_hash {
        die("journal.post_state_root mismatch");
    }

    let out = json!({
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": normalize_hex64(&state_hash_hex),
        "proof_type": PROOF_TYPE_RECURSIVE,
        "proof": encode_receipt(&receipt),
        "meta": attach_receipt_security_meta(recursive_meta(&journal, receipt_kind), &receipt),
    });
    write_json_stdout(&out);
}

fn handle_generate_recursive_spot_leaf(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }
    validate_spot_leaf_method();
    require_requested_receipt_kind(req, ProofReceiptKind::Succinct).unwrap_or_else(|e| die(&e));

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let state_hash = parse_hex32(&state_hash_hex).unwrap_or_else(|e| die(&e));
    let input = parse_spot_recursive_leaf_input(req).unwrap_or_else(|e| die(&e));
    if input.risc0_image_id != TAU_STATE_PROOF_SPOT_LEAF_ID {
        die("spot_recursive_leaf_input.risc0_image_id must equal the spot leaf image ID");
    }
    if input.spot_input.state_hash != state_hash {
        die("state_hash must equal spot_recursive_leaf_input.spot_input.state_hash");
    }
    let input_bytes = postcard::to_allocvec(&input)
        .unwrap_or_else(|e| die(&format!("failed to encode recursive spot leaf input: {e}")));
    if input_bytes.len() > RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES as usize {
        die("recursive spot leaf input exceeds max bytes");
    }
    let expected_summary =
        compose_spot_recursive_leaf_summary_v1(input.clone()).unwrap_or_else(|e| {
            die(&format!(
                "recursive spot leaf input rejected: {}",
                transition_error_str(e)
            ))
        });
    let asset_delta_rows =
        spot_recursive_leaf_asset_delta_rows_v1(&input.spot_input, input.public_policy_hash)
            .unwrap_or_else(|e| {
                die(&format!(
                    "recursive spot leaf asset deltas rejected: {}",
                    transition_error_str(e)
                ))
            });
    let asset_delta_root = recursive_asset_delta_root_v1(&asset_delta_rows).unwrap_or_else(|e| {
        die(&format!(
            "recursive spot leaf asset delta root rejected: {}",
            transition_error_str(e)
        ))
    });
    if asset_delta_root != expected_summary.asset_delta_root {
        die("recursive spot leaf asset delta root mismatch");
    }

    let (receipt, journal): (Receipt, RecursiveEffectSummaryV1) = prove_direct_guest_input(
        &input,
        TAU_STATE_PROOF_SPOT_LEAF_ELF,
        TAU_STATE_PROOF_SPOT_LEAF_ID,
        &[],
        ProofReceiptKind::Succinct,
    );
    let receipt_kind = receipt_kind(&receipt).unwrap_or_else(|e| die(&e));
    if journal != expected_summary {
        die("recursive spot leaf journal mismatch");
    }
    if journal.post_state_root != state_hash {
        die("journal.post_state_root mismatch");
    }

    let out = json!({
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": normalize_hex64(&state_hash_hex),
        "proof_type": PROOF_TYPE_RECURSIVE_SPOT_LEAF,
        "proof": encode_receipt(&receipt),
        "meta": attach_receipt_security_meta(
            recursive_spot_leaf_meta(&journal, &asset_delta_rows, receipt_kind),
            &receipt,
        ),
    });
    write_json_stdout(&out);
}

fn handle_generate_recursive_perps_np_leaf(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }
    validate_perps_np_leaf_method();
    require_requested_receipt_kind(req, ProofReceiptKind::Succinct).unwrap_or_else(|e| die(&e));

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let state_hash = parse_hex32(&state_hash_hex).unwrap_or_else(|e| die(&e));
    let input = parse_perps_np_recursive_leaf_input(req).unwrap_or_else(|e| die(&e));
    if input.risc0_image_id != TAU_STATE_PROOF_PERPS_NP_LEAF_ID {
        die("perps_np_recursive_leaf_input.risc0_image_id must equal the perps NP leaf image ID");
    }
    if input.perps_input.state_hash != state_hash {
        die("state_hash must equal perps_np_recursive_leaf_input.perps_input.state_hash");
    }
    let input_bytes = postcard::to_allocvec(&input).unwrap_or_else(|e| {
        die(&format!(
            "failed to encode recursive perps NP leaf input: {e}"
        ))
    });
    if input_bytes.len() > RECURSIVE_PERPS_NP_LEAF_MAX_INPUT_BYTES as usize {
        die("recursive perps NP leaf input exceeds max bytes");
    }
    let expected_summary = compose_perps_np_recursive_leaf_summary_v1(input.clone())
        .unwrap_or_else(|e| {
            die(&format!(
                "recursive perps NP leaf input rejected: {}",
                transition_error_str(e)
            ))
        });
    let asset_delta_rows = perps_np_recursive_leaf_asset_delta_rows_v1(&input.perps_input)
        .unwrap_or_else(|e| {
            die(&format!(
                "recursive perps NP leaf asset deltas rejected: {}",
                transition_error_str(e)
            ))
        });
    let asset_delta_root = recursive_asset_delta_root_v1(&asset_delta_rows).unwrap_or_else(|e| {
        die(&format!(
            "recursive perps NP leaf asset delta root rejected: {}",
            transition_error_str(e)
        ))
    });
    if asset_delta_root != expected_summary.asset_delta_root {
        die("recursive perps NP leaf asset delta root mismatch");
    }

    let (receipt, journal): (Receipt, RecursiveEffectSummaryV1) = prove_direct_guest_input(
        &input,
        TAU_STATE_PROOF_PERPS_NP_LEAF_ELF,
        TAU_STATE_PROOF_PERPS_NP_LEAF_ID,
        &[],
        ProofReceiptKind::Succinct,
    );
    let receipt_kind = receipt_kind(&receipt).unwrap_or_else(|e| die(&e));
    if journal != expected_summary {
        die("recursive perps NP leaf journal mismatch");
    }
    if journal.post_state_root != state_hash {
        die("journal.post_state_root mismatch");
    }

    let out = json!({
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": normalize_hex64(&state_hash_hex),
        "proof_type": PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF,
        "proof": encode_receipt(&receipt),
        "meta": attach_receipt_security_meta(
            recursive_perps_np_leaf_meta(&journal, &asset_delta_rows, receipt_kind),
            &receipt,
        ),
    });
    write_json_stdout(&out);
}

fn handle_generate_recursive_zusd_leaf(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }
    validate_zusd_leaf_method();
    require_requested_receipt_kind(req, ProofReceiptKind::Succinct).unwrap_or_else(|e| die(&e));

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let state_hash = parse_hex32(&state_hash_hex).unwrap_or_else(|e| die(&e));
    let input = parse_zusd_recursive_leaf_input(req).unwrap_or_else(|e| die(&e));
    if input.risc0_image_id != TAU_STATE_PROOF_ZUSD_LEAF_ID {
        die("zusd_recursive_leaf_input.risc0_image_id must equal the zUSD leaf image ID");
    }
    if input.zusd_input.state_hash != state_hash {
        die("state_hash must equal zusd_recursive_leaf_input.zusd_input.state_hash");
    }
    let input_bytes = postcard::to_allocvec(&input)
        .unwrap_or_else(|e| die(&format!("failed to encode recursive zUSD leaf input: {e}")));
    if input_bytes.len() > RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES as usize {
        die("recursive zUSD leaf input exceeds max bytes");
    }
    let expected_summary =
        compose_zusd_recursive_leaf_summary_v1(input.clone()).unwrap_or_else(|e| {
            die(&format!(
                "recursive zUSD leaf input rejected: {}",
                transition_error_str(e)
            ))
        });
    let zusd_journal =
        tau_state_proof_risc0_shared::execute_zusd_transition_v1(input.zusd_input.clone())
            .unwrap_or_else(|e| {
                die(&format!(
                    "recursive zUSD leaf transition rejected: {}",
                    transition_error_str(e)
                ))
            });
    let asset_delta_rows =
        zusd_recursive_leaf_asset_delta_rows_v1(&zusd_journal, input.public_policy_hash)
            .unwrap_or_else(|e| {
                die(&format!(
                    "recursive zUSD leaf asset deltas rejected: {}",
                    transition_error_str(e)
                ))
            });
    let asset_delta_root = recursive_asset_delta_root_v1(&asset_delta_rows).unwrap_or_else(|e| {
        die(&format!(
            "recursive zUSD leaf asset delta root rejected: {}",
            transition_error_str(e)
        ))
    });
    if asset_delta_root != expected_summary.asset_delta_root {
        die("recursive zUSD leaf asset delta root mismatch");
    }

    let (receipt, journal): (Receipt, RecursiveEffectSummaryV1) = prove_direct_guest_input(
        &input,
        TAU_STATE_PROOF_ZUSD_LEAF_ELF,
        TAU_STATE_PROOF_ZUSD_LEAF_ID,
        &[],
        ProofReceiptKind::Succinct,
    );
    let receipt_kind = receipt_kind(&receipt).unwrap_or_else(|e| die(&e));
    if journal != expected_summary {
        die("recursive zUSD leaf journal mismatch");
    }
    if journal.post_state_root != state_hash {
        die("journal.post_state_root mismatch");
    }

    let out = json!({
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": normalize_hex64(&state_hash_hex),
        "proof_type": PROOF_TYPE_RECURSIVE_ZUSD_LEAF,
        "proof": encode_receipt(&receipt),
        "meta": attach_receipt_security_meta(
            recursive_zusd_leaf_meta(&journal, &asset_delta_rows, receipt_kind),
            &receipt,
        ),
    });
    write_json_stdout(&out);
}

fn handle_generate_recursive_summary_leaf(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }
    validate_summary_leaf_method();
    require_requested_receipt_kind(req, ProofReceiptKind::Composite).unwrap_or_else(|e| die(&e));

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let state_hash = parse_hex32(&state_hash_hex).unwrap_or_else(|e| die(&e));
    let summary = parse_recursive_summary(req).unwrap_or_else(|e| die(&e));
    if summary.proof_profile != RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1 {
        die("recursive summary leaf requires recursive_summary_leaf_test_v1 profile");
    }
    if summary.risc0_image_id != TAU_STATE_PROOF_SUMMARY_LEAF_ID {
        die("recursive_summary.risc0_image_id must equal the summary leaf image ID");
    }
    if summary.post_state_root != state_hash {
        die("state_hash must equal recursive_summary.post_state_root");
    }
    let summary_bytes = postcard::to_allocvec(&summary)
        .unwrap_or_else(|e| die(&format!("failed to encode recursive summary: {e}")));
    if summary_bytes.len() > RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES as usize {
        die("recursive summary leaf input exceeds max bytes");
    }

    let (receipt, journal): (Receipt, RecursiveEffectSummaryV1) = prove_direct_guest_input(
        &summary,
        TAU_STATE_PROOF_SUMMARY_LEAF_ELF,
        TAU_STATE_PROOF_SUMMARY_LEAF_ID,
        &[],
        ProofReceiptKind::Composite,
    );
    let receipt_kind = receipt_kind(&receipt).unwrap_or_else(|e| die(&e));
    if journal != summary {
        die("recursive summary leaf journal mismatch");
    }

    let out = json!({
        "schema": "tau_state_proof",
        "schema_version": 1,
        "state_hash": normalize_hex64(&state_hash_hex),
        "proof_type": PROOF_TYPE_RECURSIVE_SUMMARY_LEAF,
        "proof": encode_receipt(&receipt),
        "meta": attach_receipt_security_meta(
            recursive_summary_leaf_meta(&journal, receipt_kind),
            &receipt,
        ),
    });
    write_json_stdout(&out);
}

fn handle_verify(req: &Value) {
    write_json_stdout(&verification_response(try_verify(req)));
}

fn verification_response(result: Result<VerificationSuccess, String>) -> Value {
    match result {
        Ok(VerificationSuccess::Basic) => json!({ "ok": true }),
        Ok(VerificationSuccess::Recursive(verified)) => json!({
            "ok": true,
            "verified_recursive_facts": verified.into_value(),
        }),
        Err(err) => json!({ "ok": false, "error": err }),
    }
}

fn recursive_verified_facts_from_disclosure(
    journal: &RecursiveEpochJournalV1,
    journal_bytes: &[u8],
    input: &RecursiveCompositionInputV1,
    receipt_profile: &ReceiptSecurityProfile,
) -> Result<Value, String> {
    let recomposed = compose_recursive_epoch_journal_v1(input).map_err(transition_error_str)?;
    if recomposed != *journal {
        return Err("recursive_input disclosure does not match verified journal".into());
    }

    let child_verification_claim_hashes: Vec<String> = input
        .children
        .iter()
        .map(|child| hex_prefixed(&child.descriptor.child_verification_claim_hash))
        .collect();
    let mut accepted_receipt_ids: Vec<[u8; 32]> = input
        .children
        .iter()
        .flat_map(|child| child.accepted_receipt_ids.iter())
        .copied()
        .collect();
    accepted_receipt_ids.sort_unstable();
    let accepted_receipt_ids: Vec<String> = accepted_receipt_ids.iter().map(hex_prefixed).collect();
    let mut cross_shard_message_ids: Vec<[u8; 32]> = input
        .children
        .iter()
        .flat_map(|child| child.outbox_messages.iter())
        .map(|message| message.message_id)
        .collect();
    cross_shard_message_ids.sort_unstable();
    let cross_shard_message_ids: Vec<String> =
        cross_shard_message_ids.iter().map(hex_prefixed).collect();
    let root_journal_hash =
        recursive_epoch_journal_bytes_hash_v1(journal_bytes).map_err(transition_error_str)?;
    if receipt_profile.kind != ProofReceiptKind::Succinct {
        return Err("verified recursive receipt kind mismatch".into());
    }
    let receipt_hashfn = receipt_profile
        .hashfn
        .as_ref()
        .ok_or_else(|| "verified recursive receipt hash function missing".to_string())?;
    let receipt_control_id = receipt_profile
        .control_id
        .as_ref()
        .ok_or_else(|| "verified recursive receipt control ID missing".to_string())?;

    Ok(json!({
        "schema": "zenodex.verified_recursive_stark_root_facts.v1",
        "aggregate_image_id": hex_u32_words(TAU_STATE_PROOF_AGGREGATE_ID),
        "receipt_codec": RECEIPT_CODEC_V1,
        "receipt_kind": ProofReceiptKind::Succinct.as_str(),
        "receipt_hashfn": receipt_hashfn,
        "receipt_verifier_parameters": receipt_profile.verifier_parameters,
        "receipt_control_id": receipt_control_id,
        "chain_id": journal.chain_id,
        "epoch_id": journal.epoch_id,
        "proof_profile": journal.proof_profile,
        "root_journal_hash": hex_prefixed(&root_journal_hash),
        "verifier_set_root": hex_prefixed(&journal.verifier_set_root),
        "public_policy_hash": hex_prefixed(&journal.public_policy_hash),
        "child_verification_claim_hashes": child_verification_claim_hashes,
        "child_verification_claims_root": hex_prefixed(&journal.child_verification_claims_root),
        "accepted_receipt_ids": accepted_receipt_ids,
        "accepted_receipts_root": hex_prefixed(&journal.accepted_receipts_root),
        "cross_shard_message_ids": cross_shard_message_ids,
        "cross_shard_message_ids_root": hex_prefixed(&journal.cross_shard_message_ids_root),
    }))
}

fn try_verify(req: &Value) -> Result<VerificationSuccess, String> {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        return Err("unexpected schema_version (expected tau_state_proof_verify v1)".into());
    }

    validate_embedded_methods();

    let state_hash_hex = require_str(req.get("state_hash"), "state_hash");
    let expected_state_hash = parse_hex32(&state_hash_hex).map_err(|e| e.to_string())?;

    let proof = req
        .get("proof")
        .ok_or_else(|| "proof missing".to_string())?;
    if !proof.is_object() {
        return Err("proof must be an object".into());
    }

    let proof_type = proof
        .get("proof_type")
        .and_then(Value::as_str)
        .unwrap_or("");
    if proof_type == PROOF_TYPE_PERPS_NP {
        validate_embedded_methods();
        try_verify_perps_np(req, proof, expected_state_hash)?;
        return Ok(VerificationSuccess::Basic);
    }
    if proof_type == PROOF_TYPE_ZUSD {
        validate_embedded_methods();
        try_verify_zusd(req, proof, expected_state_hash)?;
        return Ok(VerificationSuccess::Basic);
    }
    if proof_type == PROOF_TYPE_RECURSIVE {
        validate_aggregate_method();
        return try_verify_recursive(req, proof, expected_state_hash)
            .map(VerificationSuccess::Recursive);
    }
    if proof_type == PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF {
        validate_perps_np_leaf_method();
        try_verify_recursive_perps_np_leaf(proof, expected_state_hash)?;
        return Ok(VerificationSuccess::Basic);
    }
    if proof_type == PROOF_TYPE_RECURSIVE_SPOT_LEAF {
        validate_spot_leaf_method();
        try_verify_recursive_spot_leaf(proof, expected_state_hash)?;
        return Ok(VerificationSuccess::Basic);
    }
    if proof_type == PROOF_TYPE_RECURSIVE_ZUSD_LEAF {
        validate_zusd_leaf_method();
        try_verify_recursive_zusd_leaf(proof, expected_state_hash)?;
        return Ok(VerificationSuccess::Basic);
    }
    if proof_type == PROOF_TYPE_RECURSIVE_SUMMARY_LEAF {
        validate_summary_leaf_method();
        try_verify_recursive_summary_leaf(proof, expected_state_hash)?;
        return Ok(VerificationSuccess::Basic);
    }
    if proof_type != PROOF_TYPE {
        return Err("unsupported proof_type".into());
    }
    validate_embedded_methods();
    check_proof_meta_image_id(proof)?;

    let receipt = decode_verified_receipt_from_proof(proof)?;

    let journal: StateProofJournalV1 = decode_postcard_journal(&receipt, "spot journal")?;

    if journal.state_hash != expected_state_hash {
        return Err("journal.state_hash mismatch".into());
    }
    check_spot_protocol_fee_bindings(req, proof, &journal)?;
    expect_meta_hash(
        proof,
        "tx_execution_order_commitment",
        journal.tx_execution_order_commitment,
    )?;

    let mut verified_ingress: Option<Vec<TxIngressFactV1>> = None;

    // Optional stronger checks (fail-closed when provided).
    if let Some(block) = req.get("block") {
        if !block.is_object() {
            return Err("block must be an object".into());
        }
        let block_ts = block
            .get("header")
            .and_then(|h| h.get("timestamp"))
            .and_then(Value::as_u64)
            .ok_or_else(|| "block.header.timestamp missing/invalid".to_string())?;
        let journal_ts = req
            .get("context")
            .and_then(|c| c.get("block_timestamp"))
            .and_then(Value::as_u64);
        if let Some(ts) = journal_ts {
            if ts != block_ts {
                return Err("context.block_timestamp mismatch".into());
            }
        }

        let txs = parse_block_txs(block.get("transactions")).map_err(|e| e.to_string())?;
        let expected_commitment = txs_commitment_v1(&txs);
        if expected_commitment != journal.txs_commitment {
            return Err("txs_commitment mismatch".into());
        }
        let expected_order = tx_execution_order_from_context(req, txs.len())?;
        let expected_order_commitment =
            tx_execution_order_commitment_v1(&expected_order).map_err(transition_error_str)?;
        if expected_order_commitment != journal.tx_execution_order_commitment {
            return Err("tx_execution_order_commitment mismatch".into());
        }
        let ingress =
            parse_block_ingress_facts(block.get("transactions")).map_err(|e| e.to_string())?;
        let expected_ingress_commitment = ingress_commitment_v1(&ingress);
        if expected_ingress_commitment != journal.ingress_commitment {
            return Err("ingress_commitment mismatch".into());
        }
        let expected_receipts_root =
            accepted_receipts_root_v1(&txs, &ingress).map_err(transition_error_str)?;
        if expected_receipts_root != journal.accepted_receipts_root {
            return Err("accepted_receipts_root mismatch".into());
        }
        verified_ingress = Some(ingress);
    }

    if let Some(tau_state) = req.get("tau_state") {
        if !tau_state.is_object() {
            return Err("tau_state must be an object".into());
        }
        let post_hex = tau_state
            .get("app_hash")
            .and_then(Value::as_str)
            .unwrap_or("")
            .trim()
            .to_string();
        if !post_hex.is_empty() {
            let expected_post = parse_hex32(&post_hex).map_err(|e| e.to_string())?;
            if expected_post != journal.post_app_hash {
                return Err("post_app_hash mismatch".into());
            }
        }
    }

    let mut context_pre_nonces: Vec<NonceEntryV1> = Vec::new();
    let mut context_seen = false;
    if let Some(context) = req.get("context") {
        context_seen = true;
        if !context.is_object() {
            return Err("context must be an object".into());
        }
        context_pre_nonces = parse_pre_nonces(context.get("pre_nonces"), "context.pre_nonces")
            .map_err(|e| e.to_string())?;
        if let Some(prev) = context.get("app_hash_pre").and_then(Value::as_str) {
            let prev_hex = prev.trim().to_string();
            if prev_hex.is_empty() {
                if journal.pre_app_hash_present {
                    return Err("pre_app_hash present but expected empty".into());
                }
            } else {
                let expected_pre = parse_hex32(&prev_hex).map_err(|e| e.to_string())?;
                if !journal.pre_app_hash_present {
                    return Err("pre_app_hash missing but expected present".into());
                }
                if expected_pre != journal.pre_app_hash {
                    return Err("pre_app_hash mismatch".into());
                }
            }
        }
    }
    if context_seen || verified_ingress.is_some() {
        check_nonce_roots(&journal, context_pre_nonces, verified_ingress.as_deref())?;
    }

    Ok(VerificationSuccess::Basic)
}

fn try_verify_perps_np(
    req: &Value,
    proof: &Value,
    expected_state_hash: [u8; 32],
) -> Result<(), String> {
    check_proof_meta_image_id(proof)?;
    let receipt = decode_verified_receipt_from_proof(proof)?;
    let journal: PerpsNpTransitionJournalV1 =
        decode_postcard_journal(&receipt, "perps np journal")?;
    if journal.proof_type != PROOF_TYPE_PERPS_NP {
        return Err("journal proof_type mismatch".into());
    }
    if journal.state_hash != expected_state_hash {
        return Err("journal.state_hash mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_GUEST_ID {
        return Err("journal.risc0_image_id mismatch".into());
    }
    if journal.participant_count < 4 {
        return Err("participant_count below multi-party floor".into());
    }
    if journal.net_position_base != 0 {
        return Err("journal net_position_base must be zero".into());
    }
    let actions = parse_verify_perps_actions(req)?;
    let expected_operation = perps_np_operation_hash_v1(&actions);
    if expected_operation != journal.operation_hash {
        return Err("operation_hash mismatch".into());
    }
    let expected_oracle =
        perps_np_oracle_bindings_hash_v1(&actions).map_err(transition_error_str)?;
    if expected_oracle != journal.oracle_binding_hash {
        return Err("oracle_binding_hash mismatch".into());
    }
    let expected_collateral =
        perps_np_collateral_bindings_hash_v1(&actions).map_err(transition_error_str)?;
    if expected_collateral != journal.collateral_binding_hash {
        return Err("collateral_binding_hash mismatch".into());
    }
    verify_surface_request_bindings(
        req,
        proof,
        SurfaceBindingExpectations {
            journal_chain_id: &journal.chain_id,
            pre_app_hash_present: journal.pre_app_hash_present,
            pre_app_hash: journal.pre_app_hash,
            post_app_hash: journal.post_app_hash,
            operation_hash: journal.operation_hash,
            state_delta_hash: journal.state_delta_hash,
            oracle_binding_hash: journal.oracle_binding_hash,
            participant_set_hash: journal.participant_set_hash,
        },
    )?;
    let context = strict_context_obj(req)?;
    expect_meta_hash(
        proof,
        "collateral_binding_hash",
        journal.collateral_binding_hash,
    )?;
    expect_context_hash(
        context,
        "collateral_binding_hash",
        journal.collateral_binding_hash,
    )?;
    expect_meta_hash(proof, "receipt_root", journal.receipt_root)?;
    expect_context_hash(context, "receipt_root", journal.receipt_root)?;
    Ok(())
}

fn try_verify_zusd(
    req: &Value,
    proof: &Value,
    expected_state_hash: [u8; 32],
) -> Result<(), String> {
    check_proof_meta_image_id(proof)?;
    let receipt = decode_verified_receipt_from_proof(proof)?;
    let journal: ZusdTransitionJournalV1 = decode_postcard_journal(&receipt, "zUSD journal")?;
    if journal.proof_type != PROOF_TYPE_ZUSD {
        return Err("journal proof_type mismatch".into());
    }
    if journal.state_hash != expected_state_hash {
        return Err("journal.state_hash mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_GUEST_ID {
        return Err("journal.risc0_image_id mismatch".into());
    }
    if journal.minted_zusd_e8 == 0 {
        return Err("journal minted_zusd_e8 must be positive".into());
    }
    let operation = parse_verify_zusd_operation(req)?;
    let expected_operation = zusd_operation_hash_v1(&operation);
    if expected_operation != journal.operation_hash {
        return Err("operation_hash mismatch".into());
    }
    let expected_oracle =
        zusd_operation_oracle_binding_hash_v1(&operation).map_err(transition_error_str)?;
    if expected_oracle != journal.oracle_binding_hash {
        return Err("oracle_binding_hash mismatch".into());
    }
    verify_surface_request_bindings(
        req,
        proof,
        SurfaceBindingExpectations {
            journal_chain_id: &journal.chain_id,
            pre_app_hash_present: journal.pre_app_hash_present,
            pre_app_hash: journal.pre_app_hash,
            post_app_hash: journal.post_app_hash,
            operation_hash: journal.operation_hash,
            state_delta_hash: journal.state_delta_hash,
            oracle_binding_hash: journal.oracle_binding_hash,
            participant_set_hash: journal.participant_set_hash,
        },
    )?;
    let context = strict_context_obj(req)?;
    expect_meta_hash(
        proof,
        "zusd_balance_root_hash",
        journal.zusd_balance_root_hash,
    )?;
    expect_context_hash(
        context,
        "zusd_balance_root_hash",
        journal.zusd_balance_root_hash,
    )?;
    expect_meta_hash(proof, "zusd_vault_root_hash", journal.zusd_vault_root_hash)?;
    expect_context_hash(
        context,
        "zusd_vault_root_hash",
        journal.zusd_vault_root_hash,
    )?;
    Ok(())
}

fn try_verify_recursive(
    req: &Value,
    proof: &Value,
    expected_state_hash: [u8; 32],
) -> Result<VerifiedRecursiveFacts, String> {
    preflight_recursive_verification_wire(req, proof, expected_state_hash)?;
    let authenticated = recursive_receipt_authentication::authenticate(proof)?;
    finish_recursive_verification(req, proof, expected_state_hash, authenticated)
}

#[cfg(test)]
fn try_verify_recursive_with_test_authenticator<F>(
    req: &Value,
    proof: &Value,
    expected_state_hash: [u8; 32],
    authenticate_receipt: F,
) -> Result<VerifiedRecursiveFacts, String>
where
    F: FnOnce(&Value) -> Result<recursive_receipt_authentication::AuthenticatedReceipt, String>,
{
    preflight_recursive_verification_wire(req, proof, expected_state_hash)?;
    let authenticated = authenticate_receipt(proof)?;
    finish_recursive_verification(req, proof, expected_state_hash, authenticated)
}

fn preflight_recursive_verification_wire(
    req: &Value,
    proof: &Value,
    expected_state_hash: [u8; 32],
) -> Result<(), String> {
    recursive_wire::validate_recursive_verify_v1(req, proof)?;
    let proof_state_hash = proof
        .get("state_hash")
        .and_then(Value::as_str)
        .ok_or_else(|| "recursive_verify_request.proof.state_hash must be a string".to_string())?;
    let proof_state_hash = parse_hex32(proof_state_hash)
        .map_err(|error| format!("recursive_verify_request.proof.state_hash invalid: {error}"))?;
    if proof_state_hash != expected_state_hash {
        return Err("recursive_verify_request.proof.state_hash mismatch".to_string());
    }
    check_proof_meta_image_id_for(proof, TAU_STATE_PROOF_AGGREGATE_ID)?;
    expect_meta_str(proof, "proof_type", PROOF_TYPE_RECURSIVE)?;
    expect_meta_str(proof, "domain_separator", RECURSIVE_DOMAIN_SEPARATOR_V1)?;
    expect_meta_str(proof, "proof_profile", RECURSIVE_EPOCH_PROFILE_V1)?;
    expect_meta_str(proof, "receipt_codec", RECEIPT_CODEC_V1)?;
    expect_meta_str(proof, "receipt_kind", ProofReceiptKind::Succinct.as_str())?;
    Ok(())
}

fn finish_recursive_verification(
    req: &Value,
    proof: &Value,
    expected_state_hash: [u8; 32],
    authenticated: recursive_receipt_authentication::AuthenticatedReceipt,
) -> Result<VerifiedRecursiveFacts, String> {
    let (receipt, receipt_profile) = authenticated.into_parts();
    let journal: RecursiveEpochJournalV1 = decode_postcard_journal(&receipt, "recursive journal")?;
    if journal.proof_type != PROOF_TYPE_RECURSIVE {
        return Err("journal proof_type mismatch".into());
    }
    if journal.domain_separator != RECURSIVE_DOMAIN_SEPARATOR_V1 {
        return Err("journal domain_separator mismatch".into());
    }
    if journal.proof_profile != RECURSIVE_EPOCH_PROFILE_V1 {
        return Err("journal proof_profile mismatch".into());
    }
    if journal.post_state_root != expected_state_hash {
        return Err("journal.post_state_root mismatch".into());
    }
    verify_recursive_trusted_expectations(req, &journal, &receipt_profile)?;
    expect_meta_str(proof, "proof_type", PROOF_TYPE_RECURSIVE)?;
    expect_meta_str(proof, "domain_separator", RECURSIVE_DOMAIN_SEPARATOR_V1)?;
    expect_meta_str(proof, "chain_id", &journal.chain_id)?;
    expect_meta_u64(proof, "epoch_id", journal.epoch_id)?;
    expect_meta_str(proof, "proof_profile", RECURSIVE_EPOCH_PROFILE_V1)?;
    expect_meta_hash(proof, "statement_hash", journal.statement_hash)?;
    expect_meta_hash(proof, "verifier_set_root", journal.verifier_set_root)?;
    expect_meta_hash(
        proof,
        "allowed_authority_roots_root",
        journal.allowed_authority_roots_root,
    )?;
    expect_meta_hash(
        proof,
        "child_verification_claims_root",
        journal.child_verification_claims_root,
    )?;
    expect_meta_hash(proof, "child_journals_root", journal.child_journals_root)?;
    expect_meta_hash(
        proof,
        "child_effect_summaries_root",
        journal.child_effect_summaries_root,
    )?;
    expect_meta_u64(proof, "child_count", journal.child_count as u64)?;
    expect_meta_hash(proof, "pre_state_root", journal.pre_state_root)?;
    expect_meta_hash(proof, "post_state_root", journal.post_state_root)?;
    expect_meta_hash(proof, "tx_root", journal.tx_root)?;
    expect_meta_hash(proof, "evidence_root", journal.evidence_root)?;
    expect_meta_hash(proof, "receipt_root", journal.receipt_root)?;
    expect_meta_hash(
        proof,
        "accepted_receipts_root",
        journal.accepted_receipts_root,
    )?;
    expect_meta_hash(
        proof,
        "rejected_receipts_root",
        journal.rejected_receipts_root,
    )?;
    expect_meta_hash(
        proof,
        "aggregate_asset_delta_root",
        journal.aggregate_asset_delta_root,
    )?;
    expect_meta_hash(
        proof,
        "cross_shard_outbox_root",
        journal.cross_shard_outbox_root,
    )?;
    expect_meta_hash(
        proof,
        "cross_shard_inbox_root",
        journal.cross_shard_inbox_root,
    )?;
    expect_meta_hash(
        proof,
        "cross_shard_message_ids_root",
        journal.cross_shard_message_ids_root,
    )?;
    expect_meta_hash(proof, "carry_queue_pre_root", journal.carry_queue_pre_root)?;
    expect_meta_hash(
        proof,
        "carry_queue_post_root",
        journal.carry_queue_post_root,
    )?;
    expect_meta_hash(
        proof,
        "conflict_schedule_hash",
        journal.conflict_schedule_hash,
    )?;
    expect_meta_hash(
        proof,
        "data_availability_root",
        journal.data_availability_root,
    )?;
    expect_meta_hash(proof, "public_policy_hash", journal.public_policy_hash)?;
    expect_meta_hash(proof, "feature_suite_hash", journal.feature_suite_hash)?;
    expect_meta_hash(proof, "dependency_lock_hash", journal.dependency_lock_hash)?;
    expect_meta_hash(proof, "toolchain_lock_hash", journal.toolchain_lock_hash)?;
    let input = parse_recursive_input(req)?;
    let facts = recursive_verified_facts_from_disclosure(
        &journal,
        &receipt.journal.bytes,
        &input,
        &receipt_profile,
    )?;
    Ok(VerifiedRecursiveFacts(facts))
}

fn verify_recursive_trusted_expectations(
    req: &Value,
    journal: &RecursiveEpochJournalV1,
    receipt_profile: &ReceiptSecurityProfile,
) -> Result<(), String> {
    const KEYS: &[&str] = &[
        "risc0_image_id",
        "receipt_codec",
        "receipt_kind",
        "receipt_hashfn",
        "receipt_verifier_parameters",
        "receipt_control_id",
        "journal_version",
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
    ];
    let expectations = req
        .get("recursive_expectations")
        .and_then(Value::as_object)
        .ok_or_else(|| {
            "recursive_expectations missing for recursive proof verification".to_string()
        })?;
    if let Some(key) = expectations
        .keys()
        .find(|key| !KEYS.contains(&key.as_str()))
    {
        return Err(format!("recursive_expectations.{key} unknown"));
    }
    if let Some(key) = KEYS.iter().find(|key| !expectations.contains_key(**key)) {
        return Err(format!("recursive_expectations.{key} missing"));
    }
    expect_recursive_expectation_image_id(
        expectations,
        "risc0_image_id",
        TAU_STATE_PROOF_AGGREGATE_ID,
    )?;
    expect_recursive_expectation_str(expectations, "receipt_codec", RECEIPT_CODEC_V1)?;
    expect_recursive_expectation_str(
        expectations,
        "receipt_kind",
        ProofReceiptKind::Succinct.as_str(),
    )?;
    if receipt_profile.kind != ProofReceiptKind::Succinct {
        return Err("recursive receipt security profile kind mismatch".into());
    }
    expect_recursive_expectation_str(
        expectations,
        "receipt_hashfn",
        receipt_profile
            .hashfn
            .as_deref()
            .ok_or_else(|| "recursive receipt hash function missing".to_string())?,
    )?;
    expect_recursive_expectation_str(
        expectations,
        "receipt_verifier_parameters",
        &receipt_profile.verifier_parameters,
    )?;
    expect_recursive_expectation_str(
        expectations,
        "receipt_control_id",
        receipt_profile
            .control_id
            .as_deref()
            .ok_or_else(|| "recursive receipt control ID missing".to_string())?,
    )?;
    expect_recursive_expectation_u64(
        expectations,
        "journal_version",
        journal.journal_version as u64,
    )?;
    expect_recursive_expectation_str(expectations, "proof_type", &journal.proof_type)?;
    expect_recursive_expectation_str(expectations, "domain_separator", &journal.domain_separator)?;
    expect_recursive_expectation_str(expectations, "chain_id", &journal.chain_id)?;
    expect_recursive_expectation_u64(expectations, "epoch_id", journal.epoch_id)?;
    expect_recursive_expectation_str(expectations, "proof_profile", &journal.proof_profile)?;
    expect_recursive_expectation_hash(expectations, "statement_hash", journal.statement_hash)?;
    expect_recursive_expectation_hash(
        expectations,
        "verifier_set_root",
        journal.verifier_set_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "allowed_authority_roots_root",
        journal.allowed_authority_roots_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "child_verification_claims_root",
        journal.child_verification_claims_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "child_journals_root",
        journal.child_journals_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "child_effect_summaries_root",
        journal.child_effect_summaries_root,
    )?;
    expect_recursive_expectation_u64(expectations, "child_count", journal.child_count as u64)?;
    expect_recursive_expectation_hash(expectations, "pre_state_root", journal.pre_state_root)?;
    expect_recursive_expectation_hash(expectations, "post_state_root", journal.post_state_root)?;
    expect_recursive_expectation_hash(expectations, "tx_root", journal.tx_root)?;
    expect_recursive_expectation_hash(expectations, "evidence_root", journal.evidence_root)?;
    expect_recursive_expectation_hash(expectations, "receipt_root", journal.receipt_root)?;
    expect_recursive_expectation_hash(
        expectations,
        "accepted_receipts_root",
        journal.accepted_receipts_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "rejected_receipts_root",
        journal.rejected_receipts_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "aggregate_asset_delta_root",
        journal.aggregate_asset_delta_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "cross_shard_outbox_root",
        journal.cross_shard_outbox_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "cross_shard_inbox_root",
        journal.cross_shard_inbox_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "cross_shard_message_ids_root",
        journal.cross_shard_message_ids_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "carry_queue_pre_root",
        journal.carry_queue_pre_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "carry_queue_post_root",
        journal.carry_queue_post_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "conflict_schedule_hash",
        journal.conflict_schedule_hash,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "data_availability_root",
        journal.data_availability_root,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "public_policy_hash",
        journal.public_policy_hash,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "feature_suite_hash",
        journal.feature_suite_hash,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "dependency_lock_hash",
        journal.dependency_lock_hash,
    )?;
    expect_recursive_expectation_hash(
        expectations,
        "toolchain_lock_hash",
        journal.toolchain_lock_hash,
    )?;
    Ok(())
}

fn expect_recursive_expectation_image_id(
    expectations: &serde_json::Map<String, Value>,
    key: &str,
    expected: [u32; 8],
) -> Result<(), String> {
    let actual = expectations
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("recursive_expectations.{key} missing"))?;
    if normalize_hex64(actual) != hex_u32_words(expected) {
        return Err(format!("recursive_expectations.{key} mismatch"));
    }
    Ok(())
}

fn expect_recursive_expectation_hash(
    expectations: &serde_json::Map<String, Value>,
    key: &str,
    expected: [u8; 32],
) -> Result<(), String> {
    let actual = expectations
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("recursive_expectations.{key} missing"))?;
    if parse_hex32(actual)? != expected {
        return Err(format!("recursive_expectations.{key} mismatch"));
    }
    Ok(())
}

fn expect_recursive_expectation_str(
    expectations: &serde_json::Map<String, Value>,
    key: &str,
    expected: &str,
) -> Result<(), String> {
    let actual = expectations
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("recursive_expectations.{key} missing"))?;
    if actual != expected {
        return Err(format!("recursive_expectations.{key} mismatch"));
    }
    Ok(())
}

fn expect_recursive_expectation_u64(
    expectations: &serde_json::Map<String, Value>,
    key: &str,
    expected: u64,
) -> Result<(), String> {
    let actual = expectations
        .get(key)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("recursive_expectations.{key} missing"))?;
    if actual != expected {
        return Err(format!("recursive_expectations.{key} mismatch"));
    }
    Ok(())
}

fn try_verify_recursive_summary_leaf(
    proof: &Value,
    expected_state_hash: [u8; 32],
) -> Result<(), String> {
    check_proof_meta_image_id_for(proof, TAU_STATE_PROOF_SUMMARY_LEAF_ID)?;
    let receipt = decode_verified_profile_receipt_from_proof(
        proof,
        TAU_STATE_PROOF_SUMMARY_LEAF_ID,
        RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
        "summary leaf receipt",
    )?;
    let journal: RecursiveEffectSummaryV1 =
        decode_postcard_journal(&receipt, "recursive summary leaf journal")?;
    if journal.proof_profile != RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1 {
        return Err("recursive summary leaf profile mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_SUMMARY_LEAF_ID {
        return Err("recursive summary leaf image id mismatch".into());
    }
    if journal.post_state_root != expected_state_hash {
        return Err("journal.post_state_root mismatch".into());
    }
    validate_recursive_effect_summary_shape_v1(&journal).map_err(transition_error_str)?;
    expect_meta_str(proof, "proof_type", PROOF_TYPE_RECURSIVE_SUMMARY_LEAF)?;
    expect_meta_str(
        proof,
        "proof_profile",
        RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
    )?;
    expect_meta_hash(proof, "statement_hash", journal.statement_hash)?;
    expect_meta_hash(proof, "pre_state_root", journal.pre_state_root)?;
    expect_meta_hash(proof, "post_state_root", journal.post_state_root)?;
    expect_meta_hash(proof, "asset_delta_root", journal.asset_delta_root)?;
    expect_meta_hash(proof, "receipt_root", journal.receipt_root)?;
    Ok(())
}

fn try_verify_recursive_spot_leaf(
    proof: &Value,
    expected_state_hash: [u8; 32],
) -> Result<(), String> {
    check_proof_meta_image_id_for(proof, TAU_STATE_PROOF_SPOT_LEAF_ID)?;
    let receipt = decode_verified_profile_receipt_from_proof(
        proof,
        TAU_STATE_PROOF_SPOT_LEAF_ID,
        RECURSIVE_SPOT_LEAF_PROFILE_V1,
        "spot leaf receipt",
    )?;
    let journal: RecursiveEffectSummaryV1 =
        decode_postcard_journal(&receipt, "recursive spot leaf journal")?;
    if journal.proof_profile != RECURSIVE_SPOT_LEAF_PROFILE_V1 {
        return Err("recursive spot leaf profile mismatch".into());
    }
    if journal.lane_kind != "spot" {
        return Err("recursive spot leaf lane kind mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_SPOT_LEAF_ID {
        return Err("recursive spot leaf image id mismatch".into());
    }
    if journal.post_state_root != expected_state_hash {
        return Err("journal.post_state_root mismatch".into());
    }
    validate_recursive_effect_summary_shape_v1(&journal).map_err(transition_error_str)?;
    expect_meta_str(proof, "proof_type", PROOF_TYPE_RECURSIVE_SPOT_LEAF)?;
    expect_meta_str(proof, "proof_profile", RECURSIVE_SPOT_LEAF_PROFILE_V1)?;
    expect_meta_hash(proof, "statement_hash", journal.statement_hash)?;
    expect_meta_hash(proof, "pre_state_root", journal.pre_state_root)?;
    expect_meta_hash(proof, "post_state_root", journal.post_state_root)?;
    expect_meta_hash(proof, "tx_root", journal.tx_root)?;
    expect_meta_hash(proof, "evidence_root", journal.evidence_root)?;
    expect_meta_hash(proof, "receipt_root", journal.receipt_root)?;
    expect_meta_hash(proof, "asset_delta_root", journal.asset_delta_root)?;
    expect_recursive_asset_delta_rows_meta(proof, journal.asset_delta_root)?;
    Ok(())
}

fn try_verify_recursive_perps_np_leaf(
    proof: &Value,
    expected_state_hash: [u8; 32],
) -> Result<(), String> {
    check_proof_meta_image_id_for(proof, TAU_STATE_PROOF_PERPS_NP_LEAF_ID)?;
    let receipt = decode_verified_profile_receipt_from_proof(
        proof,
        TAU_STATE_PROOF_PERPS_NP_LEAF_ID,
        RECURSIVE_PERPS_NP_LEAF_PROFILE_V1,
        "perps NP leaf receipt",
    )?;
    let journal: RecursiveEffectSummaryV1 =
        decode_postcard_journal(&receipt, "recursive perps NP leaf journal")?;
    if journal.proof_profile != RECURSIVE_PERPS_NP_LEAF_PROFILE_V1 {
        return Err("recursive perps NP leaf profile mismatch".into());
    }
    if journal.lane_kind != "perps_np" {
        return Err("recursive perps NP leaf lane kind mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_PERPS_NP_LEAF_ID {
        return Err("recursive perps NP leaf image id mismatch".into());
    }
    if journal.post_state_root != expected_state_hash {
        return Err("journal.post_state_root mismatch".into());
    }
    validate_recursive_effect_summary_shape_v1(&journal).map_err(transition_error_str)?;
    expect_meta_str(proof, "proof_type", PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF)?;
    expect_meta_str(proof, "proof_profile", RECURSIVE_PERPS_NP_LEAF_PROFILE_V1)?;
    expect_meta_hash(proof, "statement_hash", journal.statement_hash)?;
    expect_meta_hash(proof, "pre_state_root", journal.pre_state_root)?;
    expect_meta_hash(proof, "post_state_root", journal.post_state_root)?;
    expect_meta_hash(proof, "tx_root", journal.tx_root)?;
    expect_meta_hash(proof, "evidence_root", journal.evidence_root)?;
    expect_meta_hash(proof, "receipt_root", journal.receipt_root)?;
    expect_meta_hash(proof, "asset_delta_root", journal.asset_delta_root)?;
    expect_recursive_asset_delta_rows_meta(proof, journal.asset_delta_root)?;
    Ok(())
}

fn try_verify_recursive_zusd_leaf(
    proof: &Value,
    expected_state_hash: [u8; 32],
) -> Result<(), String> {
    check_proof_meta_image_id_for(proof, TAU_STATE_PROOF_ZUSD_LEAF_ID)?;
    let receipt = decode_verified_profile_receipt_from_proof(
        proof,
        TAU_STATE_PROOF_ZUSD_LEAF_ID,
        RECURSIVE_ZUSD_LEAF_PROFILE_V1,
        "zUSD leaf receipt",
    )?;
    let journal: RecursiveEffectSummaryV1 =
        decode_postcard_journal(&receipt, "recursive zUSD leaf journal")?;
    if journal.proof_profile != RECURSIVE_ZUSD_LEAF_PROFILE_V1 {
        return Err("recursive zUSD leaf profile mismatch".into());
    }
    if journal.lane_kind != "zusd" {
        return Err("recursive zUSD leaf lane kind mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_ZUSD_LEAF_ID {
        return Err("recursive zUSD leaf image id mismatch".into());
    }
    if journal.post_state_root != expected_state_hash {
        return Err("journal.post_state_root mismatch".into());
    }
    validate_recursive_effect_summary_shape_v1(&journal).map_err(transition_error_str)?;
    expect_meta_str(proof, "proof_type", PROOF_TYPE_RECURSIVE_ZUSD_LEAF)?;
    expect_meta_str(proof, "proof_profile", RECURSIVE_ZUSD_LEAF_PROFILE_V1)?;
    expect_meta_hash(proof, "statement_hash", journal.statement_hash)?;
    expect_meta_hash(proof, "pre_state_root", journal.pre_state_root)?;
    expect_meta_hash(proof, "post_state_root", journal.post_state_root)?;
    expect_meta_hash(proof, "tx_root", journal.tx_root)?;
    expect_meta_hash(proof, "evidence_root", journal.evidence_root)?;
    expect_meta_hash(proof, "receipt_root", journal.receipt_root)?;
    expect_meta_hash(proof, "asset_delta_root", journal.asset_delta_root)?;
    expect_recursive_asset_delta_rows_meta(proof, journal.asset_delta_root)?;
    Ok(())
}

fn verify_surface_request_bindings(
    req: &Value,
    proof: &Value,
    expected: SurfaceBindingExpectations<'_>,
) -> Result<(), String> {
    let context = req
        .get("context")
        .and_then(Value::as_object)
        .ok_or_else(|| "context must be an object for strict surface verification".to_string())?;
    let expected_chain = req
        .get("chain_id")
        .and_then(Value::as_str)
        .or_else(|| context.get("chain_id").and_then(Value::as_str))
        .ok_or_else(|| "chain_id missing for strict surface verification".to_string())?;
    if expected_chain != expected.journal_chain_id {
        return Err("chain_id mismatch".into());
    }
    let tau_state = req
        .get("tau_state")
        .and_then(Value::as_object)
        .ok_or_else(|| "tau_state must be an object for strict surface verification".to_string())?;
    let expected_post = tau_state
        .get("app_hash")
        .and_then(Value::as_str)
        .ok_or_else(|| "tau_state.app_hash missing".to_string())
        .and_then(parse_hex32_err)?;
    if expected_post != expected.post_app_hash {
        return Err("post_app_hash mismatch".into());
    }
    let expected_pre_raw = context
        .get("app_hash_pre")
        .and_then(Value::as_str)
        .ok_or_else(|| "context.app_hash_pre missing".to_string())?;
    if expected_pre_raw.trim().is_empty() {
        if expected.pre_app_hash_present {
            return Err("pre_app_hash present but expected empty".into());
        }
    } else {
        let expected_pre = parse_hex32(expected_pre_raw)?;
        if !expected.pre_app_hash_present {
            return Err("pre_app_hash missing but expected present".into());
        }
        if expected_pre != expected.pre_app_hash {
            return Err("pre_app_hash mismatch".into());
        }
    }
    expect_meta_hash(proof, "post_app_hash", expected.post_app_hash)?;
    expect_meta_pre_hash(proof, expected.pre_app_hash_present, expected.pre_app_hash)?;
    expect_meta_hash(proof, "operation_hash", expected.operation_hash)?;
    expect_meta_hash(proof, "state_delta_hash", expected.state_delta_hash)?;
    expect_meta_hash(proof, "oracle_binding_hash", expected.oracle_binding_hash)?;
    expect_meta_hash(proof, "participant_set_hash", expected.participant_set_hash)?;
    expect_context_hash(context, "operation_hash", expected.operation_hash)?;
    expect_context_hash(context, "state_delta_hash", expected.state_delta_hash)?;
    expect_context_hash(context, "oracle_binding_hash", expected.oracle_binding_hash)?;
    expect_context_hash(
        context,
        "participant_set_hash",
        expected.participant_set_hash,
    )?;
    Ok(())
}

fn validate_embedded_methods() {
    validate_embedded_method("guest", TAU_STATE_PROOF_GUEST_ELF, TAU_STATE_PROOF_GUEST_ID)
        .unwrap_or_else(|e| die(&e));
}

fn validate_aggregate_method() {
    validate_embedded_method(
        "aggregate",
        TAU_STATE_PROOF_AGGREGATE_ELF,
        TAU_STATE_PROOF_AGGREGATE_ID,
    )
    .unwrap_or_else(|e| die(&e));
}

fn validate_summary_leaf_method() {
    validate_embedded_method(
        "summary leaf",
        TAU_STATE_PROOF_SUMMARY_LEAF_ELF,
        TAU_STATE_PROOF_SUMMARY_LEAF_ID,
    )
    .unwrap_or_else(|e| die(&e));
}

fn validate_spot_leaf_method() {
    validate_embedded_method(
        "spot leaf",
        TAU_STATE_PROOF_SPOT_LEAF_ELF,
        TAU_STATE_PROOF_SPOT_LEAF_ID,
    )
    .unwrap_or_else(|e| die(&e));
}

fn validate_perps_np_leaf_method() {
    validate_embedded_method(
        "perps NP leaf",
        TAU_STATE_PROOF_PERPS_NP_LEAF_ELF,
        TAU_STATE_PROOF_PERPS_NP_LEAF_ID,
    )
    .unwrap_or_else(|e| die(&e));
}

fn validate_zusd_leaf_method() {
    validate_embedded_method(
        "zUSD leaf",
        TAU_STATE_PROOF_ZUSD_LEAF_ELF,
        TAU_STATE_PROOF_ZUSD_LEAF_ID,
    )
    .unwrap_or_else(|e| die(&e));
}

fn validate_embedded_method(label: &str, program: &[u8], image_id: [u32; 8]) -> Result<(), String> {
    if program.is_empty() {
        return Err(format!(
            "Risc0 {label} program is empty (methods not embedded); rebuild with RISC0_FORCE_BUILD=1"
        ));
    }
    if image_id.iter().all(|word| *word == 0) {
        return Err(format!(
            "Risc0 {label} image ID is all-zero (methods not embedded); rebuild with RISC0_FORCE_BUILD=1"
        ));
    }
    let computed = compute_image_id(program)
        .map_err(|e| format!("Risc0 {label} program image ID computation failed: {e}"))?;
    if computed != Digest::from(image_id) {
        return Err(format!("Risc0 {label} embedded program/image ID mismatch"));
    }
    Ok(())
}

fn prove_guest_input<T>(guest_input: &ZenoProofInputV1) -> (Receipt, T)
where
    T: DeserializeOwned,
{
    prove_direct_guest_input(
        guest_input,
        TAU_STATE_PROOF_GUEST_ELF,
        TAU_STATE_PROOF_GUEST_ID,
        &[],
        ProofReceiptKind::Composite,
    )
}

fn prove_aggregate_input_with_assumptions<T>(
    input: &RecursiveCompositionInputV1,
    assumptions: &[Receipt],
) -> (Receipt, T)
where
    T: DeserializeOwned,
{
    prove_direct_guest_input(
        input,
        TAU_STATE_PROOF_AGGREGATE_ELF,
        TAU_STATE_PROOF_AGGREGATE_ID,
        assumptions,
        ProofReceiptKind::Succinct,
    )
}

fn prove_direct_guest_input<I, T>(
    input: &I,
    elf: &[u8],
    image_id: [u32; 8],
    assumptions: &[Receipt],
    expected_receipt_kind: ProofReceiptKind,
) -> (Receipt, T)
where
    I: serde::Serialize,
    T: DeserializeOwned,
{
    if risc0_dev_mode_env_enabled() {
        die("RISC0_DEV_MODE set: prover refuses dev mode");
    }
    let input_bytes = postcard::to_allocvec(input)
        .unwrap_or_else(|e| die(&format!("failed to encode postcard input: {e}")));
    let input_len: u32 = input_bytes
        .len()
        .try_into()
        .unwrap_or_else(|_| die("guest input too large"));
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]).write_slice(&input_bytes);
    for receipt in assumptions {
        builder.add_assumption(receipt.clone());
    }
    let env = builder
        .build()
        .unwrap_or_else(|e| die(&format!("failed to build env: {e}")));

    let prover = default_prover();
    let prover_opts = prover_opts(expected_receipt_kind).unwrap_or_else(|e| die(&e));
    let prove_info = prover
        .prove_with_opts(env, elf, &prover_opts)
        .unwrap_or_else(|e| die(&format!("proving failed: {e}")));
    let receipt = prove_info.receipt;
    require_actual_receipt_kind(&receipt, expected_receipt_kind)
        .unwrap_or_else(|e| die(&format!("generated {e}")));
    receipt
        .verify(image_id)
        .unwrap_or_else(|e| die(&format!("receipt verification failed: {e}")));
    let journal: T = decode_postcard_journal(&receipt, "journal")
        .unwrap_or_else(|e| die(&format!("failed to decode {e}")));
    (receipt, journal)
}

fn decode_postcard_journal<T>(receipt: &Receipt, name: &str) -> Result<T, String>
where
    T: DeserializeOwned,
{
    postcard::from_bytes(&receipt.journal.bytes).map_err(|e| format!("{name} postcard bytes: {e}"))
}

fn prover_opts(receipt_kind: ProofReceiptKind) -> Result<ProverOpts, String> {
    match receipt_kind {
        ProofReceiptKind::Composite => Ok(ProverOpts::composite()),
        ProofReceiptKind::Succinct => Ok(ProverOpts::succinct()),
        ProofReceiptKind::Groth16 => Ok(ProverOpts::groth16()),
        ProofReceiptKind::Fake => Err("fake receipt kind cannot be requested from prover".into()),
    }
}

fn receipt_kind(receipt: &Receipt) -> Result<ProofReceiptKind, String> {
    match &receipt.inner {
        InnerReceipt::Composite(_) => Ok(ProofReceiptKind::Composite),
        InnerReceipt::Succinct(_) => Ok(ProofReceiptKind::Succinct),
        InnerReceipt::Groth16(_) => Ok(ProofReceiptKind::Groth16),
        InnerReceipt::Fake(_) => Ok(ProofReceiptKind::Fake),
        _ => Err("unsupported RISC0 receipt kind".into()),
    }
}

fn receipt_security_profile(receipt: &Receipt) -> Result<ReceiptSecurityProfile, String> {
    let kind = receipt_kind(receipt)?;
    let (hashfn, control_id) = match &receipt.inner {
        InnerReceipt::Succinct(inner) => (
            Some(inner.hashfn.clone()),
            Some(inner.control_id.to_string()),
        ),
        InnerReceipt::Composite(_) | InnerReceipt::Groth16(_) | InnerReceipt::Fake(_) => {
            (None, None)
        }
        _ => return Err("unsupported RISC0 receipt kind".into()),
    };
    Ok(ReceiptSecurityProfile {
        kind,
        verifier_parameters: receipt.metadata.verifier_parameters.to_string(),
        hashfn,
        control_id,
    })
}

fn expected_receipt_kind_for_profile(profile: &str) -> Result<ProofReceiptKind, String> {
    match profile {
        RECURSIVE_EPOCH_PROFILE_V1
        | RECURSIVE_SPOT_LEAF_PROFILE_V1
        | RECURSIVE_PERPS_NP_LEAF_PROFILE_V1
        | RECURSIVE_ZUSD_LEAF_PROFILE_V1 => Ok(ProofReceiptKind::Succinct),
        RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1 => Ok(ProofReceiptKind::Composite),
        _ => Err(format!(
            "receipt kind policy has no entry for profile {profile}"
        )),
    }
}

fn require_receipt_kind_for_profile(profile: &str, actual: ProofReceiptKind) -> Result<(), String> {
    if actual == ProofReceiptKind::Fake {
        return Err("receipt kind policy rejects fake receipt".into());
    }
    let expected = expected_receipt_kind_for_profile(profile)?;
    if actual != expected {
        return Err(format!(
            "receipt kind mismatch for profile {profile}: expected {}, got {}",
            expected.as_str(),
            actual.as_str()
        ));
    }
    Ok(())
}

fn require_recursive_child_receipt_kind(
    profile: &str,
    actual: ProofReceiptKind,
) -> Result<(), String> {
    if actual != ProofReceiptKind::Succinct {
        return Err(format!(
            "recursive child receipt kind mismatch: expected succinct, got {}",
            actual.as_str()
        ));
    }
    require_receipt_kind_for_profile(profile, actual)
}

fn require_actual_receipt_kind(
    receipt: &Receipt,
    expected: ProofReceiptKind,
) -> Result<(), String> {
    let actual = receipt_kind(receipt)?;
    if actual != expected {
        return Err(format!(
            "receipt kind mismatch: expected {}, got {}",
            expected.as_str(),
            actual.as_str()
        ));
    }
    Ok(())
}

fn require_requested_receipt_kind(req: &Value, expected: ProofReceiptKind) -> Result<(), String> {
    let raw = req
        .get("receipt_kind")
        .and_then(Value::as_str)
        .ok_or_else(|| "receipt_kind missing".to_string())?;
    let declared =
        ProofReceiptKind::parse(raw).ok_or_else(|| "receipt_kind unsupported".to_string())?;
    if declared != expected {
        return Err(format!(
            "receipt_kind mismatch: expected {}, got {}",
            expected.as_str(),
            declared.as_str()
        ));
    }
    Ok(())
}

fn require_proof_meta_receipt_kind(proof: &Value, actual: ProofReceiptKind) -> Result<(), String> {
    let raw = proof_meta_obj(proof)?
        .get("receipt_kind")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof.meta.receipt_kind missing".to_string())?;
    let declared = ProofReceiptKind::parse(raw)
        .ok_or_else(|| "proof.meta.receipt_kind unsupported".to_string())?;
    if declared != actual {
        return Err(format!(
            "proof.meta.receipt_kind mismatch: declared {}, actual {}",
            declared.as_str(),
            actual.as_str()
        ));
    }
    Ok(())
}

fn require_receipt_codec(value: Option<&Value>, name: &str) -> Result<(), String> {
    let codec = value
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{name} missing"))?;
    if codec != RECEIPT_CODEC_V1 {
        return Err(format!("{name} unsupported"));
    }
    Ok(())
}

fn require_proof_meta_receipt_security(proof: &Value, receipt: &Receipt) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    require_receipt_codec(meta.get("receipt_codec"), "proof.meta.receipt_codec")?;
    let profile = receipt_security_profile(receipt)?;
    require_proof_meta_receipt_kind(proof, profile.kind)?;
    expect_meta_str(
        proof,
        "receipt_verifier_parameters",
        &profile.verifier_parameters,
    )?;
    match (&profile.hashfn, &profile.control_id) {
        (Some(hashfn), Some(control_id)) => {
            expect_meta_str(proof, "receipt_hashfn", hashfn)?;
            expect_meta_str(proof, "receipt_control_id", control_id)?;
        }
        (None, None) => {
            if meta.get("receipt_hashfn") != Some(&Value::Null) {
                return Err("proof.meta.receipt_hashfn must be null".into());
            }
            if meta.get("receipt_control_id") != Some(&Value::Null) {
                return Err("proof.meta.receipt_control_id must be null".into());
            }
        }
        _ => return Err("receipt security profile incomplete".into()),
    }
    Ok(())
}

fn insert_receipt_security_meta(
    meta: &mut serde_json::Map<String, Value>,
    receipt: &Receipt,
) -> Result<(), String> {
    let profile = receipt_security_profile(receipt)?;
    meta.insert(
        "receipt_codec".to_string(),
        Value::String(RECEIPT_CODEC_V1.to_string()),
    );
    meta.insert(
        "receipt_kind".to_string(),
        Value::String(profile.kind.as_str().to_string()),
    );
    meta.insert(
        "receipt_verifier_parameters".to_string(),
        Value::String(profile.verifier_parameters),
    );
    meta.insert(
        "receipt_hashfn".to_string(),
        profile.hashfn.map(Value::String).unwrap_or(Value::Null),
    );
    meta.insert(
        "receipt_control_id".to_string(),
        profile.control_id.map(Value::String).unwrap_or(Value::Null),
    );
    Ok(())
}

fn attach_receipt_security_meta(mut meta: Value, receipt: &Receipt) -> Value {
    let object = meta
        .as_object_mut()
        .unwrap_or_else(|| die("proof metadata must be an object"));
    insert_receipt_security_meta(object, receipt).unwrap_or_else(|e| die(&e));
    meta
}

fn encode_receipt(receipt: &Receipt) -> String {
    let receipt_bytes = serde_json::to_vec(receipt)
        .unwrap_or_else(|e| die(&format!("failed to serialize receipt: {e}")));
    require_receipt_bytes_len(receipt_bytes.len()).unwrap_or_else(|e| die(&e));
    base64::engine::general_purpose::STANDARD.encode(receipt_bytes)
}

fn decode_verified_receipt_from_proof(proof: &Value) -> Result<Receipt, String> {
    let receipt = decode_receipt_from_proof(proof)?;
    reject_dev_mode_receipt(&receipt, "receipt")?;
    receipt
        .verify(TAU_STATE_PROOF_GUEST_ID)
        .map_err(|e| format!("receipt verification failed: {e}"))?;
    require_proof_meta_receipt_security(proof, &receipt)?;
    Ok(receipt)
}

fn decode_verified_profile_receipt_from_proof(
    proof: &Value,
    image_id: [u32; 8],
    profile: &str,
    label: &str,
) -> Result<Receipt, String> {
    let receipt = decode_receipt_from_proof(proof)?;
    reject_dev_mode_receipt(&receipt, label)?;
    let actual_kind = receipt_kind(&receipt)?;
    require_receipt_kind_for_profile(profile, actual_kind)?;
    receipt
        .verify(image_id)
        .map_err(|e| format!("{label} verification failed: {e}"))?;
    require_proof_meta_receipt_security(proof, &receipt)?;
    Ok(receipt)
}

mod recursive_receipt_authentication {
    use super::*;

    pub(super) struct AuthenticatedReceipt {
        receipt: Receipt,
        security_profile: ReceiptSecurityProfile,
    }

    impl AuthenticatedReceipt {
        pub(super) fn into_parts(self) -> (Receipt, ReceiptSecurityProfile) {
            (self.receipt, self.security_profile)
        }

        #[cfg(test)]
        pub(super) fn from_test_parts(
            receipt: Receipt,
            security_profile: ReceiptSecurityProfile,
        ) -> Self {
            Self {
                receipt,
                security_profile,
            }
        }
    }

    pub(super) fn authenticate(proof: &Value) -> Result<AuthenticatedReceipt, String> {
        let receipt = decode_verified_profile_receipt_from_proof(
            proof,
            TAU_STATE_PROOF_AGGREGATE_ID,
            RECURSIVE_EPOCH_PROFILE_V1,
            "receipt",
        )?;
        let security_profile = receipt_security_profile(&receipt)?;
        Ok(AuthenticatedReceipt {
            receipt,
            security_profile,
        })
    }
}

fn decode_receipt_from_proof(proof: &Value) -> Result<Receipt, String> {
    let meta = proof_meta_obj(proof)?;
    require_receipt_codec(meta.get("receipt_codec"), "proof.meta.receipt_codec")?;
    let proof_b64 = proof
        .get("proof")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof.proof missing".to_string())?;
    decode_receipt_b64(proof_b64)
}

fn decode_receipt_b64(proof_b64: &str) -> Result<Receipt, String> {
    require_receipt_base64_len(proof_b64.len())?;
    let proof_bytes = base64::engine::general_purpose::STANDARD
        .decode(proof_b64)
        .map_err(|e| format!("invalid base64 proof: {e}"))?;
    require_receipt_bytes_len(proof_bytes.len())?;
    let receipt: Receipt =
        serde_json::from_slice(&proof_bytes).map_err(|e| format!("invalid receipt bytes: {e}"))?;
    let canonical = serde_json::to_vec(&receipt)
        .map_err(|e| format!("failed to canonicalize receipt bytes: {e}"))?;
    if canonical != proof_bytes {
        return Err("receipt bytes are not canonical for declared codec".into());
    }
    Ok(receipt)
}

fn require_receipt_base64_len(encoded_len: usize) -> Result<(), String> {
    if encoded_len > MAX_RECEIPT_BASE64_BYTES {
        return Err(format!(
            "receipt base64 exceeds {MAX_RECEIPT_BASE64_BYTES} byte limit"
        ));
    }
    Ok(())
}

fn require_receipt_bytes_len(decoded_len: usize) -> Result<(), String> {
    if decoded_len > MAX_RECEIPT_BYTES {
        return Err(format!(
            "receipt bytes exceed {MAX_RECEIPT_BYTES} byte limit"
        ));
    }
    Ok(())
}

fn reject_dev_mode_receipt(receipt: &Receipt, label: &str) -> Result<(), String> {
    if risc0_dev_mode_env_enabled() {
        return Err("RISC0_DEV_MODE set: verifier refuses dev-mode receipts".into());
    }
    reject_fake_receipt(receipt, label)
}

fn reject_fake_receipt(receipt: &Receipt, label: &str) -> Result<(), String> {
    if matches!(&receipt.inner, InnerReceipt::Fake(_)) {
        return Err(format!("{label} fake receipt rejected"));
    }
    Ok(())
}

fn risc0_dev_mode_env_enabled() -> bool {
    match std::env::var("RISC0_DEV_MODE") {
        Ok(value) => risc0_dev_mode_value_enabled(&value),
        Err(_) => false,
    }
}

fn risc0_dev_mode_value_enabled(value: &str) -> bool {
    matches!(
        value.trim().to_ascii_lowercase().as_str(),
        "1" | "true" | "yes" | "on"
    )
}

fn expected_post_app_hash_hex(req: &Value) -> String {
    if let Some(v) = req.get("expected_post_app_hash").and_then(Value::as_str) {
        return v.trim().to_string();
    }
    req.get("tau_state")
        .and_then(|v| v.get("app_hash"))
        .and_then(Value::as_str)
        .map(|s| s.trim().to_string())
        .filter(|s| !s.is_empty())
        .unwrap_or_else(|| die("tau_state.app_hash or expected_post_app_hash missing/empty"))
}

fn chain_id_from_request(req: &Value, context: &Value) -> String {
    req.get("chain_id")
        .and_then(Value::as_str)
        .or_else(|| context.get("chain_id").and_then(Value::as_str))
        .map(str::trim)
        .filter(|s| !s.is_empty())
        .map(str::to_string)
        .unwrap_or_else(|| die("chain_id missing/empty"))
}

fn parse_pre_app_hash_context(context: &serde_json::Map<String, Value>) -> (bool, [u8; 32]) {
    let pre_app_hash_hex = context
        .get("app_hash_pre")
        .and_then(Value::as_str)
        .unwrap_or("")
        .trim()
        .to_string();
    if pre_app_hash_hex.is_empty() {
        (false, [0u8; 32])
    } else {
        (
            true,
            parse_hex32(&pre_app_hash_hex).unwrap_or_else(|e| die(&e)),
        )
    }
}

fn value_obj<'a>(v: &'a Value, name: &str) -> Result<&'a serde_json::Map<String, Value>, String> {
    v.as_object()
        .ok_or_else(|| format!("{name} must be an object"))
}

fn value_array<'a>(v: &'a Value, name: &str) -> Result<&'a Vec<Value>, String> {
    v.as_array().ok_or_else(|| format!("{name} must be a list"))
}

fn obj_str(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    default: Option<&str>,
) -> Result<String, String> {
    match obj.get(key) {
        Some(Value::String(s)) if !s.trim().is_empty() || default.is_some() => Ok(s.clone()),
        Some(Value::String(_)) => Err(format!("{key} must be non-empty")),
        Some(_) => Err(format!("{key} must be a string")),
        None => default
            .map(str::to_string)
            .ok_or_else(|| format!("{key} missing")),
    }
}

fn parse_i128_value(v: &Value, name: &str) -> Result<i128, String> {
    if let Some(n) = v.as_i64() {
        return Ok(n as i128);
    }
    if let Some(n) = v.as_u64() {
        return Ok(n as i128);
    }
    if let Some(s) = v.as_str() {
        return s
            .trim()
            .parse::<i128>()
            .map_err(|_| format!("{name} must be an i128"));
    }
    if let Some(n) = v.as_number() {
        return n
            .to_string()
            .parse::<i128>()
            .map_err(|_| format!("{name} must be an i128"));
    }
    Err(format!("{name} must be an i128"))
}

fn parse_u128_value(v: &Value, name: &str) -> Result<u128, String> {
    if let Some(n) = v.as_u64() {
        return Ok(n as u128);
    }
    if let Some(n) = v.as_i64() {
        if n >= 0 {
            return Ok(n as u128);
        }
    }
    if let Some(s) = v.as_str() {
        return s
            .trim()
            .parse::<u128>()
            .map_err(|_| format!("{name} must be a u128"));
    }
    if let Some(n) = v.as_number() {
        return n
            .to_string()
            .parse::<u128>()
            .map_err(|_| format!("{name} must be a u128"));
    }
    Err(format!("{name} must be a u128"))
}

fn obj_i128(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    default: Option<i128>,
) -> Result<i128, String> {
    match obj.get(key) {
        Some(v) => parse_i128_value(v, key),
        None => default.ok_or_else(|| format!("{key} missing")),
    }
}

fn obj_u128(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    default: Option<u128>,
) -> Result<u128, String> {
    match obj.get(key) {
        Some(v) => parse_u128_value(v, key),
        None => default.ok_or_else(|| format!("{key} missing")),
    }
}

fn obj_u64(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    default: Option<u64>,
) -> Result<u64, String> {
    let n = obj_i128(obj, key, default.map(|v| v as i128))?;
    if n < 0 || n > u64::MAX as i128 {
        return Err(format!("{key} must be a u64"));
    }
    Ok(n as u64)
}

fn obj_u32(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    default: Option<u32>,
) -> Result<u32, String> {
    let n = obj_u64(obj, key, default.map(|v| v as u64))?;
    if n > u32::MAX as u64 {
        return Err(format!("{key} must be a u32"));
    }
    Ok(n as u32)
}

fn parse_protocol_fee_context(
    context: &serde_json::Map<String, Value>,
) -> Result<ProtocolFeeFields, String> {
    let share_bps = match context.get("protocol_fee_share_bps") {
        None => 0,
        Some(Value::Number(n)) => {
            let raw = n
                .as_u64()
                .ok_or_else(|| "context.protocol_fee_share_bps must be a u32".to_string())?;
            if raw > u32::MAX as u64 {
                return Err("context.protocol_fee_share_bps must be a u32".to_string());
            }
            raw as u32
        }
        Some(_) => return Err("context.protocol_fee_share_bps must be a u32".to_string()),
    };
    if share_bps > 10_000 {
        return Err("context.protocol_fee_share_bps out of range".to_string());
    }
    let recipient_pubkey = match context.get("protocol_fee_recipient_pubkey") {
        None => None,
        Some(Value::String(s)) if s.trim().is_empty() => None,
        Some(Value::String(s)) => Some(s.clone()),
        Some(_) => return Err("context.protocol_fee_recipient_pubkey must be a string".to_string()),
    };
    if share_bps > 0 && recipient_pubkey.is_none() {
        return Err(
            "context.protocol_fee_recipient_pubkey required when share_bps > 0".to_string(),
        );
    }
    Ok(ProtocolFeeFields {
        share_bps,
        recipient_pubkey,
    })
}

fn parse_tx_execution_order_context(
    context: &serde_json::Map<String, Value>,
) -> Result<Vec<u32>, String> {
    let Some(value) = context.get("tx_execution_order") else {
        return Ok(Vec::new());
    };
    let entries = value
        .as_array()
        .ok_or_else(|| "context.tx_execution_order must be a list".to_string())?;
    let mut order = Vec::with_capacity(entries.len());
    for entry in entries {
        let raw = entry
            .as_u64()
            .ok_or_else(|| "context.tx_execution_order entries must be u32".to_string())?;
        if raw > u32::MAX as u64 {
            return Err("context.tx_execution_order entries must be u32".to_string());
        }
        order.push(raw as u32);
    }
    Ok(order)
}

fn parse_route_price_intervals_context(
    context: &serde_json::Map<String, Value>,
) -> Result<Vec<RoutePriceIntervalV1>, String> {
    let Some(value) = context.get("route_price_intervals") else {
        return Ok(Vec::new());
    };
    if !value.is_array() {
        return Err("context.route_price_intervals must be a list".to_string());
    }
    serde_json::from_value(value.clone())
        .map_err(|e| format!("context.route_price_intervals schema mismatch: {e}"))
}

fn parse_optional_u64_field(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    name: &str,
) -> Result<Option<u64>, String> {
    let Some(value) = obj.get(key) else {
        return Ok(None);
    };
    if value.is_null() {
        return Ok(None);
    }
    let parsed = parse_u128_value(value, name)?;
    if parsed > u64::MAX as u128 {
        return Err(format!("{name} must be a u64"));
    }
    Ok(Some(parsed as u64))
}

fn parse_route_price_interval_max_width_bps_context(
    context: &serde_json::Map<String, Value>,
) -> Result<Option<u64>, String> {
    parse_optional_u64_field(
        context,
        "route_price_interval_max_width_bps",
        "context.route_price_interval_max_width_bps",
    )
}

fn parse_route_price_interval_max_width_bps_meta(
    meta: &serde_json::Map<String, Value>,
) -> Result<Option<u64>, String> {
    parse_optional_u64_field(
        meta,
        "route_price_interval_max_width_bps",
        "proof.meta.route_price_interval_max_width_bps",
    )
}

fn parse_route_price_interval_authority_context(
    context: &serde_json::Map<String, Value>,
) -> Result<Option<RoutePriceIntervalAuthorityV1>, String> {
    let Some(value) = context.get("route_price_interval_authority") else {
        return Ok(None);
    };
    if value.is_null() {
        return Ok(None);
    }
    let obj = value_obj(value, "context.route_price_interval_authority")?;
    let source_root_hex = obj_str(obj, "source_root", None)?;
    let route_price_intervals_root_hex = obj_str(obj, "route_price_intervals_root", None)?;
    Ok(Some(RoutePriceIntervalAuthorityV1 {
        schema: obj_str(obj, "schema", None)?,
        source_id: obj_str(obj, "source_id", None)?,
        source_root: parse_hex32(&source_root_hex)
            .map_err(|e| format!("context.route_price_interval_authority.source_root {e}"))?,
        price_timestamp: obj_u64(obj, "price_timestamp", None)?,
        max_staleness_seconds: obj_u64(obj, "max_staleness_seconds", None)?,
        route_price_intervals_root: parse_hex32(&route_price_intervals_root_hex).map_err(|e| {
            format!("context.route_price_interval_authority.route_price_intervals_root {e}")
        })?,
    }))
}

fn parse_route_price_interval_authority_policy_context(
    context: &serde_json::Map<String, Value>,
) -> Result<Option<RoutePriceIntervalAuthorityPolicyV1>, String> {
    let Some(value) = context.get("route_price_interval_authority_policy") else {
        return Ok(None);
    };
    if value.is_null() {
        return Ok(None);
    }
    let obj = value_obj(value, "context.route_price_interval_authority_policy")?;
    let sources_value = obj.get("sources").ok_or_else(|| {
        "context.route_price_interval_authority_policy.sources missing".to_string()
    })?;
    let sources = sources_value.as_array().ok_or_else(|| {
        "context.route_price_interval_authority_policy.sources must be a list".to_string()
    })?;
    let mut parsed_sources = Vec::with_capacity(sources.len());
    for (index, source_value) in sources.iter().enumerate() {
        let source_obj = value_obj(
            source_value,
            &format!("context.route_price_interval_authority_policy.sources[{index}]"),
        )?;
        let source_root_hex = obj_str(source_obj, "source_root", None)?;
        let verification_root_hex = obj_str(source_obj, "verification_root", None)?;
        parsed_sources.push(RoutePriceIntervalAuthorityPolicySourceV1 {
            source_id: obj_str(source_obj, "source_id", None)?,
            source_root: parse_hex32(&source_root_hex).map_err(|e| {
                format!("context.route_price_interval_authority_policy.sources[{index}].source_root {e}")
            })?,
            verification_root: parse_hex32(&verification_root_hex).map_err(|e| {
                format!("context.route_price_interval_authority_policy.sources[{index}].verification_root {e}")
            })?,
            verification_status: obj_str(source_obj, "verification_status", None)?,
        });
    }
    Ok(Some(RoutePriceIntervalAuthorityPolicyV1 {
        schema: obj_str(obj, "schema", None)?,
        policy_id: obj_str(obj, "policy_id", None)?,
        sources: parsed_sources,
    }))
}

fn parse_frontier_signature_certificates_context(
    context: &serde_json::Map<String, Value>,
) -> Result<Vec<SharedPoolFrontierSignatureCertificateV1>, String> {
    let Some(value) = context.get("shared_pool_frontier_signature_certificates") else {
        return Ok(Vec::new());
    };
    if !value.is_array() {
        return Err(
            "context.shared_pool_frontier_signature_certificates must be a list".to_string(),
        );
    }
    serde_json::from_value(value.clone()).map_err(|e| {
        format!("context.shared_pool_frontier_signature_certificates schema mismatch: {e}")
    })
}

fn parse_protocol_fee_meta(
    meta: &serde_json::Map<String, Value>,
) -> Result<ProtocolFeeFields, String> {
    let share_bps = match meta.get("protocol_fee_share_bps") {
        Some(Value::Number(n)) => {
            let raw = n
                .as_u64()
                .ok_or_else(|| "proof.meta.protocol_fee_share_bps must be a u32".to_string())?;
            if raw > u32::MAX as u64 {
                return Err("proof.meta.protocol_fee_share_bps must be a u32".to_string());
            }
            raw as u32
        }
        Some(_) => return Err("proof.meta.protocol_fee_share_bps must be a u32".to_string()),
        None => 0,
    };
    if share_bps > 10_000 {
        return Err("proof.meta.protocol_fee_share_bps out of range".to_string());
    }
    let recipient_pubkey = match meta.get("protocol_fee_recipient_pubkey") {
        Some(Value::Null) => None,
        Some(Value::String(s)) if s.trim().is_empty() => None,
        Some(Value::String(s)) => Some(s.clone()),
        Some(_) => {
            return Err(
                "proof.meta.protocol_fee_recipient_pubkey must be a string or null".to_string(),
            )
        }
        None => None,
    };
    if share_bps > 0 && recipient_pubkey.is_none() {
        return Err(
            "proof.meta.protocol_fee_recipient_pubkey required when share_bps > 0".to_string(),
        );
    }
    Ok(ProtocolFeeFields {
        share_bps,
        recipient_pubkey,
    })
}

fn obj_i32(
    obj: &serde_json::Map<String, Value>,
    key: &str,
    default: Option<i32>,
) -> Result<i32, String> {
    let n = obj_i128(obj, key, default.map(|v| v as i128))?;
    if n < i32::MIN as i128 || n > i32::MAX as i128 {
        return Err(format!("{key} must be an i32"));
    }
    Ok(n as i32)
}

fn parse_oracle_binding_value(v: &Value) -> Result<OracleBindingV1, String> {
    let obj = value_obj(v, "oracle")?;
    Ok(OracleBindingV1 {
        oracle_bridge_id: obj_str(obj, "oracle_bridge_id", None)?,
        oracle_bridge_hash: obj_str(obj, "oracle_bridge_hash", None)?,
        price_e8: obj_i128(obj, "price_e8", None)?,
        price_timestamp: obj_u64(obj, "price_timestamp", None)?,
        max_staleness_seconds: obj_u64(obj, "max_staleness_seconds", None)?,
        observed_at: obj_u64(obj, "observed_at", None)?,
        pre_price_batch_commitment: obj_str(obj, "pre_price_batch_commitment", None)?,
    })
}

fn parse_collateral_binding_value(v: &Value) -> Result<CollateralBindingV1, String> {
    let obj = value_obj(v, "collateral_binding")?;
    Ok(CollateralBindingV1 {
        source_proof_type: obj_str(obj, "source_proof_type", None)?,
        source_state_hash: obj_str(obj, "source_state_hash", None)?,
        balance_root_hash: obj_str(obj, "balance_root_hash", None)?,
        balance_delta_hash: obj_str(obj, "balance_delta_hash", None)?,
    })
}

fn parse_perps_params_value(v: Option<&Value>) -> Result<PerpsMarketParamsV1, String> {
    let default = PerpsMarketParamsV1::default();
    let Some(v) = v else { return Ok(default) };
    let obj = value_obj(v, "params")?;
    Ok(PerpsMarketParamsV1 {
        initial_margin_bps: obj_u32(obj, "initial_margin_bps", Some(default.initial_margin_bps))?,
        maintenance_margin_bps: obj_u32(
            obj,
            "maintenance_margin_bps",
            Some(default.maintenance_margin_bps),
        )?,
        depeg_buffer_bps: obj_u32(obj, "depeg_buffer_bps", Some(default.depeg_buffer_bps))?,
        liquidation_penalty_bps: obj_u32(
            obj,
            "liquidation_penalty_bps",
            Some(default.liquidation_penalty_bps),
        )?,
        max_oracle_move_bps: obj_u32(
            obj,
            "max_oracle_move_bps",
            Some(default.max_oracle_move_bps),
        )?,
        funding_cap_bps: obj_i32(obj, "funding_cap_bps", Some(default.funding_cap_bps))?,
        max_position_abs: obj_i128(obj, "max_position_abs", Some(default.max_position_abs))?,
        min_notional_for_bounty_e8: obj_i128(
            obj,
            "min_notional_for_bounty_e8",
            Some(default.min_notional_for_bounty_e8),
        )?,
    })
}

fn parse_perps_account_value(v: &Value) -> Result<PerpsAccountV1, String> {
    let obj = value_obj(v, "perps account")?;
    Ok(PerpsAccountV1 {
        pubkey: obj_str(obj, "pubkey", None)?,
        position_base: obj_i128(obj, "position_base", Some(0))?,
        entry_price_e8: obj_i128(obj, "entry_price_e8", Some(0))?,
        collateral_e8: obj_i128(obj, "collateral_e8", Some(0))?,
        funding_paid_cum_e8: obj_i128(obj, "funding_paid_cum_e8", Some(0))?,
        nonce: obj_u64(obj, "nonce", Some(0))?,
    })
}

fn parse_perps_intent_value(v: &Value) -> Result<PerpsIntentV1, String> {
    let obj = value_obj(v, "perps intent")?;
    Ok(PerpsIntentV1 {
        pubkey: obj_str(obj, "pubkey", None)?,
        target_base: obj_i128(obj, "target_base", None)?,
        limit_price_e8: obj_i128(obj, "limit_price_e8", Some(0))?,
        min_fill_base: obj_i128(obj, "min_fill_base", Some(0))?,
        expiry_epoch: obj_u64(obj, "expiry_epoch", Some(1u64 << 62))?,
        nonce: obj_u64(obj, "nonce", None)?,
    })
}

fn parse_optional_collateral_binding_value(
    obj: &serde_json::Map<String, Value>,
) -> Result<Option<CollateralBindingV1>, String> {
    match obj.get("collateral_binding") {
        None | Some(Value::Null) => Ok(None),
        Some(v) => parse_collateral_binding_value(v).map(Some),
    }
}

fn parse_optional_perps_intents_value(
    obj: &serde_json::Map<String, Value>,
    key: &str,
) -> Result<Vec<PerpsIntentV1>, String> {
    let Some(value) = obj.get(key) else {
        return Ok(Vec::new());
    };
    value_array(value, key)?
        .iter()
        .map(parse_perps_intent_value)
        .collect()
}

fn parse_perps_snapshot_value(v: &Value) -> Result<PerpsNpSnapshotV1, String> {
    let obj = value_obj(v, "perps snapshot")?;
    let accounts = match obj.get("accounts") {
        None => Vec::new(),
        Some(value) => value_array(value, "accounts")?
            .iter()
            .map(parse_perps_account_value)
            .collect::<Result<Vec<_>, _>>()?,
    };
    let pending_intents = parse_optional_perps_intents_value(obj, "pending_intents")?;
    Ok(PerpsNpSnapshotV1 {
        version: obj_u32(obj, "version", Some(1))?,
        market_id: obj_str(obj, "market_id", Some(""))?,
        collateral_asset: obj_str(obj, "collateral_asset", Some("zUSD"))?,
        index_price_e8: obj_i128(obj, "index_price_e8", Some(0))?,
        params: parse_perps_params_value(obj.get("params"))?,
        accounts,
        pending_intents,
        now_epoch: obj_u64(obj, "now_epoch", Some(0))?,
        fee_pool_e8: obj_i128(obj, "fee_pool_e8", Some(0))?,
        insurance_e8: obj_i128(obj, "insurance_e8", Some(0))?,
        insurance_ext_e8: obj_i128(obj, "insurance_ext_e8", Some(0))?,
        claims_paid_e8: obj_i128(obj, "claims_paid_e8", Some(0))?,
        net_deposited_e8: obj_i128(obj, "net_deposited_e8", Some(0))?,
    })
}

fn parse_perps_action_value(v: &Value) -> Result<PerpsNpActionV1, String> {
    let obj = value_obj(v, "perps action")?;
    let kind = obj_str(obj, "kind", None)?;
    match kind.as_str() {
        "init_market" => Ok(PerpsNpActionV1::InitMarket {
            market_id: obj_str(obj, "market_id", None)?,
            collateral_asset: obj_str(obj, "collateral_asset", Some("zUSD"))?,
            index_price_e8: obj_i128(obj, "index_price_e8", None)?,
            params: parse_perps_params_value(obj.get("params"))?,
            insurance_seed_e8: obj_i128(obj, "insurance_seed_e8", Some(0))?,
        }),
        "deposit_collateral" => Ok(PerpsNpActionV1::DepositCollateral {
            pubkey: obj_str(obj, "pubkey", None)?,
            asset: obj_str(obj, "asset", Some("zUSD"))?,
            amount_e8: obj_i128(obj, "amount_e8", None)?,
            nonce: obj_u64(obj, "nonce", None)?,
            collateral_binding: parse_optional_collateral_binding_value(obj)?,
        }),
        "withdraw_collateral" => Ok(PerpsNpActionV1::WithdrawCollateral {
            pubkey: obj_str(obj, "pubkey", None)?,
            asset: obj_str(obj, "asset", Some("zUSD"))?,
            amount_e8: obj_i128(obj, "amount_e8", None)?,
            nonce: obj_u64(obj, "nonce", None)?,
        }),
        "submit_intent" => {
            let intent = obj
                .get("intent")
                .ok_or_else(|| "intent missing".to_string())
                .and_then(parse_perps_intent_value)?;
            Ok(PerpsNpActionV1::SubmitIntent { intent })
        }
        "run_epoch" => {
            let oracle = obj
                .get("oracle")
                .ok_or_else(|| "oracle missing".to_string())
                .and_then(parse_oracle_binding_value)?;
            Ok(PerpsNpActionV1::RunEpoch {
                oracle,
                clearing_price_e8: obj_i128(obj, "clearing_price_e8", None)?,
                funding_rate_bps: obj_i32(obj, "funding_rate_bps", Some(0))?,
                intents: parse_optional_perps_intents_value(obj, "intents")?,
            })
        }
        _ => Err(format!("unsupported perps action kind: {kind}")),
    }
}

fn parse_perps_actions_value(v: &Value) -> Result<Vec<PerpsNpActionV1>, String> {
    value_array(v, "actions")?
        .iter()
        .map(parse_perps_action_value)
        .collect()
}

fn parse_zusd_vault_value(v: &Value) -> Result<ZusdVaultEntryV1, String> {
    let obj = value_obj(v, "zUSD vault")?;
    Ok(ZusdVaultEntryV1 {
        pubkey: obj_str(obj, "pubkey", None)?,
        collateral_asset: obj_str(obj, "collateral_asset", None)?,
        collateral_amount_e8: obj_u128(obj, "collateral_amount_e8", Some(0))?,
        debt_zusd_e8: obj_u128(obj, "debt_zusd_e8", Some(0))?,
        nonce: obj_u64(obj, "nonce", Some(0))?,
    })
}

fn parse_zusd_balance_value(v: &Value) -> Result<ZusdBalanceEntryV1, String> {
    let obj = value_obj(v, "zUSD balance")?;
    Ok(ZusdBalanceEntryV1 {
        pubkey: obj_str(obj, "pubkey", None)?,
        amount_e8: obj_u128(obj, "amount_e8", Some(0))?,
    })
}

fn parse_zusd_snapshot_value(v: &Value) -> Result<ZusdSnapshotV1, String> {
    let obj = value_obj(v, "zUSD snapshot")?;
    let vaults = match obj.get("vaults") {
        None => Vec::new(),
        Some(value) => value_array(value, "vaults")?
            .iter()
            .map(parse_zusd_vault_value)
            .collect::<Result<Vec<_>, _>>()?,
    };
    let balances = match obj.get("balances") {
        None => Vec::new(),
        Some(value) => value_array(value, "balances")?
            .iter()
            .map(parse_zusd_balance_value)
            .collect::<Result<Vec<_>, _>>()?,
    };
    Ok(ZusdSnapshotV1 {
        version: obj_u32(obj, "version", Some(1))?,
        vaults,
        balances,
        total_debt_zusd_e8: obj_u128(obj, "total_debt_zusd_e8", Some(0))?,
    })
}

fn parse_zusd_operation_value(v: &Value) -> Result<ZusdOperationV1, String> {
    let obj = value_obj(v, "zUSD operation")?;
    let kind = obj_str(obj, "kind", None)?;
    match kind.as_str() {
        "deposit_mint" => {
            let oracle = obj
                .get("oracle")
                .ok_or_else(|| "oracle missing".to_string())
                .and_then(parse_oracle_binding_value)?;
            Ok(ZusdOperationV1::DepositMint {
                pubkey: obj_str(obj, "pubkey", None)?,
                collateral_asset: obj_str(obj, "collateral_asset", None)?,
                deposit_amount_e8: obj_u128(obj, "deposit_amount_e8", None)?,
                mint_amount_e8: obj_u128(obj, "mint_amount_e8", None)?,
                oracle,
                mcr_bps: obj_u32(obj, "mcr_bps", None)?,
                nonce: obj_u64(obj, "nonce", None)?,
            })
        }
        _ => Err(format!("unsupported zUSD operation kind: {kind}")),
    }
}

fn parse_perps_pre_state(req: &Value, context: &Value) -> PerpsNpSnapshotV1 {
    let value = req
        .get("pre_state")
        .or_else(|| context.get("perps_state_pre"))
        .or_else(|| context.get("app_state_pre"));
    let Some(value) = value else {
        return PerpsNpSnapshotV1::empty();
    };
    if let Some(s) = value.as_str() {
        if s.trim().is_empty() {
            return PerpsNpSnapshotV1::empty();
        }
        let parsed = strict_json::parse_value(s)
            .unwrap_or_else(|e| die(&format!("perps pre_state invalid JSON: {e}")));
        return parse_perps_snapshot_value(&parsed)
            .unwrap_or_else(|e| die(&format!("perps pre_state schema mismatch: {e}")));
    }
    parse_perps_snapshot_value(value)
        .unwrap_or_else(|e| die(&format!("perps pre_state schema mismatch: {e}")))
}

fn parse_zusd_pre_state(req: &Value, context: &Value) -> ZusdSnapshotV1 {
    let value = req
        .get("pre_state")
        .or_else(|| context.get("zusd_state_pre"))
        .or_else(|| context.get("app_state_pre"));
    let Some(value) = value else {
        return ZusdSnapshotV1::empty();
    };
    if let Some(s) = value.as_str() {
        if s.trim().is_empty() {
            return ZusdSnapshotV1::empty();
        }
        let parsed = strict_json::parse_value(s)
            .unwrap_or_else(|e| die(&format!("zUSD pre_state invalid JSON: {e}")));
        return parse_zusd_snapshot_value(&parsed)
            .unwrap_or_else(|e| die(&format!("zUSD pre_state schema mismatch: {e}")));
    }
    parse_zusd_snapshot_value(value)
        .unwrap_or_else(|e| die(&format!("zUSD pre_state schema mismatch: {e}")))
}

fn parse_verify_perps_actions(req: &Value) -> Result<Vec<PerpsNpActionV1>, String> {
    let value = req
        .get("actions")
        .ok_or_else(|| "actions missing for strict perps np verification".to_string())?;
    let actions =
        parse_perps_actions_value(value).map_err(|e| format!("actions schema mismatch: {e}"))?;
    if actions.is_empty() {
        return Err("actions must be non-empty for strict perps np verification".into());
    }
    Ok(actions)
}

fn parse_verify_zusd_operation(req: &Value) -> Result<ZusdOperationV1, String> {
    let value = req
        .get("operation")
        .ok_or_else(|| "operation missing for strict zUSD verification".to_string())?;
    parse_zusd_operation_value(value).map_err(|e| format!("operation schema mismatch: {e}"))
}

fn parse_recursive_input(req: &Value) -> Result<RecursiveCompositionInputV1, String> {
    let value = req
        .get("recursive_input")
        .cloned()
        .ok_or_else(|| "recursive_input missing for recursive proof".to_string())?;
    recursive_wire::validate_composition(&value)?;
    let input: RecursiveCompositionInputV1 = serde_json::from_value(value)
        .map_err(|e| format!("recursive_input schema mismatch: {e}"))?;
    compose_recursive_epoch_journal_v1(&input).map_err(transition_error_str)?;
    Ok(input)
}

fn parse_spot_recursive_leaf_input(req: &Value) -> Result<SpotRecursiveLeafInputV1, String> {
    let value = req
        .get("spot_recursive_leaf_input")
        .cloned()
        .ok_or_else(|| {
            "spot_recursive_leaf_input missing for recursive spot leaf proof".to_string()
        })?;
    recursive_wire::validate_spot_leaf(&value)?;
    let input: SpotRecursiveLeafInputV1 = serde_json::from_value(value)
        .map_err(|e| format!("spot_recursive_leaf_input schema mismatch: {e}"))?;
    compose_spot_recursive_leaf_summary_v1(input.clone()).map_err(transition_error_str)?;
    Ok(input)
}

fn parse_perps_np_recursive_leaf_input(req: &Value) -> Result<PerpsNpRecursiveLeafInputV1, String> {
    let value = req
        .get("perps_np_recursive_leaf_input")
        .cloned()
        .ok_or_else(|| {
            "perps_np_recursive_leaf_input missing for recursive perps NP leaf proof".to_string()
        })?;
    recursive_wire::validate_perps_leaf(&value)?;
    let input: PerpsNpRecursiveLeafInputV1 = serde_json::from_value(value)
        .map_err(|e| format!("perps_np_recursive_leaf_input schema mismatch: {e}"))?;
    compose_perps_np_recursive_leaf_summary_v1(input.clone()).map_err(transition_error_str)?;
    Ok(input)
}

fn parse_zusd_recursive_leaf_input(req: &Value) -> Result<ZusdRecursiveLeafInputV1, String> {
    let value = req
        .get("zusd_recursive_leaf_input")
        .cloned()
        .ok_or_else(|| {
            "zusd_recursive_leaf_input missing for recursive zUSD leaf proof".to_string()
        })?;
    recursive_wire::validate_zusd_leaf(&value)?;
    let input: ZusdRecursiveLeafInputV1 = serde_json::from_value(value)
        .map_err(|e| format!("zusd_recursive_leaf_input schema mismatch: {e}"))?;
    compose_zusd_recursive_leaf_summary_v1(input.clone()).map_err(transition_error_str)?;
    Ok(input)
}

fn parse_recursive_summary(req: &Value) -> Result<RecursiveEffectSummaryV1, String> {
    let value = req
        .get("recursive_summary")
        .cloned()
        .ok_or_else(|| "recursive_summary missing for recursive summary leaf proof".to_string())?;
    recursive_wire::validate_summary(&value, "recursive_summary")?;
    let summary: RecursiveEffectSummaryV1 = serde_json::from_value(value)
        .map_err(|e| format!("recursive_summary schema mismatch: {e}"))?;
    validate_recursive_effect_summary_shape_v1(&summary).map_err(transition_error_str)?;
    Ok(summary)
}

fn parse_recursive_child_receipts(
    req: &Value,
    input: &RecursiveCompositionInputV1,
) -> Result<Vec<Receipt>, String> {
    require_receipt_codec(req.get("child_receipt_codec"), "child_receipt_codec")?;
    let values = req
        .get("child_proofs")
        .and_then(Value::as_array)
        .ok_or_else(|| "child_proofs must be a list".to_string())?;
    if values.len() != input.children.len() {
        return Err("child_proofs length mismatch".into());
    }
    let mut receipts = Vec::with_capacity(values.len());
    for (index, value) in values.iter().enumerate() {
        let proof_b64 = value
            .as_str()
            .ok_or_else(|| format!("child_proofs[{index}] must be a base64 receipt"))?;
        let receipt =
            decode_receipt_b64(proof_b64).map_err(|e| format!("child_proofs[{index}]: {e}"))?;
        reject_dev_mode_receipt(&receipt, &format!("child_proofs[{index}] receipt"))?;
        let child = &input.children[index];
        let actual_kind = receipt_kind(&receipt)?;
        require_recursive_child_receipt_kind(&child.descriptor.child_profile, actual_kind)
            .map_err(|e| format!("child_proofs[{index}]: {e}"))?;
        receipt
            .verify(child.descriptor.child_image_id)
            .map_err(|e| format!("child_proofs[{index}] verification failed: {e}"))?;
        if receipt.journal.bytes != child.child_journal_bytes {
            return Err(format!("child_proofs[{index}] journal bytes mismatch"));
        }
        receipts.push(receipt);
    }
    Ok(receipts)
}

fn perps_np_meta(journal: &PerpsNpTransitionJournalV1) -> Value {
    json!({
        "risc0_image_id": hex_u32_words(journal.risc0_image_id),
        "chain_id": journal.chain_id,
        "pre_app_hash": if journal.pre_app_hash_present { hex_lower(&journal.pre_app_hash) } else { String::new() },
        "post_app_hash": hex_lower(&journal.post_app_hash),
        "operation_hash": hex_lower(&journal.operation_hash),
        "state_delta_hash": hex_lower(&journal.state_delta_hash),
        "oracle_binding_hash": hex_lower(&journal.oracle_binding_hash),
        "collateral_binding_hash": hex_lower(&journal.collateral_binding_hash),
        "participant_set_hash": hex_lower(&journal.participant_set_hash),
        "receipt_root": hex_lower(&journal.receipt_root),
        "participant_count": journal.participant_count,
        "net_position_base": journal.net_position_base.to_string(),
        "total_collateral_e8": journal.total_collateral_e8.to_string(),
        "funding_residual_e8": journal.funding_residual_e8.to_string(),
        "matched_base_volume": journal.matched_base_volume.to_string(),
    })
}

fn zusd_meta(journal: &ZusdTransitionJournalV1) -> Value {
    json!({
        "risc0_image_id": hex_u32_words(journal.risc0_image_id),
        "chain_id": journal.chain_id,
        "pre_app_hash": if journal.pre_app_hash_present { hex_lower(&journal.pre_app_hash) } else { String::new() },
        "post_app_hash": hex_lower(&journal.post_app_hash),
        "operation_hash": hex_lower(&journal.operation_hash),
        "state_delta_hash": hex_lower(&journal.state_delta_hash),
        "oracle_binding_hash": hex_lower(&journal.oracle_binding_hash),
        "zusd_balance_root_hash": hex_lower(&journal.zusd_balance_root_hash),
        "zusd_vault_root_hash": hex_lower(&journal.zusd_vault_root_hash),
        "participant_set_hash": hex_lower(&journal.participant_set_hash),
        "minted_zusd_e8": journal.minted_zusd_e8.to_string(),
        "collateral_value_e8": journal.collateral_value_e8.to_string(),
        "mcr_bps": journal.mcr_bps,
    })
}

fn recursive_meta(journal: &RecursiveEpochJournalV1, receipt_kind: ProofReceiptKind) -> Value {
    json!({
        "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_AGGREGATE_ID),
        "receipt_kind": receipt_kind.as_str(),
        "proof_type": journal.proof_type,
        "domain_separator": journal.domain_separator,
        "chain_id": journal.chain_id,
        "epoch_id": journal.epoch_id,
        "proof_profile": journal.proof_profile,
        "statement_hash": hex_lower(&journal.statement_hash),
        "verifier_set_root": hex_lower(&journal.verifier_set_root),
        "allowed_authority_roots_root": hex_lower(&journal.allowed_authority_roots_root),
        "child_verification_claims_root": hex_lower(&journal.child_verification_claims_root),
        "child_journals_root": hex_lower(&journal.child_journals_root),
        "child_effect_summaries_root": hex_lower(&journal.child_effect_summaries_root),
        "child_count": journal.child_count,
        "pre_state_root": hex_lower(&journal.pre_state_root),
        "post_state_root": hex_lower(&journal.post_state_root),
        "tx_root": hex_lower(&journal.tx_root),
        "evidence_root": hex_lower(&journal.evidence_root),
        "receipt_root": hex_lower(&journal.receipt_root),
        "accepted_receipts_root": hex_lower(&journal.accepted_receipts_root),
        "rejected_receipts_root": hex_lower(&journal.rejected_receipts_root),
        "aggregate_asset_delta_root": hex_lower(&journal.aggregate_asset_delta_root),
        "cross_shard_outbox_root": hex_lower(&journal.cross_shard_outbox_root),
        "cross_shard_inbox_root": hex_lower(&journal.cross_shard_inbox_root),
        "cross_shard_message_ids_root": hex_lower(&journal.cross_shard_message_ids_root),
        "carry_queue_pre_root": hex_lower(&journal.carry_queue_pre_root),
        "carry_queue_post_root": hex_lower(&journal.carry_queue_post_root),
        "conflict_schedule_hash": hex_lower(&journal.conflict_schedule_hash),
        "data_availability_root": hex_lower(&journal.data_availability_root),
        "public_policy_hash": hex_lower(&journal.public_policy_hash),
        "feature_suite_hash": hex_lower(&journal.feature_suite_hash),
        "dependency_lock_hash": hex_lower(&journal.dependency_lock_hash),
        "toolchain_lock_hash": hex_lower(&journal.toolchain_lock_hash),
    })
}

fn recursive_summary_leaf_meta(
    journal: &RecursiveEffectSummaryV1,
    receipt_kind: ProofReceiptKind,
) -> Value {
    json!({
        "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_SUMMARY_LEAF_ID),
        "receipt_kind": receipt_kind.as_str(),
        "proof_type": PROOF_TYPE_RECURSIVE_SUMMARY_LEAF,
        "summary_version": journal.summary_version,
        "lane_id": journal.lane_id,
        "lane_kind": journal.lane_kind,
        "chain_id": journal.chain_id,
        "epoch_id": journal.epoch_id,
        "proof_profile": journal.proof_profile,
        "child_image_id": hex_u32_words(journal.risc0_image_id),
        "statement_hash": hex_lower(&journal.statement_hash),
        "pre_state_root": hex_lower(&journal.pre_state_root),
        "post_state_root": hex_lower(&journal.post_state_root),
        "tx_root": hex_lower(&journal.tx_root),
        "evidence_root": hex_lower(&journal.evidence_root),
        "receipt_root": hex_lower(&journal.receipt_root),
        "accepted_receipts_root": hex_lower(&journal.accepted_receipts_root),
        "rejected_receipts_root": hex_lower(&journal.rejected_receipts_root),
        "asset_delta_root": hex_lower(&journal.asset_delta_root),
        "cross_shard_outbox_root": hex_lower(&journal.cross_shard_outbox_root),
        "cross_shard_inbox_root": hex_lower(&journal.cross_shard_inbox_root),
        "write_set_root": hex_lower(&journal.write_set_root),
        "public_policy_hash": hex_lower(&journal.public_policy_hash),
        "feature_suite_hash": hex_lower(&journal.feature_suite_hash),
        "dependency_lock_hash": hex_lower(&journal.dependency_lock_hash),
        "toolchain_lock_hash": hex_lower(&journal.toolchain_lock_hash),
    })
}

fn recursive_spot_leaf_meta(
    journal: &RecursiveEffectSummaryV1,
    asset_delta_rows: &[RecursiveAssetDeltaRowV1],
    receipt_kind: ProofReceiptKind,
) -> Value {
    json!({
        "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_SPOT_LEAF_ID),
        "receipt_kind": receipt_kind.as_str(),
        "proof_type": PROOF_TYPE_RECURSIVE_SPOT_LEAF,
        "summary_version": journal.summary_version,
        "lane_id": journal.lane_id,
        "lane_kind": journal.lane_kind,
        "chain_id": journal.chain_id,
        "epoch_id": journal.epoch_id,
        "proof_profile": journal.proof_profile,
        "child_image_id": hex_u32_words(journal.risc0_image_id),
        "statement_hash": hex_lower(&journal.statement_hash),
        "pre_state_root": hex_lower(&journal.pre_state_root),
        "post_state_root": hex_lower(&journal.post_state_root),
        "tx_root": hex_lower(&journal.tx_root),
        "evidence_root": hex_lower(&journal.evidence_root),
        "receipt_root": hex_lower(&journal.receipt_root),
        "accepted_receipts_root": hex_lower(&journal.accepted_receipts_root),
        "rejected_receipts_root": hex_lower(&journal.rejected_receipts_root),
        "asset_delta_root": hex_lower(&journal.asset_delta_root),
        "asset_delta_rows": recursive_asset_delta_rows_meta(asset_delta_rows),
        "cross_shard_outbox_root": hex_lower(&journal.cross_shard_outbox_root),
        "cross_shard_inbox_root": hex_lower(&journal.cross_shard_inbox_root),
        "write_set_root": hex_lower(&journal.write_set_root),
        "public_policy_hash": hex_lower(&journal.public_policy_hash),
        "feature_suite_hash": hex_lower(&journal.feature_suite_hash),
        "dependency_lock_hash": hex_lower(&journal.dependency_lock_hash),
        "toolchain_lock_hash": hex_lower(&journal.toolchain_lock_hash),
    })
}

fn recursive_perps_np_leaf_meta(
    journal: &RecursiveEffectSummaryV1,
    asset_delta_rows: &[RecursiveAssetDeltaRowV1],
    receipt_kind: ProofReceiptKind,
) -> Value {
    json!({
        "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_PERPS_NP_LEAF_ID),
        "receipt_kind": receipt_kind.as_str(),
        "proof_type": PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF,
        "summary_version": journal.summary_version,
        "lane_id": journal.lane_id,
        "lane_kind": journal.lane_kind,
        "chain_id": journal.chain_id,
        "epoch_id": journal.epoch_id,
        "proof_profile": journal.proof_profile,
        "child_image_id": hex_u32_words(journal.risc0_image_id),
        "statement_hash": hex_lower(&journal.statement_hash),
        "pre_state_root": hex_lower(&journal.pre_state_root),
        "post_state_root": hex_lower(&journal.post_state_root),
        "tx_root": hex_lower(&journal.tx_root),
        "evidence_root": hex_lower(&journal.evidence_root),
        "receipt_root": hex_lower(&journal.receipt_root),
        "accepted_receipts_root": hex_lower(&journal.accepted_receipts_root),
        "rejected_receipts_root": hex_lower(&journal.rejected_receipts_root),
        "asset_delta_root": hex_lower(&journal.asset_delta_root),
        "asset_delta_rows": recursive_asset_delta_rows_meta(asset_delta_rows),
        "cross_shard_outbox_root": hex_lower(&journal.cross_shard_outbox_root),
        "cross_shard_inbox_root": hex_lower(&journal.cross_shard_inbox_root),
        "write_set_root": hex_lower(&journal.write_set_root),
        "public_policy_hash": hex_lower(&journal.public_policy_hash),
        "feature_suite_hash": hex_lower(&journal.feature_suite_hash),
        "dependency_lock_hash": hex_lower(&journal.dependency_lock_hash),
        "toolchain_lock_hash": hex_lower(&journal.toolchain_lock_hash),
    })
}

fn recursive_asset_delta_rows_meta(rows: &[RecursiveAssetDeltaRowV1]) -> Value {
    Value::Array(
        rows.iter()
            .map(|row| {
                json!({
                    "asset_id": row.asset_id.as_str(),
                    "debit_atoms": row.debit_atoms.to_string(),
                    "credit_atoms": row.credit_atoms.to_string(),
                    "authorized_mint_atoms": row.authorized_mint_atoms.to_string(),
                    "authorized_burn_atoms": row.authorized_burn_atoms.to_string(),
                    "authority_root": hex_lower(&row.authority_root),
                })
            })
            .collect(),
    )
}

fn recursive_zusd_leaf_meta(
    journal: &RecursiveEffectSummaryV1,
    asset_delta_rows: &[RecursiveAssetDeltaRowV1],
    receipt_kind: ProofReceiptKind,
) -> Value {
    json!({
        "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_ZUSD_LEAF_ID),
        "receipt_kind": receipt_kind.as_str(),
        "proof_type": PROOF_TYPE_RECURSIVE_ZUSD_LEAF,
        "summary_version": journal.summary_version,
        "lane_id": journal.lane_id,
        "lane_kind": journal.lane_kind,
        "chain_id": journal.chain_id,
        "epoch_id": journal.epoch_id,
        "proof_profile": journal.proof_profile,
        "child_image_id": hex_u32_words(journal.risc0_image_id),
        "statement_hash": hex_lower(&journal.statement_hash),
        "pre_state_root": hex_lower(&journal.pre_state_root),
        "post_state_root": hex_lower(&journal.post_state_root),
        "tx_root": hex_lower(&journal.tx_root),
        "evidence_root": hex_lower(&journal.evidence_root),
        "receipt_root": hex_lower(&journal.receipt_root),
        "accepted_receipts_root": hex_lower(&journal.accepted_receipts_root),
        "rejected_receipts_root": hex_lower(&journal.rejected_receipts_root),
        "asset_delta_root": hex_lower(&journal.asset_delta_root),
        "asset_delta_rows": recursive_asset_delta_rows_meta(asset_delta_rows),
        "cross_shard_outbox_root": hex_lower(&journal.cross_shard_outbox_root),
        "cross_shard_inbox_root": hex_lower(&journal.cross_shard_inbox_root),
        "write_set_root": hex_lower(&journal.write_set_root),
        "public_policy_hash": hex_lower(&journal.public_policy_hash),
        "feature_suite_hash": hex_lower(&journal.feature_suite_hash),
        "dependency_lock_hash": hex_lower(&journal.dependency_lock_hash),
        "toolchain_lock_hash": hex_lower(&journal.toolchain_lock_hash),
    })
}

fn check_proof_meta_image_id(proof: &Value) -> Result<(), String> {
    check_proof_meta_image_id_for(proof, TAU_STATE_PROOF_GUEST_ID)
}

fn check_proof_meta_image_id_for(proof: &Value, expected_id: [u32; 8]) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    let image_id = meta
        .get("risc0_image_id")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof.meta.risc0_image_id missing".to_string())?;
    let expected = hex_u32_words(expected_id);
    if normalize_hex64(image_id) != expected {
        return Err("risc0_image_id mismatch".into());
    }
    Ok(())
}

fn proof_meta_obj(proof: &Value) -> Result<&serde_json::Map<String, Value>, String> {
    proof
        .get("meta")
        .and_then(Value::as_object)
        .ok_or_else(|| "proof.meta must be an object".to_string())
}

fn parse_recursive_asset_delta_rows_meta(
    meta: &serde_json::Map<String, Value>,
) -> Result<Vec<RecursiveAssetDeltaRowV1>, String> {
    let rows = meta
        .get("asset_delta_rows")
        .and_then(Value::as_array)
        .ok_or_else(|| "proof.meta.asset_delta_rows missing".to_string())?;
    let mut parsed = Vec::with_capacity(rows.len());
    for (index, row) in rows.iter().enumerate() {
        let obj = row
            .as_object()
            .ok_or_else(|| format!("proof.meta.asset_delta_rows[{index}] must be an object"))?;
        let field = |key: &str| {
            obj.get(key)
                .ok_or_else(|| format!("proof.meta.asset_delta_rows[{index}].{key} missing"))
        };
        let asset_id = field("asset_id")?
            .as_str()
            .ok_or_else(|| {
                format!("proof.meta.asset_delta_rows[{index}].asset_id must be a string")
            })?
            .to_string();
        let debit_atoms = parse_u128_value(
            field("debit_atoms")?,
            "proof.meta.asset_delta_rows[].debit_atoms",
        )?;
        let credit_atoms = parse_u128_value(
            field("credit_atoms")?,
            "proof.meta.asset_delta_rows[].credit_atoms",
        )?;
        let authorized_mint_atoms = parse_u128_value(
            field("authorized_mint_atoms")?,
            "proof.meta.asset_delta_rows[].authorized_mint_atoms",
        )?;
        let authorized_burn_atoms = parse_u128_value(
            field("authorized_burn_atoms")?,
            "proof.meta.asset_delta_rows[].authorized_burn_atoms",
        )?;
        let authority_root = field("authority_root")?
            .as_str()
            .ok_or_else(|| {
                format!("proof.meta.asset_delta_rows[{index}].authority_root must be a hex string")
            })
            .and_then(parse_hex32_err)?;
        parsed.push(RecursiveAssetDeltaRowV1 {
            asset_id,
            debit_atoms,
            credit_atoms,
            authorized_mint_atoms,
            authorized_burn_atoms,
            authority_root,
        });
    }
    Ok(parsed)
}

fn expect_recursive_asset_delta_rows_meta(
    proof: &Value,
    expected_root: [u8; 32],
) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    let rows = parse_recursive_asset_delta_rows_meta(meta)?;
    let actual_root = recursive_asset_delta_root_v1(&rows).map_err(transition_error_str)?;
    if actual_root != expected_root {
        return Err("proof.meta.asset_delta_rows root mismatch".to_string());
    }
    Ok(())
}

fn check_spot_protocol_fee_bindings(
    req: &Value,
    proof: &Value,
    journal: &StateProofJournalV1,
) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    let meta_fee = parse_protocol_fee_meta(meta)?;
    if meta_fee.share_bps != journal.protocol_fee_share_bps {
        return Err("proof.meta.protocol_fee_share_bps mismatch".to_string());
    }
    if meta_fee.recipient_pubkey != journal.protocol_fee_recipient_pubkey {
        return Err("proof.meta.protocol_fee_recipient_pubkey mismatch".to_string());
    }
    let empty_route_price_intervals_root =
        route_price_intervals_root_v1(&[]).map_err(transition_error_str)?;
    let legacy_empty_route_price_intervals = journal.route_price_interval_count == 0
        && journal.route_price_intervals_root == empty_route_price_intervals_root;
    let meta_route_price_interval_count = match meta
        .get("route_price_interval_count")
        .and_then(Value::as_u64)
    {
        Some(count) => count,
        None if legacy_empty_route_price_intervals => 0,
        None => {
            return Err("proof.meta.route_price_interval_count missing/invalid".to_string());
        }
    };
    if meta_route_price_interval_count > u32::MAX as u64 {
        return Err("proof.meta.route_price_interval_count missing/invalid".to_string());
    }
    if meta_route_price_interval_count as u32 != journal.route_price_interval_count {
        return Err("proof.meta.route_price_interval_count mismatch".to_string());
    }
    if let Some(actual_root) = meta
        .get("route_price_intervals_root")
        .and_then(Value::as_str)
    {
        if normalize_hex64(actual_root) != hex_lower(&journal.route_price_intervals_root) {
            return Err("proof.meta.route_price_intervals_root mismatch".to_string());
        }
    } else if !legacy_empty_route_price_intervals {
        return Err("proof.meta.route_price_intervals_root missing".to_string());
    }
    let empty_route_price_interval_authority_root =
        route_price_interval_authority_root_v1(None).map_err(transition_error_str)?;
    let legacy_empty_route_price_interval_authority = journal.route_price_interval_count == 0
        && journal.route_price_interval_authority_root == empty_route_price_interval_authority_root;
    if let Some(actual_root) = meta
        .get("route_price_interval_authority_root")
        .and_then(Value::as_str)
    {
        if normalize_hex64(actual_root) != hex_lower(&journal.route_price_interval_authority_root) {
            return Err("proof.meta.route_price_interval_authority_root mismatch".to_string());
        }
    } else if !legacy_empty_route_price_interval_authority {
        return Err("proof.meta.route_price_interval_authority_root missing".to_string());
    }
    let empty_route_price_interval_authority_policy_root =
        route_price_interval_authority_policy_root_v1(None).map_err(transition_error_str)?;
    let legacy_empty_route_price_interval_authority_policy = journal.route_price_interval_count
        == 0
        && journal.route_price_interval_authority_policy_root
            == empty_route_price_interval_authority_policy_root;
    if let Some(actual_root) = meta
        .get("route_price_interval_authority_policy_root")
        .and_then(Value::as_str)
    {
        if normalize_hex64(actual_root)
            != hex_lower(&journal.route_price_interval_authority_policy_root)
        {
            return Err(
                "proof.meta.route_price_interval_authority_policy_root mismatch".to_string(),
            );
        }
    } else if !legacy_empty_route_price_interval_authority_policy {
        return Err("proof.meta.route_price_interval_authority_policy_root missing".to_string());
    }
    let meta_max_width = parse_route_price_interval_max_width_bps_meta(meta)?;
    if meta_max_width != journal.route_price_interval_max_width_bps {
        return Err("proof.meta.route_price_interval_max_width_bps mismatch".to_string());
    }
    if journal.route_price_interval_count > 0 {
        let trusted_policy_root = req
            .get("trusted_route_price_interval_authority_policy_root")
            .and_then(Value::as_str)
            .ok_or_else(|| {
                "trusted_route_price_interval_authority_policy_root required".to_string()
            })?;
        if normalize_hex64(trusted_policy_root)
            != hex_lower(&journal.route_price_interval_authority_policy_root)
        {
            return Err("trusted_route_price_interval_authority_policy_root mismatch".to_string());
        }
    }

    let empty_frontier_root =
        frontier_signature_certificates_root_v1(&[]).map_err(transition_error_str)?;
    let legacy_empty_frontier = journal.shared_pool_frontier_signature_certificate_count == 0
        && journal.shared_pool_frontier_signature_certificates_root == empty_frontier_root;
    let meta_frontier_count = match meta
        .get("shared_pool_frontier_signature_certificate_count")
        .and_then(Value::as_u64)
    {
        Some(count) => count,
        None if legacy_empty_frontier => 0,
        None => {
            return Err(
                "proof.meta.shared_pool_frontier_signature_certificate_count missing/invalid"
                    .to_string(),
            )
        }
    };
    if meta_frontier_count > u32::MAX as u64 {
        return Err(
            "proof.meta.shared_pool_frontier_signature_certificate_count missing/invalid"
                .to_string(),
        );
    }
    if meta_frontier_count as u32 != journal.shared_pool_frontier_signature_certificate_count {
        return Err(
            "proof.meta.shared_pool_frontier_signature_certificate_count mismatch".to_string(),
        );
    }
    if let Some(actual_root) = meta
        .get("shared_pool_frontier_signature_certificates_root")
        .and_then(Value::as_str)
    {
        if normalize_hex64(actual_root)
            != hex_lower(&journal.shared_pool_frontier_signature_certificates_root)
        {
            return Err(
                "proof.meta.shared_pool_frontier_signature_certificates_root mismatch".to_string(),
            );
        }
    } else if !legacy_empty_frontier {
        return Err(
            "proof.meta.shared_pool_frontier_signature_certificates_root missing".to_string(),
        );
    }

    if let Some(context_value) = req.get("context") {
        let context = context_value
            .as_object()
            .ok_or_else(|| "context must be an object".to_string())?;
        let context_fee = parse_protocol_fee_context(context)?;
        if context_fee.share_bps != journal.protocol_fee_share_bps {
            return Err("context.protocol_fee_share_bps mismatch".to_string());
        }
        if context_fee.recipient_pubkey != journal.protocol_fee_recipient_pubkey {
            return Err("context.protocol_fee_recipient_pubkey mismatch".to_string());
        }
        let context_route_price_intervals = parse_route_price_intervals_context(context)?;
        if context_route_price_intervals.len() as u32 != journal.route_price_interval_count {
            return Err("context.route_price_interval_count mismatch".to_string());
        }
        let context_route_price_intervals_root =
            route_price_intervals_root_v1(&context_route_price_intervals)
                .map_err(transition_error_str)?;
        if context_route_price_intervals_root != journal.route_price_intervals_root {
            return Err("context.route_price_intervals_root mismatch".to_string());
        }
        let context_route_price_interval_authority =
            parse_route_price_interval_authority_context(context)?;
        let context_route_price_interval_authority_root =
            route_price_interval_authority_root_v1(context_route_price_interval_authority.as_ref())
                .map_err(transition_error_str)?;
        if context_route_price_interval_authority_root
            != journal.route_price_interval_authority_root
        {
            return Err("context.route_price_interval_authority_root mismatch".to_string());
        }
        let context_route_price_interval_authority_policy =
            parse_route_price_interval_authority_policy_context(context)?;
        let context_route_price_interval_authority_policy_root =
            route_price_interval_authority_policy_root_v1(
                context_route_price_interval_authority_policy.as_ref(),
            )
            .map_err(transition_error_str)?;
        if context_route_price_interval_authority_policy_root
            != journal.route_price_interval_authority_policy_root
        {
            return Err("context.route_price_interval_authority_policy_root mismatch".to_string());
        }
        let context_max_width = parse_route_price_interval_max_width_bps_context(context)?;
        if context_max_width != journal.route_price_interval_max_width_bps {
            return Err("context.route_price_interval_max_width_bps mismatch".to_string());
        }
        let context_frontier_certs = parse_frontier_signature_certificates_context(context)?;
        if context_frontier_certs.len() as u32
            != journal.shared_pool_frontier_signature_certificate_count
        {
            return Err(
                "context.shared_pool_frontier_signature_certificate_count mismatch".to_string(),
            );
        }
        let context_frontier_root =
            frontier_signature_certificates_root_v1(&context_frontier_certs)
                .map_err(transition_error_str)?;
        if context_frontier_root != journal.shared_pool_frontier_signature_certificates_root {
            return Err(
                "context.shared_pool_frontier_signature_certificates_root mismatch".to_string(),
            );
        }
    }

    Ok(())
}

fn tx_execution_order_from_context(req: &Value, tx_count: usize) -> Result<Vec<usize>, String> {
    let raw_order = if let Some(context_value) = req.get("context") {
        let context = context_value
            .as_object()
            .ok_or_else(|| "context must be an object".to_string())?;
        parse_tx_execution_order_context(context)?
    } else {
        Vec::new()
    };
    if raw_order.is_empty() {
        return Ok((0..tx_count).collect());
    }
    if raw_order.len() != tx_count {
        return Err("context.tx_execution_order length mismatch".to_string());
    }

    let mut seen = vec![false; tx_count];
    let mut order = Vec::with_capacity(tx_count);
    for raw_index in raw_order {
        let index = usize::try_from(raw_index)
            .map_err(|_| "context.tx_execution_order entries must be u32".to_string())?;
        if index >= tx_count {
            return Err("context.tx_execution_order index out of range".to_string());
        }
        if seen[index] {
            return Err("context.tx_execution_order duplicate index".to_string());
        }
        seen[index] = true;
        order.push(index);
    }
    Ok(order)
}

fn strict_context_obj(req: &Value) -> Result<&serde_json::Map<String, Value>, String> {
    req.get("context")
        .and_then(Value::as_object)
        .ok_or_else(|| "context must be an object for strict surface verification".to_string())
}

fn expect_meta_hash(proof: &Value, key: &str, expected: [u8; 32]) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    let actual = meta
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("proof.meta.{key} missing"))?;
    if normalize_hex64(actual) != hex_lower(&expected) {
        return Err(format!("proof.meta.{key} mismatch"));
    }
    Ok(())
}

fn expect_meta_str(proof: &Value, key: &str, expected: &str) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    let actual = meta
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("proof.meta.{key} missing"))?;
    if actual != expected {
        return Err(format!("proof.meta.{key} mismatch"));
    }
    Ok(())
}

fn expect_meta_u64(proof: &Value, key: &str, expected: u64) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    let actual = meta
        .get(key)
        .and_then(Value::as_u64)
        .ok_or_else(|| format!("proof.meta.{key} missing"))?;
    if actual != expected {
        return Err(format!("proof.meta.{key} mismatch"));
    }
    Ok(())
}

fn expect_meta_pre_hash(proof: &Value, present: bool, expected: [u8; 32]) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    let actual = meta
        .get("pre_app_hash")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof.meta.pre_app_hash missing".to_string())?;
    if !present {
        if !actual.trim().is_empty() {
            return Err("proof.meta.pre_app_hash mismatch".into());
        }
        return Ok(());
    }
    if normalize_hex64(actual) != hex_lower(&expected) {
        return Err("proof.meta.pre_app_hash mismatch".into());
    }
    Ok(())
}

fn expect_context_hash(
    context: &serde_json::Map<String, Value>,
    key: &str,
    expected: [u8; 32],
) -> Result<(), String> {
    let actual = context
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("context.{key} missing"))?;
    if normalize_hex64(actual) != hex_lower(&expected) {
        return Err(format!("context.{key} mismatch"));
    }
    Ok(())
}

fn parse_hex32_err(s: &str) -> Result<[u8; 32], String> {
    parse_hex32(s)
}

fn parse_dex_snapshot_json(app_state_json: &str) -> Result<DexSnapshotV1, String> {
    let v = strict_json::parse_value(app_state_json)
        .map_err(|e| format!("app_state_pre invalid JSON: {e}"))?;
    if !v.is_object() {
        return Err("app_state_pre must be a JSON object".into());
    }
    serde_json::from_value(v).map_err(|e| format!("app_state_pre schema mismatch: {e}"))
}

fn parse_chain_balances(v: Option<&Value>, name: &str) -> Vec<ChainBalanceV1> {
    let Some(val) = v else { return vec![] };
    let Some(obj) = val.as_object() else {
        die(&format!("{name} must be an object"));
    };
    let mut out = Vec::with_capacity(obj.len());
    for (pk, amt) in obj {
        if !pk.is_empty() {
            let n = amt
                .as_u64()
                .or_else(|| {
                    amt.as_i64()
                        .and_then(|i| if i >= 0 { Some(i as u64) } else { None })
                })
                .unwrap_or_else(|| die(&format!("{name}: invalid amount for pubkey")));
            out.push(ChainBalanceV1 {
                pubkey: pk.clone(),
                amount: n as u128,
            });
        }
    }
    out
}

fn parse_pre_nonces(v: Option<&Value>, name: &str) -> Result<Vec<NonceEntryV1>, String> {
    let Some(val) = v else { return Ok(vec![]) };
    let Some(obj) = val.as_object() else {
        return Err(format!("{name} must be an object"));
    };
    let mut out = Vec::with_capacity(obj.len());
    for (pk, nonce) in obj {
        if pk.is_empty() {
            return Err(format!("{name}: pubkey must be non-empty"));
        }
        let n = nonce
            .as_u64()
            .or_else(|| {
                nonce
                    .as_i64()
                    .and_then(|i| if i >= 0 { Some(i as u64) } else { None })
            })
            .ok_or_else(|| format!("{name}: invalid nonce for pubkey"))?;
        out.push(NonceEntryV1 {
            pubkey: pk.clone(),
            next_nonce: n,
        });
    }
    Ok(out)
}

fn parse_block_ingress_facts(v: Option<&Value>) -> Result<Vec<TxIngressFactV1>, String> {
    let txs = v
        .and_then(Value::as_array)
        .ok_or_else(|| "block.transactions must be a list".to_string())?;
    let mut out = Vec::with_capacity(txs.len());
    for tx in txs {
        let tx_obj = tx
            .as_object()
            .ok_or_else(|| "tx must be an object".to_string())?;
        let sender = tx_sender_identity_v1(tx_obj)?;
        let nonce = tx_obj
            .get("nonce")
            .and_then(Value::as_u64)
            .ok_or_else(|| "tx.nonce missing/invalid".to_string())?;
        out.push(TxIngressFactV1 {
            sender_pubkey: sender,
            nonce,
        });
    }
    Ok(out)
}

fn check_nonce_roots(
    journal: &StateProofJournalV1,
    pre_nonces: Vec<NonceEntryV1>,
    ingress: Option<&[TxIngressFactV1]>,
) -> Result<(), String> {
    let mut nonce_state = NonceStateV1::from_entries(pre_nonces).map_err(transition_error_str)?;
    if nonce_state.root() != journal.pre_nonce_root {
        return Err("pre_nonce_root mismatch".into());
    }
    if let Some(facts) = ingress {
        for fact in facts {
            let tx = TauTxV1 {
                sender_pubkey: fact.sender_pubkey.clone(),
                app_ops: TauTxAppOpsV1 {
                    has_faucet: false,
                    faucet_mint: Vec::new(),
                    has_intents: false,
                    intents: Vec::new(),
                },
            };
            nonce_state
                .apply_ingress(&tx, fact)
                .map_err(transition_error_str)?;
        }
        if nonce_state.root() != journal.post_nonce_root {
            return Err("post_nonce_root mismatch".into());
        }
    }
    Ok(())
}

fn transition_error_str(err: tau_state_proof_risc0_shared::TransitionError) -> String {
    match err {
        tau_state_proof_risc0_shared::TransitionError::InvalidInput(msg) => msg.to_string(),
        tau_state_proof_risc0_shared::TransitionError::Unsupported(msg) => msg.to_string(),
        tau_state_proof_risc0_shared::TransitionError::Arithmetic(msg) => msg.to_string(),
    }
}

fn parse_block_txs(v: Option<&Value>) -> Result<Vec<TauTxV1>, String> {
    parse_txs(v, "block.transactions")
}

fn parse_txs(v: Option<&Value>, name: &str) -> Result<Vec<TauTxV1>, String> {
    let txs = v
        .and_then(Value::as_array)
        .ok_or_else(|| format!("{name} must be a list"))?;
    let mut out = Vec::with_capacity(txs.len());
    for tx in txs {
        let tx_obj = tx
            .as_object()
            .ok_or_else(|| "tx must be an object".to_string())?;
        let sender = tx_sender_identity_v1(tx_obj)?;

        let ops = tx_obj
            .get("operations")
            .ok_or_else(|| "tx.operations missing".to_string())?;
        let ops_obj = ops
            .as_object()
            .ok_or_else(|| "tx.operations must be an object".to_string())?;

        let (has_faucet, faucet_mint) = if let Some(v4) = ops_obj.get("4") {
            (true, parse_faucet(v4)?)
        } else {
            (false, vec![])
        };
        let (has_intents, intents) = if let Some(v2) = ops_obj.get("2") {
            (true, parse_intents(v2, &sender)?)
        } else {
            (false, vec![])
        };

        out.push(TauTxV1 {
            sender_pubkey: sender,
            app_ops: TauTxAppOpsV1 {
                has_faucet,
                faucet_mint,
                has_intents,
                intents,
            },
        });
    }
    Ok(out)
}

fn tx_sender_identity_v1(tx_obj: &serde_json::Map<String, Value>) -> Result<String, String> {
    let tx_sender = tx_obj.get("tx_sender_pubkey").and_then(Value::as_str);
    let legacy_sender = tx_obj.get("sender_pubkey").and_then(Value::as_str);
    if let Some(sender) = tx_sender {
        if sender.is_empty() {
            return Err("tx.tx_sender_pubkey must be non-empty".to_string());
        }
        if let Some(legacy) = legacy_sender {
            if legacy.is_empty() {
                return Err("tx.sender_pubkey must be non-empty when present".to_string());
            }
            if legacy != sender {
                return Err("tx.sender_pubkey must match tx_sender_pubkey".to_string());
            }
        }
        return Ok(sender.to_string());
    }
    if let Some(sender) = legacy_sender {
        if sender.is_empty() {
            return Err("tx.sender_pubkey must be non-empty".to_string());
        }
        return Ok(sender.to_string());
    }
    Err("tx.sender_pubkey missing".to_string())
}

fn parse_faucet(v4: &Value) -> Result<Vec<tau_state_proof_risc0_shared::FaucetMintV1>, String> {
    let o = v4
        .as_object()
        .ok_or_else(|| "operations['4'] must be an object".to_string())?;
    let mint = o
        .get("mint")
        .and_then(Value::as_array)
        .ok_or_else(|| "operations['4'].mint must be a list".to_string())?;
    let mut out = Vec::with_capacity(mint.len());
    for entry in mint {
        if let Some(arr) = entry.as_array() {
            if arr.len() != 3 {
                return Err("faucet mint entry must have length 3".into());
            }
            let pk = arr[0]
                .as_str()
                .ok_or_else(|| "mint pubkey must be a string".to_string())?;
            let asset = arr[1]
                .as_str()
                .ok_or_else(|| "mint asset must be a string".to_string())?;
            let amount = arr[2]
                .as_u64()
                .ok_or_else(|| "mint amount must be a non-negative int".to_string())?;
            out.push(tau_state_proof_risc0_shared::FaucetMintV1 {
                pubkey: pk.to_string(),
                asset: asset.to_string(),
                amount: amount as u128,
            });
            continue;
        }
        let obj = entry
            .as_object()
            .ok_or_else(|| "mint entry must be list or object".to_string())?;
        let pk = obj
            .get("pubkey")
            .and_then(Value::as_str)
            .ok_or_else(|| "mint pubkey missing".to_string())?;
        let asset = obj
            .get("asset")
            .and_then(Value::as_str)
            .ok_or_else(|| "mint asset missing".to_string())?;
        let amount = obj
            .get("amount")
            .and_then(Value::as_u64)
            .ok_or_else(|| "mint amount missing".to_string())?;
        out.push(tau_state_proof_risc0_shared::FaucetMintV1 {
            pubkey: pk.to_string(),
            asset: asset.to_string(),
            amount: amount as u128,
        });
    }
    Ok(out)
}

fn parse_intents(
    v2: &Value,
    tx_sender_pubkey: &str,
) -> Result<Vec<tau_state_proof_risc0_shared::SignedIntentV1>, String> {
    let arr = v2
        .as_array()
        .ok_or_else(|| "operations['2'] must be a list".to_string())?;
    let mut out = Vec::with_capacity(arr.len());
    for entry in arr {
        if let Some(pair) = entry.as_array() {
            if pair.len() != 2 {
                return Err("signed intent entry must have length 2".into());
            }
            let intent_obj = pair[0]
                .as_object()
                .ok_or_else(|| "intent must be an object".to_string())?;
            let sig = pair[1].as_str().map(|s| s.to_string());
            let intent = parse_intent_obj(intent_obj)?;
            verify_intent_sender_matches_tx(&intent, tx_sender_pubkey)?;
            out.push(tau_state_proof_risc0_shared::SignedIntentV1 {
                intent,
                signature: sig,
            });
            continue;
        }
        let obj = entry
            .as_object()
            .ok_or_else(|| "intent entry must be [intent, sig] or object".to_string())?;
        let intent = parse_intent_obj(obj)?;
        verify_intent_sender_matches_tx(&intent, tx_sender_pubkey)?;
        out.push(tau_state_proof_risc0_shared::SignedIntentV1 {
            intent,
            signature: None,
        });
    }
    Ok(out)
}

fn verify_intent_sender_matches_tx(
    intent: &tau_state_proof_risc0_shared::DexIntentV1,
    tx_sender_pubkey: &str,
) -> Result<(), String> {
    let intent_sender = match intent {
        tau_state_proof_risc0_shared::DexIntentV1::CreatePool(intent) => &intent.sender_pubkey,
        tau_state_proof_risc0_shared::DexIntentV1::SwapExactIn(intent) => &intent.sender_pubkey,
        tau_state_proof_risc0_shared::DexIntentV1::AddLiquidity(intent) => &intent.sender_pubkey,
        tau_state_proof_risc0_shared::DexIntentV1::RemoveLiquidity(intent) => &intent.sender_pubkey,
        tau_state_proof_risc0_shared::DexIntentV1::SwapExactOut(intent) => &intent.sender_pubkey,
        tau_state_proof_risc0_shared::DexIntentV1::Route(intent) => &intent.sender_pubkey,
    };
    if intent_sender != tx_sender_pubkey {
        return Err("intent.sender_pubkey must match tx.sender_pubkey".to_string());
    }
    Ok(())
}

fn parse_intent_obj(
    obj: &serde_json::Map<String, Value>,
) -> Result<tau_state_proof_risc0_shared::DexIntentV1, String> {
    let module = obj
        .get("module")
        .and_then(Value::as_str)
        .ok_or_else(|| "intent.module missing".to_string())?;
    let version = obj
        .get("version")
        .and_then(Value::as_str)
        .ok_or_else(|| "intent.version missing".to_string())?;
    let kind = obj
        .get("kind")
        .and_then(Value::as_str)
        .ok_or_else(|| "intent.kind missing".to_string())?;
    let intent_id = obj
        .get("intent_id")
        .and_then(Value::as_str)
        .ok_or_else(|| "intent.intent_id missing".to_string())?;
    let sender = obj
        .get("sender_pubkey")
        .and_then(Value::as_str)
        .ok_or_else(|| "intent.sender_pubkey missing".to_string())?;
    let deadline = obj
        .get("deadline")
        .and_then(Value::as_u64)
        .ok_or_else(|| "intent.deadline missing".to_string())?;
    let salt = obj
        .get("salt")
        .and_then(Value::as_str)
        .map(|s| s.to_string());

    match kind {
        "CREATE_POOL" => {
            let asset0 = obj
                .get("asset0")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.asset0 missing".to_string())?;
            let asset1 = obj
                .get("asset1")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.asset1 missing".to_string())?;
            let fee_bps_raw = obj
                .get("fee_bps")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.fee_bps missing or invalid".to_string())?;
            let fee_bps = u32::try_from(fee_bps_raw)
                .map_err(|_| "intent.fee_bps must fit in a u32".to_string())?;
            let amount0 = obj
                .get("amount0")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount0 missing".to_string())?;
            let amount1 = obj
                .get("amount1")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount1 missing".to_string())?;
            Ok(tau_state_proof_risc0_shared::DexIntentV1::CreatePool(
                tau_state_proof_risc0_shared::CreatePoolIntentV1 {
                    module: module.to_string(),
                    version: version.to_string(),
                    intent_id: intent_id.to_string(),
                    sender_pubkey: sender.to_string(),
                    deadline,
                    asset0: asset0.to_string(),
                    asset1: asset1.to_string(),
                    fee_bps,
                    amount0: amount0 as u128,
                    amount1: amount1 as u128,
                    salt,
                },
            ))
        }
        "SWAP_EXACT_IN" => {
            let pool_id = obj
                .get("pool_id")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.pool_id missing".to_string())?;
            let asset_in = obj
                .get("asset_in")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.asset_in missing".to_string())?;
            let asset_out = obj
                .get("asset_out")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.asset_out missing".to_string())?;
            let amount_in = obj
                .get("amount_in")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount_in missing".to_string())?;
            let min_amount_out = obj
                .get("min_amount_out")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.min_amount_out missing".to_string())?;
            let recipient = obj
                .get("recipient")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.recipient missing".to_string())?;
            Ok(tau_state_proof_risc0_shared::DexIntentV1::SwapExactIn(
                tau_state_proof_risc0_shared::SwapExactInIntentV1 {
                    module: module.to_string(),
                    version: version.to_string(),
                    intent_id: intent_id.to_string(),
                    sender_pubkey: sender.to_string(),
                    deadline,
                    pool_id: pool_id.to_string(),
                    asset_in: asset_in.to_string(),
                    asset_out: asset_out.to_string(),
                    amount_in: amount_in as u128,
                    min_amount_out: min_amount_out as u128,
                    recipient: recipient.to_string(),
                    salt,
                },
            ))
        }
        "ADD_LIQUIDITY" => {
            let pool_id = obj
                .get("pool_id")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.pool_id missing".to_string())?;
            let amount0_desired = obj
                .get("amount0_desired")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount0_desired missing".to_string())?;
            let amount1_desired = obj
                .get("amount1_desired")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount1_desired missing".to_string())?;
            let amount0_min = obj
                .get("amount0_min")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount0_min missing".to_string())?;
            let amount1_min = obj
                .get("amount1_min")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount1_min missing".to_string())?;
            let recipient = obj
                .get("recipient")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.recipient missing".to_string())?;
            Ok(tau_state_proof_risc0_shared::DexIntentV1::AddLiquidity(
                tau_state_proof_risc0_shared::AddLiquidityIntentV1 {
                    module: module.to_string(),
                    version: version.to_string(),
                    intent_id: intent_id.to_string(),
                    sender_pubkey: sender.to_string(),
                    deadline,
                    pool_id: pool_id.to_string(),
                    amount0_desired: amount0_desired as u128,
                    amount1_desired: amount1_desired as u128,
                    amount0_min: amount0_min as u128,
                    amount1_min: amount1_min as u128,
                    recipient: recipient.to_string(),
                    salt,
                },
            ))
        }
        "REMOVE_LIQUIDITY" => {
            let pool_id = obj
                .get("pool_id")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.pool_id missing".to_string())?;
            let lp_amount = obj
                .get("lp_amount")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.lp_amount missing".to_string())?;
            let amount0_min = obj
                .get("amount0_min")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount0_min missing".to_string())?;
            let amount1_min = obj
                .get("amount1_min")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.amount1_min missing".to_string())?;
            let recipient = obj
                .get("recipient")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.recipient missing".to_string())?;
            Ok(tau_state_proof_risc0_shared::DexIntentV1::RemoveLiquidity(
                tau_state_proof_risc0_shared::RemoveLiquidityIntentV1 {
                    module: module.to_string(),
                    version: version.to_string(),
                    intent_id: intent_id.to_string(),
                    sender_pubkey: sender.to_string(),
                    deadline,
                    pool_id: pool_id.to_string(),
                    lp_amount: lp_amount as u128,
                    amount0_min: amount0_min as u128,
                    amount1_min: amount1_min as u128,
                    recipient: recipient.to_string(),
                    salt,
                },
            ))
        }
        "SWAP_EXACT_OUT" => {
            let pool_id = obj
                .get("pool_id")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.pool_id missing".to_string())?;
            let asset_in = obj
                .get("asset_in")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.asset_in missing".to_string())?;
            let asset_out = obj
                .get("asset_out")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.asset_out missing".to_string())?;
            let amount_out = obj_u128(obj, "amount_out", None)?;
            let max_amount_in = obj_u128(obj, "max_amount_in", None)?;
            let recipient = obj
                .get("recipient")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.recipient missing".to_string())?;
            Ok(tau_state_proof_risc0_shared::DexIntentV1::SwapExactOut(
                tau_state_proof_risc0_shared::SwapExactOutIntentV1 {
                    module: module.to_string(),
                    version: version.to_string(),
                    intent_id: intent_id.to_string(),
                    sender_pubkey: sender.to_string(),
                    deadline,
                    pool_id: pool_id.to_string(),
                    asset_in: asset_in.to_string(),
                    asset_out: asset_out.to_string(),
                    amount_out,
                    max_amount_in,
                    recipient: recipient.to_string(),
                    salt,
                },
            ))
        }
        "ROUTE_EXACT_IN" | "ROUTE_EXACT_OUT" => {
            let quote_receipt_hash = obj
                .get("quote_receipt_hash")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.quote_receipt_hash missing".to_string())?;
            let asset_in = obj
                .get("asset_in")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.asset_in missing".to_string())?;
            let asset_out = obj
                .get("asset_out")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.asset_out missing".to_string())?;
            let leg_indices = obj
                .get("leg_indices")
                .and_then(Value::as_array)
                .ok_or_else(|| "intent.leg_indices missing".to_string())?
                .iter()
                .map(|v| {
                    v.as_u64()
                        .filter(|n| *n <= u32::MAX as u64)
                        .map(|n| n as u32)
                        .ok_or_else(|| "leg_indices entry must be u32".to_string())
                })
                .collect::<Result<Vec<u32>, String>>()?;
            let legs = obj
                .get("legs")
                .and_then(Value::as_array)
                .ok_or_else(|| "intent.legs missing".to_string())?
                .iter()
                .map(|leg_obj| {
                    let hops = leg_obj
                        .get("hops")
                        .and_then(Value::as_array)
                        .ok_or_else(|| "leg.hops missing".to_string())?
                        .iter()
                        .map(|hop_obj| {
                            let pool_id = hop_obj
                                .get("pool_id")
                                .and_then(Value::as_str)
                                .ok_or_else(|| "hop.pool_id missing".to_string())?;
                            Ok::<_, String>(tau_state_proof_risc0_shared::RouteLegHopV1 {
                                pool_id: pool_id.to_string(),
                            })
                        })
                        .collect::<Result<Vec<_>, String>>()?;
                    Ok::<_, String>(tau_state_proof_risc0_shared::RouteLegV1 { hops })
                })
                .collect::<Result<Vec<_>, String>>()?;
            let totals = parse_route_totals(obj, kind)?;
            let recipient = obj
                .get("recipient")
                .and_then(Value::as_str)
                .ok_or_else(|| "intent.recipient missing".to_string())?;
            Ok(tau_state_proof_risc0_shared::DexIntentV1::Route(
                tau_state_proof_risc0_shared::RouteIntentV1 {
                    module: module.to_string(),
                    version: version.to_string(),
                    intent_id: intent_id.to_string(),
                    sender_pubkey: sender.to_string(),
                    deadline,
                    quote_receipt_hash: quote_receipt_hash.to_string(),
                    asset_in: asset_in.to_string(),
                    asset_out: asset_out.to_string(),
                    leg_indices,
                    legs,
                    kind: kind.to_string(),
                    total_amount_in: totals.total_amount_in,
                    total_min_amount_out: totals.total_min_amount_out,
                    total_amount_out: totals.total_amount_out,
                    total_max_amount_in: totals.total_max_amount_in,
                    recipient: recipient.to_string(),
                    salt,
                },
            ))
        }
        _ => Err("unsupported intent.kind".into()),
    }
}

fn parse_route_totals(
    obj: &serde_json::Map<String, Value>,
    kind: &str,
) -> Result<RouteTotals, String> {
    let total_amount_in = obj_u128(
        obj,
        "total_amount_in",
        if kind == "ROUTE_EXACT_IN" {
            None
        } else {
            Some(0)
        },
    )?;
    let total_min_amount_out = obj_u128(obj, "total_min_amount_out", Some(0))?;
    let total_amount_out = obj_u128(
        obj,
        "total_amount_out",
        if kind == "ROUTE_EXACT_OUT" {
            None
        } else {
            Some(0)
        },
    )?;
    let total_max_amount_in = obj_u128(
        obj,
        "total_max_amount_in",
        if kind == "ROUTE_EXACT_OUT" {
            None
        } else {
            Some(0)
        },
    )?;
    match kind {
        "ROUTE_EXACT_IN" => {
            if total_amount_in == 0 {
                return Err("total_amount_in must be positive".to_string());
            }
            if total_amount_out != 0 {
                return Err(
                    "total_amount_out must be absent or zero for ROUTE_EXACT_IN".to_string()
                );
            }
            if total_max_amount_in != 0 {
                return Err(
                    "total_max_amount_in must be absent or zero for ROUTE_EXACT_IN".to_string(),
                );
            }
        }
        "ROUTE_EXACT_OUT" => {
            if total_amount_out == 0 {
                return Err("total_amount_out must be positive".to_string());
            }
            if total_max_amount_in == 0 {
                return Err("total_max_amount_in must be positive".to_string());
            }
            if total_amount_in != 0 {
                return Err(
                    "total_amount_in must be absent or zero for ROUTE_EXACT_OUT".to_string()
                );
            }
            if total_min_amount_out != 0 {
                return Err(
                    "total_min_amount_out must be absent or zero for ROUTE_EXACT_OUT".to_string(),
                );
            }
        }
        _ => return Err("unsupported route kind".to_string()),
    }
    Ok(RouteTotals {
        total_amount_in,
        total_min_amount_out,
        total_amount_out,
        total_max_amount_in,
    })
}

fn require_str(v: Option<&Value>, name: &str) -> String {
    v.and_then(Value::as_str)
        .map(|s| s.to_string())
        .unwrap_or_else(|| die(&format!("{name} must be a string")))
}

fn normalize_hex64(s: &str) -> String {
    let mut h = s.trim().to_ascii_lowercase();
    if h.starts_with("0x") {
        h = h[2..].to_string();
    }
    h
}

fn parse_hex32(s: &str) -> Result<[u8; 32], String> {
    let h = normalize_hex64(s);
    if h.len() != 64 {
        return Err("hex must be 64 chars".into());
    }
    let bytes = hex::decode(&h).map_err(|e| format!("invalid hex: {e}"))?;
    let arr: [u8; 32] = bytes
        .try_into()
        .map_err(|_| "hex must decode to 32 bytes".to_string())?;
    Ok(arr)
}

fn hex_lower(bytes: &[u8; 32]) -> String {
    hex::encode(bytes)
}

fn hex_prefixed(bytes: &[u8; 32]) -> String {
    format!("0x{}", hex_lower(bytes))
}

fn hex_u32_words(words: [u32; 8]) -> String {
    Digest::from(words).to_string()
}

fn write_json_stdout(v: &Value) {
    let mut stdout = std::io::stdout();
    let s = serde_json::to_string(v).unwrap_or_else(|_| "{\"ok\":false}".to_string());
    let _ = stdout.write_all(s.as_bytes());
}

fn die(msg: &str) -> ! {
    eprintln!("{msg}");
    std::process::exit(2);
}

#[cfg(test)]
mod tests {
    use super::*;
    use risc0_zkvm::{FakeReceipt, ReceiptClaim};
    use tau_state_proof_risc0_shared::{
        recursive_asset_delta_root_v1, recursive_authority_set_root_v1,
        recursive_child_journal_hash_v1, recursive_child_verification_claim_hash_v1,
        recursive_child_verifier_id_v1, recursive_cross_shard_message_id_v1,
        recursive_cross_shard_messages_root_v1, recursive_effect_summary_hash_v1,
        recursive_lane_state_vector_root_v1, recursive_receipt_ids_root_v1,
        recursive_verifier_set_root_v1, RecursiveAssetDeltaRowV1, RecursiveChildDescriptorV1,
        RecursiveChildEffectV1, RecursiveCrossShardMessageV1, RecursiveEffectSummaryV1,
        RECURSIVE_EFFECT_SUMMARY_VERSION_V1, RECURSIVE_EPOCH_PROFILE_V1,
        RECURSIVE_SPOT_LEAF_PROFILE_V1, RECURSIVE_STATEMENT_VERSION_V1,
        RECURSIVE_STRICT_CROSS_SHARD_MODE_V1,
    };

    fn h(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn hx(byte: u8) -> String {
        hex::encode(h(byte))
    }

    fn recursive_image(byte: u32) -> [u32; 8] {
        [byte; 8]
    }

    fn nonzero_test_method_id(method_id: [u32; 8], fallback: u32) -> [u32; 8] {
        if method_id.iter().all(|word| *word == 0) {
            recursive_image(fallback)
        } else {
            method_id
        }
    }

    fn recursive_asset_row(
        asset_id: &str,
        debit_atoms: u128,
        credit_atoms: u128,
    ) -> RecursiveAssetDeltaRowV1 {
        RecursiveAssetDeltaRowV1 {
            asset_id: asset_id.to_string(),
            debit_atoms,
            credit_atoms,
            authorized_mint_atoms: 0,
            authorized_burn_atoms: 0,
            authority_root: [0u8; 32],
        }
    }

    fn recursive_child(
        lane_id: &str,
        image_byte: u8,
        journal_byte: u8,
        asset_delta_rows: Vec<RecursiveAssetDeltaRowV1>,
        accepted_receipt_ids: Vec<[u8; 32]>,
    ) -> RecursiveChildEffectV1 {
        let outbox_messages: Vec<RecursiveCrossShardMessageV1> = Vec::new();
        let inbox_messages: Vec<RecursiveCrossShardMessageV1> = Vec::new();
        let rejected_receipt_ids: Vec<[u8; 32]> = Vec::new();
        let asset_delta_root = recursive_asset_delta_root_v1(&asset_delta_rows).unwrap();
        let accepted_receipts_root = recursive_receipt_ids_root_v1(&accepted_receipt_ids).unwrap();
        let rejected_receipts_root = recursive_receipt_ids_root_v1(&rejected_receipt_ids).unwrap();
        let summary = RecursiveEffectSummaryV1 {
            summary_version: RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
            lane_id: lane_id.to_string(),
            lane_kind: "spot".to_string(),
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            proof_profile: "recursive_block_v1".to_string(),
            risc0_image_id: recursive_image(image_byte as u32),
            statement_hash: h(image_byte + 30),
            pre_state_root: h(image_byte + 40),
            post_state_root: h(image_byte + 50),
            tx_root: h(image_byte + 60),
            evidence_root: h(image_byte + 70),
            receipt_root: h(image_byte + 80),
            accepted_receipts_root,
            rejected_receipts_root,
            asset_delta_root,
            cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&outbox_messages)
                .unwrap(),
            cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&inbox_messages)
                .unwrap(),
            write_set_root: h(image_byte + 90),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
        };
        let child_journal_bytes = vec![journal_byte, image_byte];
        let child_journal_hash = recursive_child_journal_hash_v1(&child_journal_bytes).unwrap();
        let child_verification_claim_hash = recursive_child_verification_claim_hash_v1(
            &summary.risc0_image_id,
            &child_journal_bytes,
        )
        .unwrap();
        let child_effect_summary_hash = recursive_effect_summary_hash_v1(&summary);
        let child_verifier_id =
            recursive_child_verifier_id_v1(&summary.risc0_image_id, &summary.proof_profile)
                .unwrap();
        RecursiveChildEffectV1 {
            descriptor: RecursiveChildDescriptorV1 {
                child_verification_claim_hash,
                child_journal_hash,
                child_effect_summary_hash,
                child_statement_hash: summary.statement_hash,
                child_image_id: summary.risc0_image_id,
                child_verifier_id,
                child_profile: summary.proof_profile.clone(),
            },
            child_journal_bytes,
            summary,
            asset_delta_rows,
            outbox_messages,
            inbox_messages,
            accepted_receipt_ids,
            rejected_receipt_ids,
        }
    }

    fn recursive_message(
        source_shard_id: &str,
        destination_shard_id: &str,
        scope_seed: u8,
    ) -> RecursiveCrossShardMessageV1 {
        let mut message = RecursiveCrossShardMessageV1 {
            message_id: [0u8; 32],
            epoch_id: 7,
            source_shard_id: source_shard_id.to_string(),
            destination_shard_id: destination_shard_id.to_string(),
            asset_id: "ASSET0".to_string(),
            amount_atoms: 1,
            sender_scope_hash: h(scope_seed),
            recipient_scope_hash: h(scope_seed + 1),
            source_receipt_hash: h(scope_seed + 2),
            deadline_epoch: 7,
        };
        message.message_id = recursive_cross_shard_message_id_v1(&message).unwrap();
        message
    }

    fn refresh_recursive_child_disclosure_roots(child: &mut RecursiveChildEffectV1) {
        child.summary.accepted_receipts_root =
            recursive_receipt_ids_root_v1(&child.accepted_receipt_ids).unwrap();
        child.summary.rejected_receipts_root =
            recursive_receipt_ids_root_v1(&child.rejected_receipt_ids).unwrap();
        child.summary.cross_shard_outbox_root =
            recursive_cross_shard_messages_root_v1(&child.outbox_messages).unwrap();
        child.summary.cross_shard_inbox_root =
            recursive_cross_shard_messages_root_v1(&child.inbox_messages).unwrap();
        child.descriptor.child_effect_summary_hash =
            recursive_effect_summary_hash_v1(&child.summary);
    }

    fn recursive_input() -> RecursiveCompositionInputV1 {
        let authority_roots = vec![h(6)];
        let left = recursive_child(
            "lane-a",
            21,
            31,
            vec![
                recursive_asset_row("ASSET0", 10, 0),
                recursive_asset_row("ASSET1", 0, 5),
            ],
            vec![h(81)],
        );
        let right = recursive_child(
            "lane-b",
            22,
            32,
            vec![
                recursive_asset_row("ASSET0", 0, 10),
                recursive_asset_row("ASSET1", 5, 0),
            ],
            vec![h(82)],
        );
        let mut verifier_ids = vec![
            left.descriptor.child_verifier_id,
            right.descriptor.child_verifier_id,
        ];
        verifier_ids.sort();
        let pre_state_root = recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.pre_state_vector_root.v1",
            &[
                (left.summary.lane_id.clone(), left.summary.pre_state_root),
                (right.summary.lane_id.clone(), right.summary.pre_state_root),
            ],
        )
        .unwrap();
        let post_state_root = recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.post_state_vector_root.v1",
            &[
                (left.summary.lane_id.clone(), left.summary.post_state_root),
                (right.summary.lane_id.clone(), right.summary.post_state_root),
            ],
        )
        .unwrap();
        RecursiveCompositionInputV1 {
            statement: tau_state_proof_risc0_shared::RecursiveCompositionStatementV1 {
                domain_separator: RECURSIVE_DOMAIN_SEPARATOR_V1.to_string(),
                schema_version: RECURSIVE_STATEMENT_VERSION_V1,
                chain_id: "tau-test".to_string(),
                epoch_id: 7,
                proof_profile: RECURSIVE_EPOCH_PROFILE_V1.to_string(),
                verifier_set_root: recursive_verifier_set_root_v1(&verifier_ids).unwrap(),
                allowed_authority_roots_root: recursive_authority_set_root_v1(&authority_roots)
                    .unwrap(),
                public_policy_hash: h(10),
                feature_suite_hash: h(11),
                dependency_lock_hash: h(12),
                toolchain_lock_hash: h(13),
                expected_pre_state_root: pre_state_root,
                expected_post_state_root: post_state_root,
                conflict_schedule_hash: h(14),
                carry_queue_pre_root: h(15),
                carry_queue_post_root: h(15),
                data_availability_root: h(16),
                expected_child_count: 2,
                max_children: 8,
                max_child_journal_bytes: 64,
                max_total_child_journal_bytes: 128,
                max_asset_delta_rows: 16,
                max_cross_shard_messages: 16,
                max_receipt_ids: 16,
                cross_shard_mode: RECURSIVE_STRICT_CROSS_SHARD_MODE_V1.to_string(),
            },
            allowed_verifier_ids: verifier_ids,
            allowed_authority_roots: authority_roots,
            children: vec![left, right],
        }
    }

    fn recursive_summary_leaf_summary() -> RecursiveEffectSummaryV1 {
        let mut summary = recursive_input().children[0].summary.clone();
        summary.proof_profile = RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1.to_string();
        summary.risc0_image_id = nonzero_test_method_id(TAU_STATE_PROOF_SUMMARY_LEAF_ID, 101);
        summary
    }

    fn recursive_spot_leaf_summary() -> RecursiveEffectSummaryV1 {
        let mut summary = recursive_input().children[0].summary.clone();
        summary.proof_profile = RECURSIVE_SPOT_LEAF_PROFILE_V1.to_string();
        summary.risc0_image_id = nonzero_test_method_id(TAU_STATE_PROOF_SPOT_LEAF_ID, 102);
        summary
    }

    fn recursive_perps_np_leaf_summary() -> RecursiveEffectSummaryV1 {
        let mut summary = recursive_input().children[0].summary.clone();
        summary.lane_kind = "perps_np".to_string();
        summary.proof_profile = RECURSIVE_PERPS_NP_LEAF_PROFILE_V1.to_string();
        summary.risc0_image_id = nonzero_test_method_id(TAU_STATE_PROOF_PERPS_NP_LEAF_ID, 103);
        summary
    }

    fn recursive_zusd_leaf_summary() -> RecursiveEffectSummaryV1 {
        let mut summary = recursive_input().children[0].summary.clone();
        summary.lane_kind = "zusd".to_string();
        summary.proof_profile = RECURSIVE_ZUSD_LEAF_PROFILE_V1.to_string();
        summary.risc0_image_id = nonzero_test_method_id(TAU_STATE_PROOF_ZUSD_LEAF_ID, 104);
        summary
    }

    fn strict_req() -> Value {
        json!({
            "schema": "tau_state_proof_verify",
            "schema_version": 1,
            "chain_id": "devnet",
            "state_hash": hx(1),
            "tau_state": {"app_hash": hx(2)},
            "context": {
                "app_hash_pre": "",
                "operation_hash": hx(3),
                "state_delta_hash": hx(4),
                "oracle_binding_hash": hx(5),
                "participant_set_hash": hx(6)
            }
        })
    }

    fn strict_proof_meta() -> Value {
        json!({
            "proof_type": PROOF_TYPE_PERPS_NP,
            "proof": "unused",
            "meta": {
                "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_GUEST_ID),
                "pre_app_hash": "",
                "post_app_hash": hx(2),
                "operation_hash": hx(3),
                "state_delta_hash": hx(4),
                "oracle_binding_hash": hx(5),
                "participant_set_hash": hx(6)
            }
        })
    }

    fn strict_binding_expectations(journal_chain_id: &str) -> SurfaceBindingExpectations<'_> {
        SurfaceBindingExpectations {
            journal_chain_id,
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            post_app_hash: h(2),
            operation_hash: h(3),
            state_delta_hash: h(4),
            oracle_binding_hash: h(5),
            participant_set_hash: h(6),
        }
    }

    fn recursive_expectations(journal: &RecursiveEpochJournalV1) -> Value {
        let receipt_profile = recursive_receipt_profile();
        json!({
            "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_AGGREGATE_ID),
            "receipt_codec": RECEIPT_CODEC_V1,
            "receipt_kind": ProofReceiptKind::Succinct.as_str(),
            "receipt_hashfn": receipt_profile.hashfn,
            "receipt_verifier_parameters": receipt_profile.verifier_parameters,
            "receipt_control_id": receipt_profile.control_id,
            "journal_version": journal.journal_version,
            "proof_type": journal.proof_type.as_str(),
            "domain_separator": journal.domain_separator.as_str(),
            "chain_id": journal.chain_id.as_str(),
            "epoch_id": journal.epoch_id,
            "proof_profile": journal.proof_profile.as_str(),
            "statement_hash": hex_lower(&journal.statement_hash),
            "verifier_set_root": hex_lower(&journal.verifier_set_root),
            "allowed_authority_roots_root": hex_lower(&journal.allowed_authority_roots_root),
            "child_verification_claims_root": hex_lower(&journal.child_verification_claims_root),
            "child_journals_root": hex_lower(&journal.child_journals_root),
            "child_effect_summaries_root": hex_lower(&journal.child_effect_summaries_root),
            "child_count": journal.child_count,
            "pre_state_root": hex_lower(&journal.pre_state_root),
            "post_state_root": hex_lower(&journal.post_state_root),
            "tx_root": hex_lower(&journal.tx_root),
            "evidence_root": hex_lower(&journal.evidence_root),
            "receipt_root": hex_lower(&journal.receipt_root),
            "accepted_receipts_root": hex_lower(&journal.accepted_receipts_root),
            "rejected_receipts_root": hex_lower(&journal.rejected_receipts_root),
            "aggregate_asset_delta_root": hex_lower(&journal.aggregate_asset_delta_root),
            "cross_shard_outbox_root": hex_lower(&journal.cross_shard_outbox_root),
            "cross_shard_inbox_root": hex_lower(&journal.cross_shard_inbox_root),
            "cross_shard_message_ids_root": hex_lower(&journal.cross_shard_message_ids_root),
            "carry_queue_pre_root": hex_lower(&journal.carry_queue_pre_root),
            "carry_queue_post_root": hex_lower(&journal.carry_queue_post_root),
            "conflict_schedule_hash": hex_lower(&journal.conflict_schedule_hash),
            "data_availability_root": hex_lower(&journal.data_availability_root),
            "public_policy_hash": hex_lower(&journal.public_policy_hash),
            "feature_suite_hash": hex_lower(&journal.feature_suite_hash),
            "dependency_lock_hash": hex_lower(&journal.dependency_lock_hash),
            "toolchain_lock_hash": hex_lower(&journal.toolchain_lock_hash),
        })
    }

    fn recursive_receipt_profile() -> ReceiptSecurityProfile {
        ReceiptSecurityProfile {
            kind: ProofReceiptKind::Succinct,
            verifier_parameters: hx(201),
            hashfn: Some("poseidon2".to_string()),
            control_id: Some(hx(202)),
        }
    }

    fn recursive_verification_proof(journal: &RecursiveEpochJournalV1) -> Value {
        let profile = recursive_receipt_profile();
        let mut meta = recursive_meta(journal, ProofReceiptKind::Succinct);
        let object = meta.as_object_mut().unwrap();
        object.insert(
            "receipt_codec".to_string(),
            Value::String(RECEIPT_CODEC_V1.to_string()),
        );
        object.insert(
            "receipt_verifier_parameters".to_string(),
            Value::String(profile.verifier_parameters),
        );
        object.insert(
            "receipt_hashfn".to_string(),
            Value::String(profile.hashfn.unwrap()),
        );
        object.insert(
            "receipt_control_id".to_string(),
            Value::String(profile.control_id.unwrap()),
        );
        json!({
            "schema": "tau_state_proof",
            "schema_version": 1,
            "state_hash": hex_lower(&journal.post_state_root),
            "proof_type": PROOF_TYPE_RECURSIVE,
            "proof": "injected-by-test-authenticator",
            "meta": meta,
        })
    }

    fn recursive_verification_request(
        input: &RecursiveCompositionInputV1,
        journal: &RecursiveEpochJournalV1,
        proof: &Value,
    ) -> Value {
        json!({
            "schema": "tau_state_proof_verify",
            "schema_version": 1,
            "state_hash": hex_lower(&journal.post_state_root),
            "proof": proof,
            "recursive_input": input,
            "recursive_expectations": recursive_expectations(journal),
        })
    }

    fn assert_recursive_wire_rejects_before_authentication(
        req: &Value,
        proof: &Value,
        expected_state_hash: [u8; 32],
        expected_error: &str,
    ) {
        use std::cell::Cell;

        let authentication_calls = Cell::new(0usize);
        let result = try_verify_recursive_with_test_authenticator(
            req,
            proof,
            expected_state_hash,
            |_| -> Result<recursive_receipt_authentication::AuthenticatedReceipt, String> {
                authentication_calls.set(authentication_calls.get() + 1);
                Err("test authenticator must not run".to_string())
            },
        );
        let error = match result {
            Ok(_) => panic!("malformed recursive wire unexpectedly authenticated"),
            Err(error) => error,
        };
        assert_eq!(error, expected_error);
        assert_eq!(authentication_calls.get(), 0);
    }

    #[test]
    fn recursive_meta_binds_verification_claim_and_journal_roots() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let meta = recursive_meta(&journal, ProofReceiptKind::Succinct);
        assert_eq!(
            meta["risc0_image_id"],
            Value::String(hex_u32_words(TAU_STATE_PROOF_AGGREGATE_ID))
        );
        assert_eq!(meta["receipt_kind"], "succinct");
        assert_eq!(
            meta["proof_profile"],
            Value::String(RECURSIVE_EPOCH_PROFILE_V1.to_string())
        );
        assert_eq!(
            meta["child_verification_claims_root"],
            Value::String(hex_lower(&journal.child_verification_claims_root))
        );
        assert_eq!(
            meta["child_journals_root"],
            Value::String(hex_lower(&journal.child_journals_root))
        );
        assert_eq!(
            meta["child_effect_summaries_root"],
            Value::String(hex_lower(&journal.child_effect_summaries_root))
        );
        assert_eq!(
            meta["allowed_authority_roots_root"],
            Value::String(hex_lower(&journal.allowed_authority_roots_root))
        );
        assert_eq!(
            meta["accepted_receipts_root"],
            Value::String(hex_lower(&journal.accepted_receipts_root))
        );
        assert_eq!(
            meta["rejected_receipts_root"],
            Value::String(hex_lower(&journal.rejected_receipts_root))
        );
        assert_eq!(
            meta["carry_queue_pre_root"],
            Value::String(hex_lower(&journal.carry_queue_pre_root))
        );
        assert_eq!(
            meta["carry_queue_post_root"],
            Value::String(hex_lower(&journal.carry_queue_post_root))
        );
        assert_eq!(
            meta["dependency_lock_hash"],
            Value::String(hex_lower(&journal.dependency_lock_hash))
        );
        assert_eq!(
            meta["toolchain_lock_hash"],
            Value::String(hex_lower(&journal.toolchain_lock_hash))
        );
    }

    #[test]
    fn aggregate_guest_input_abi_is_bare_recursive_composition_v1() {
        let input = recursive_input();
        let bare = postcard::to_allocvec(&input).unwrap();
        let wrapped = postcard::to_allocvec(&ZenoProofInputV1::Recursive(input.clone())).unwrap();
        let decoded: RecursiveCompositionInputV1 = postcard::from_bytes(&bare).unwrap();

        assert_eq!(decoded, input);
        assert_ne!(bare, wrapped);
    }

    #[test]
    fn recursive_trusted_expectations_accept_matching_journal() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let req = json!({
            "recursive_expectations": recursive_expectations(&journal),
        });

        verify_recursive_trusted_expectations(&req, &journal, &recursive_receipt_profile())
            .unwrap();
    }

    #[test]
    fn recursive_verified_facts_require_root_matching_disclosure() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let journal_bytes = postcard::to_allocvec(&journal).unwrap();

        let receipt_profile = recursive_receipt_profile();
        let facts = recursive_verified_facts_from_disclosure(
            &journal,
            &journal_bytes,
            &input,
            &receipt_profile,
        )
        .unwrap();
        assert_eq!(
            facts["schema"],
            Value::String("zenodex.verified_recursive_stark_root_facts.v1".to_string())
        );
        assert_eq!(
            facts["child_verification_claims_root"],
            Value::String(hex_prefixed(&journal.child_verification_claims_root))
        );
        assert_eq!(
            facts["accepted_receipts_root"],
            Value::String(hex_prefixed(&journal.accepted_receipts_root))
        );
        assert_eq!(
            facts["cross_shard_message_ids_root"],
            Value::String(hex_prefixed(&journal.cross_shard_message_ids_root))
        );

        let mut substituted = input;
        substituted.statement.conflict_schedule_hash[0] ^= 1;
        assert_eq!(
            recursive_verified_facts_from_disclosure(
                &journal,
                &journal_bytes,
                &substituted,
                &receipt_profile,
            )
            .unwrap_err(),
            "recursive_input disclosure does not match verified journal"
        );
    }

    #[test]
    fn recursive_request_authenticates_receipt_once_and_preserves_response_schema() {
        use std::cell::Cell;

        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let journal_bytes = postcard::to_allocvec(&journal).unwrap();
        let proof = recursive_verification_proof(&journal);
        let req = recursive_verification_request(&input, &journal, &proof);
        let authentication_calls = Cell::new(0usize);
        let authenticated_journal = journal_bytes.clone();
        let authenticator = |_proof: &Value| {
            authentication_calls.set(authentication_calls.get() + 1);
            let claim =
                ReceiptClaim::ok(TAU_STATE_PROOF_AGGREGATE_ID, authenticated_journal.clone());
            let receipt = Receipt::new(
                InnerReceipt::Fake(FakeReceipt::new(claim)),
                authenticated_journal.clone(),
            );
            Ok(
                recursive_receipt_authentication::AuthenticatedReceipt::from_test_parts(
                    receipt,
                    recursive_receipt_profile(),
                ),
            )
        };

        let verified = try_verify_recursive_with_test_authenticator(
            &req,
            &proof,
            journal.post_state_root,
            authenticator,
        )
        .unwrap();
        assert_eq!(authentication_calls.get(), 1);

        let response = verification_response(Ok(VerificationSuccess::Recursive(verified)));
        assert_eq!(response["ok"], Value::Bool(true));
        assert_eq!(
            response["verified_recursive_facts"]["schema"],
            Value::String("zenodex.verified_recursive_stark_root_facts.v1".to_string())
        );
        assert_eq!(response.as_object().unwrap().len(), 2);
        assert_eq!(authentication_calls.get(), 1);
    }

    #[test]
    fn recursive_request_shape_mutations_reject_before_receipt_authentication() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let baseline_proof = recursive_verification_proof(&journal);
        let baseline_request = recursive_verification_request(&input, &journal, &baseline_proof);

        let mut request = baseline_request.clone();
        request["prover_note"] = Value::String("unreviewed".to_string());
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &baseline_proof,
            journal.post_state_root,
            "recursive_verify_request contains unknown field `prover_note`",
        );

        let mut request = baseline_request.clone();
        request.as_object_mut().unwrap().remove("schema");
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &baseline_proof,
            journal.post_state_root,
            "recursive_verify_request missing required field `schema`",
        );

        let mut request = baseline_request.clone();
        request["schema"] = Value::String("tau_state_proof_request".to_string());
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &baseline_proof,
            journal.post_state_root,
            "recursive_verify_request.schema must equal `tau_state_proof_verify`",
        );

        let mut request = baseline_request.clone();
        request["schema_version"] = json!(2);
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &baseline_proof,
            journal.post_state_root,
            "recursive_verify_request.schema_version must equal 1",
        );
    }

    #[test]
    fn recursive_proof_shape_mutations_reject_before_receipt_authentication() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let baseline_proof = recursive_verification_proof(&journal);
        let baseline_request = recursive_verification_request(&input, &journal, &baseline_proof);

        let mut proof = baseline_proof.clone();
        proof["prover_note"] = Value::String("unreviewed".to_string());
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request.proof contains unknown field `prover_note`",
        );

        let mut proof = baseline_proof.clone();
        proof.as_object_mut().unwrap().remove("schema");
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request.proof missing required field `schema`",
        );

        let mut proof = baseline_proof.clone();
        proof["schema_version"] = json!(2);
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request.proof.schema_version must equal 1",
        );

        let mut proof = baseline_proof.clone();
        proof["state_hash"] = Value::String(hx(241));
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request.proof.state_hash mismatch",
        );
    }

    #[test]
    fn recursive_meta_mutations_reject_before_receipt_authentication() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let baseline_proof = recursive_verification_proof(&journal);
        let baseline_request = recursive_verification_request(&input, &journal, &baseline_proof);

        let mut proof = baseline_proof.clone();
        proof["meta"]["prover_note"] = Value::String("unreviewed".to_string());
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request.proof.meta contains unknown field `prover_note`",
        );

        let mut proof = baseline_proof.clone();
        proof["meta"]
            .as_object_mut()
            .unwrap()
            .remove("toolchain_lock_hash");
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request.proof.meta missing required field `toolchain_lock_hash`",
        );

        let mut proof = baseline_proof.clone();
        proof["meta"]["epoch_id"] = Value::String("1".to_string());
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request.proof.meta.epoch_id must be an unsigned 64-bit integer",
        );

        let mut proof = baseline_proof.clone();
        proof["meta"]["proof_profile"] = Value::String("unreviewed-profile".to_string());
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "proof.meta.proof_profile mismatch",
        );
    }

    #[test]
    fn recursive_wire_reject_precedence_is_outer_then_proof_then_meta() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let baseline_proof = recursive_verification_proof(&journal);
        let baseline_request = recursive_verification_request(&input, &journal, &baseline_proof);

        let mut proof = baseline_proof.clone();
        proof["meta"]["prover_note"] = Value::String("nested".to_string());
        proof["prover_note"] = Value::String("envelope".to_string());
        let mut request = baseline_request.clone();
        request["proof"] = proof.clone();
        request["prover_note"] = Value::String("outer".to_string());
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request contains unknown field `prover_note`",
        );

        request.as_object_mut().unwrap().remove("prover_note");
        assert_recursive_wire_rejects_before_authentication(
            &request,
            &proof,
            journal.post_state_root,
            "recursive_verify_request.proof contains unknown field `prover_note`",
        );
    }

    #[test]
    fn every_recursive_verification_wire_field_is_required_before_authentication() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let proof = recursive_verification_proof(&journal);
        let request = recursive_verification_request(&input, &journal, &proof);

        for field in recursive_wire::RECURSIVE_VERIFY_REQUEST_FIELDS_V1 {
            let mut mutated_request = request.clone();
            mutated_request.as_object_mut().unwrap().remove(*field);
            let expected = format!("recursive_verify_request missing required field `{field}`");
            assert_recursive_wire_rejects_before_authentication(
                &mutated_request,
                &proof,
                journal.post_state_root,
                &expected,
            );
        }
        for field in recursive_wire::RECURSIVE_PROOF_FIELDS_V1 {
            let mut mutated_proof = proof.clone();
            mutated_proof.as_object_mut().unwrap().remove(*field);
            let mut mutated_request = request.clone();
            mutated_request["proof"] = mutated_proof.clone();
            let expected =
                format!("recursive_verify_request.proof missing required field `{field}`");
            assert_recursive_wire_rejects_before_authentication(
                &mutated_request,
                &mutated_proof,
                journal.post_state_root,
                &expected,
            );
        }
        for field in recursive_wire::RECURSIVE_PROOF_META_FIELDS_V1 {
            let mut mutated_proof = proof.clone();
            mutated_proof["meta"]
                .as_object_mut()
                .unwrap()
                .remove(*field);
            let mut mutated_request = request.clone();
            mutated_request["proof"] = mutated_proof.clone();
            let expected =
                format!("recursive_verify_request.proof.meta missing required field `{field}`");
            assert_recursive_wire_rejects_before_authentication(
                &mutated_request,
                &mutated_proof,
                journal.post_state_root,
                &expected,
            );
        }
    }

    #[test]
    fn recursive_production_path_has_one_cryptographic_verify_call_site() {
        let source = include_str!("main.rs");
        let recursive_entry = source
            .split_once("fn try_verify_recursive(\n")
            .unwrap()
            .1
            .split_once("#[cfg(test)]\nfn try_verify_recursive_with_test_authenticator")
            .unwrap()
            .0;
        assert_eq!(
            recursive_entry
                .matches("recursive_receipt_authentication::authenticate(proof)?")
                .count(),
            1
        );
        assert_eq!(recursive_entry.matches(".verify(").count(), 0);

        let profile_decoder = source
            .split_once("fn decode_verified_profile_receipt_from_proof(\n")
            .unwrap()
            .1
            .split_once("mod recursive_receipt_authentication")
            .unwrap()
            .0;
        assert_eq!(profile_decoder.matches(".verify(image_id)").count(), 1);

        let root_authenticator = source
            .split_once("pub(super) fn authenticate(proof: &Value)")
            .unwrap()
            .1
            .split_once("fn decode_receipt_from_proof")
            .unwrap()
            .0;
        assert_eq!(
            root_authenticator
                .matches("decode_verified_profile_receipt_from_proof")
                .count(),
            1
        );
        assert_eq!(root_authenticator.matches(".verify(").count(), 0);
    }

    #[test]
    fn recursive_verified_facts_emit_canonical_replay_id_order() {
        let mut input = recursive_input();
        input.children[0].accepted_receipt_ids = vec![h(82)];
        input.children[1].accepted_receipt_ids = vec![h(81)];

        let left_to_right = recursive_message("lane-a", "lane-b", 10);
        let right_to_left = recursive_message("lane-b", "lane-a", 20);
        assert!(left_to_right.message_id > right_to_left.message_id);
        input.children[0].outbox_messages = vec![left_to_right.clone()];
        input.children[0].inbox_messages = vec![right_to_left.clone()];
        input.children[1].outbox_messages = vec![right_to_left.clone()];
        input.children[1].inbox_messages = vec![left_to_right.clone()];
        for child in &mut input.children {
            refresh_recursive_child_disclosure_roots(child);
        }

        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let journal_bytes = postcard::to_allocvec(&journal).unwrap();
        let facts = recursive_verified_facts_from_disclosure(
            &journal,
            &journal_bytes,
            &input,
            &recursive_receipt_profile(),
        )
        .unwrap();

        assert_eq!(
            facts["accepted_receipt_ids"],
            json!([hex_prefixed(&h(81)), hex_prefixed(&h(82))])
        );
        assert_eq!(
            facts["cross_shard_message_ids"],
            json!([
                hex_prefixed(&right_to_left.message_id),
                hex_prefixed(&left_to_right.message_id),
            ])
        );
    }

    #[test]
    fn recursive_trusted_expectations_reject_missing_object() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let req = json!({});

        assert_eq!(
            verify_recursive_trusted_expectations(&req, &journal, &recursive_receipt_profile())
                .unwrap_err(),
            "recursive_expectations missing for recursive proof verification"
        );
    }

    #[test]
    fn recursive_trusted_expectations_reject_verifier_set_mismatch() {
        let input = recursive_input();
        let journal = compose_recursive_epoch_journal_v1(&input).unwrap();
        let mut expectations = recursive_expectations(&journal);
        expectations["verifier_set_root"] = Value::String(hx(99));
        let req = json!({
            "recursive_expectations": expectations,
        });

        assert_eq!(
            verify_recursive_trusted_expectations(&req, &journal, &recursive_receipt_profile())
                .unwrap_err(),
            "recursive_expectations.verifier_set_root mismatch"
        );
    }

    #[test]
    fn recursive_trusted_expectations_reject_omitted_child_root() {
        let journal = compose_recursive_epoch_journal_v1(&recursive_input()).unwrap();
        let mut expectations = recursive_expectations(&journal);
        expectations
            .as_object_mut()
            .unwrap()
            .remove("child_journals_root");
        let req = json!({"recursive_expectations": expectations});

        assert_eq!(
            verify_recursive_trusted_expectations(&req, &journal, &recursive_receipt_profile())
                .unwrap_err(),
            "recursive_expectations.child_journals_root missing"
        );
    }

    #[test]
    fn recursive_trusted_expectations_reject_substituted_child_root() {
        let journal = compose_recursive_epoch_journal_v1(&recursive_input()).unwrap();
        let mut expectations = recursive_expectations(&journal);
        expectations["child_effect_summaries_root"] = Value::String(hx(99));
        let req = json!({"recursive_expectations": expectations});

        assert_eq!(
            verify_recursive_trusted_expectations(&req, &journal, &recursive_receipt_profile())
                .unwrap_err(),
            "recursive_expectations.child_effect_summaries_root mismatch"
        );
    }

    #[test]
    fn recursive_trusted_expectations_reject_unknown_key() {
        let journal = compose_recursive_epoch_journal_v1(&recursive_input()).unwrap();
        let mut expectations = recursive_expectations(&journal);
        expectations["prover_note"] = Value::String("untrusted".to_string());
        let req = json!({"recursive_expectations": expectations});

        assert_eq!(
            verify_recursive_trusted_expectations(&req, &journal, &recursive_receipt_profile())
                .unwrap_err(),
            "recursive_expectations.prover_note unknown"
        );
    }

    #[test]
    fn risc0_dev_mode_value_parser_is_explicit() {
        assert!(risc0_dev_mode_value_enabled("1"));
        assert!(risc0_dev_mode_value_enabled("true"));
        assert!(risc0_dev_mode_value_enabled("TRUE"));
        assert!(risc0_dev_mode_value_enabled(" yes "));
        assert!(risc0_dev_mode_value_enabled("on"));
        assert!(!risc0_dev_mode_value_enabled(""));
        assert!(!risc0_dev_mode_value_enabled("0"));
        assert!(!risc0_dev_mode_value_enabled("false"));
    }

    #[test]
    fn recursive_receipt_profile_policy_is_exact() {
        for profile in [
            RECURSIVE_EPOCH_PROFILE_V1,
            RECURSIVE_SPOT_LEAF_PROFILE_V1,
            RECURSIVE_PERPS_NP_LEAF_PROFILE_V1,
            RECURSIVE_ZUSD_LEAF_PROFILE_V1,
        ] {
            assert!(require_receipt_kind_for_profile(profile, ProofReceiptKind::Succinct).is_ok());
            assert_eq!(
                require_receipt_kind_for_profile(profile, ProofReceiptKind::Composite).unwrap_err(),
                format!(
                    "receipt kind mismatch for profile {profile}: expected succinct, got composite"
                )
            );
            assert_eq!(
                require_receipt_kind_for_profile(profile, ProofReceiptKind::Groth16).unwrap_err(),
                format!(
                    "receipt kind mismatch for profile {profile}: expected succinct, got groth16"
                )
            );
        }
        assert!(require_receipt_kind_for_profile(
            RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
            ProofReceiptKind::Composite,
        )
        .is_ok());
        assert_eq!(
            require_receipt_kind_for_profile(RECURSIVE_EPOCH_PROFILE_V1, ProofReceiptKind::Fake,)
                .unwrap_err(),
            "receipt kind policy rejects fake receipt"
        );
        assert_eq!(
            require_receipt_kind_for_profile("unknown_profile", ProofReceiptKind::Succinct)
                .unwrap_err(),
            "receipt kind policy has no entry for profile unknown_profile"
        );
    }

    #[test]
    fn receipt_kind_declarations_are_required_and_match_actual_kind() {
        assert_eq!(
            require_requested_receipt_kind(&json!({}), ProofReceiptKind::Succinct).unwrap_err(),
            "receipt_kind missing"
        );
        assert_eq!(
            require_requested_receipt_kind(
                &json!({"receipt_kind": "composite"}),
                ProofReceiptKind::Succinct,
            )
            .unwrap_err(),
            "receipt_kind mismatch: expected succinct, got composite"
        );
        let missing_meta = json!({"meta": {}});
        assert_eq!(
            require_proof_meta_receipt_kind(&missing_meta, ProofReceiptKind::Succinct).unwrap_err(),
            "proof.meta.receipt_kind missing"
        );
        let wrong_meta = json!({"meta": {"receipt_kind": "groth16"}});
        assert_eq!(
            require_proof_meta_receipt_kind(&wrong_meta, ProofReceiptKind::Succinct).unwrap_err(),
            "proof.meta.receipt_kind mismatch: declared groth16, actual succinct"
        );
        let matching_meta = json!({"meta": {"receipt_kind": "succinct"}});
        assert!(
            require_proof_meta_receipt_kind(&matching_meta, ProofReceiptKind::Succinct,).is_ok()
        );
    }

    #[test]
    fn summary_test_profile_is_inadmissible_as_recursive_child() {
        assert_eq!(
            require_recursive_child_receipt_kind(
                RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
                ProofReceiptKind::Composite,
            )
            .unwrap_err(),
            "recursive child receipt kind mismatch: expected succinct, got composite"
        );
        assert_eq!(
            require_recursive_child_receipt_kind(
                RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
                ProofReceiptKind::Succinct,
            )
            .unwrap_err(),
            format!(
                "receipt kind mismatch for profile {RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1}: expected composite, got succinct"
            )
        );
    }

    #[test]
    fn fake_receipt_is_rejected_before_verification() {
        let journal = vec![1u8, 2, 3];
        let claim = ReceiptClaim::ok([1u32; 8], journal.clone());
        let receipt = Receipt::new(InnerReceipt::Fake(FakeReceipt::new(claim)), journal);

        assert_eq!(receipt_kind(&receipt).unwrap(), ProofReceiptKind::Fake);
        assert_eq!(
            reject_fake_receipt(&receipt, "test receipt").unwrap_err(),
            "test receipt fake receipt rejected"
        );
    }

    #[test]
    fn receipt_codec_round_trip_is_depth_limited_json() {
        let journal = vec![1u8, 2, 3];
        let claim = ReceiptClaim::ok([1u32; 8], journal.clone());
        let receipt = Receipt::new(InnerReceipt::Fake(FakeReceipt::new(claim)), journal);

        let encoded = encode_receipt(&receipt);
        let bytes = base64::engine::general_purpose::STANDARD
            .decode(&encoded)
            .unwrap();
        assert_eq!(bytes.first(), Some(&b'{'));
        assert_eq!(
            receipt_kind(&decode_receipt_b64(&encoded).unwrap()).unwrap(),
            ProofReceiptKind::Fake
        );

        let mut noncanonical = bytes;
        noncanonical.push(b' ');
        let noncanonical = base64::engine::general_purpose::STANDARD.encode(noncanonical);
        assert_eq!(
            decode_receipt_b64(&noncanonical).unwrap_err(),
            "receipt bytes are not canonical for declared codec"
        );

        let legacy_binary = base64::engine::general_purpose::STANDARD.encode([0u8; 32]);
        assert!(decode_receipt_b64(&legacy_binary)
            .unwrap_err()
            .starts_with("invalid receipt bytes:"));
    }

    #[test]
    fn receipt_codec_rejects_duplicate_json_keys() {
        let journal = vec![1u8, 2, 3];
        let claim = ReceiptClaim::ok([1u32; 8], journal.clone());
        let receipt = Receipt::new(InnerReceipt::Fake(FakeReceipt::new(claim)), journal);
        let value = serde_json::to_value(&receipt).unwrap();
        let (key, duplicate_value) = value.as_object().unwrap().iter().next().unwrap();
        let mut bytes = serde_json::to_vec(&receipt).unwrap();
        assert_eq!(bytes.pop(), Some(b'}'));
        bytes.extend_from_slice(b",");
        bytes.extend_from_slice(serde_json::to_string(key).unwrap().as_bytes());
        bytes.push(b':');
        bytes.extend_from_slice(serde_json::to_string(duplicate_value).unwrap().as_bytes());
        bytes.push(b'}');
        let encoded = base64::engine::general_purpose::STANDARD.encode(bytes);

        assert!(decode_receipt_b64(&encoded)
            .unwrap_err()
            .contains("duplicate field"));
    }

    #[test]
    fn receipt_codec_rejects_excessive_recursive_receipt_depth() {
        let claim = ReceiptClaim::ok([1u32; 8], Vec::new());
        let receipt = Receipt::new(InnerReceipt::Fake(FakeReceipt::new(claim)), Vec::new());
        let mut receipt_value = serde_json::to_value(receipt).unwrap();
        let mut nested = json!({
            "segments": [],
            "assumption_receipts": [],
            "verifier_parameters": Digest::ZERO,
        });
        for _ in 0..140 {
            nested = json!({
                "segments": [],
                "assumption_receipts": [{"Composite": nested}],
                "verifier_parameters": Digest::ZERO,
            });
        }
        receipt_value["inner"] = json!({"Composite": nested});
        let bytes = serde_json::to_vec(&receipt_value).unwrap();
        let encoded = base64::engine::general_purpose::STANDARD.encode(bytes);

        assert!(decode_receipt_b64(&encoded)
            .unwrap_err()
            .contains("recursion limit exceeded"));
    }

    #[test]
    fn receipt_codec_marker_is_exact() {
        assert!(require_receipt_codec(
            Some(&Value::String(RECEIPT_CODEC_V1.to_string())),
            "receipt_codec",
        )
        .is_ok());
        assert_eq!(
            require_receipt_codec(None, "receipt_codec").unwrap_err(),
            "receipt_codec missing"
        );
        assert_eq!(
            require_receipt_codec(
                Some(&Value::String("risc0_receipt_bincode_v0".to_string())),
                "receipt_codec",
            )
            .unwrap_err(),
            "receipt_codec unsupported"
        );
    }

    #[test]
    fn risc0_digest_text_uses_canonical_little_endian_bytes() {
        assert_eq!(
            hex_u32_words([
                0x01234567, 0x89abcdef, 0x10203040, 0x50607080, 0x0a0b0c0d, 0x0e0f1011, 0x12131415,
                0x16171819,
            ]),
            "67452301efcdab8940302010807060500d0c0b0a11100f0e1514131219181716"
        );
    }

    #[test]
    fn resource_caps_are_absolute_and_inclusive() {
        assert!(require_receipt_base64_len(MAX_RECEIPT_BASE64_BYTES).is_ok());
        assert!(require_receipt_bytes_len(MAX_RECEIPT_BYTES).is_ok());
        assert!(require_request_bytes_len(MAX_REQUEST_BYTES).is_ok());
        assert_eq!(
            require_receipt_base64_len(MAX_RECEIPT_BASE64_BYTES + 1).unwrap_err(),
            format!("receipt base64 exceeds {MAX_RECEIPT_BASE64_BYTES} byte limit")
        );
        assert_eq!(
            require_receipt_bytes_len(MAX_RECEIPT_BYTES + 1).unwrap_err(),
            format!("receipt bytes exceed {MAX_RECEIPT_BYTES} byte limit")
        );
        assert_eq!(
            require_request_bytes_len(MAX_REQUEST_BYTES + 1).unwrap_err(),
            format!("request exceeds {MAX_REQUEST_BYTES} byte limit")
        );
    }

    #[test]
    fn bounded_reader_accepts_one_json_value_and_parser_rejects_trailing_value() {
        let stdin = read_bounded_utf8(&b"{\"schema\":\"x\"}"[..]).unwrap();
        assert!(parse_request_json(&stdin).is_ok());
        assert!(parse_request_json("{} {}").is_err());
    }

    #[test]
    fn request_parser_rejects_duplicate_keys_at_every_depth() {
        for raw in [
            r#"{"schema":"first","schema":"second"}"#,
            r#"{"outer":{"key":1,"key":2}}"#,
            r#"{"outer":[{"key":1,"key":2}]}"#,
            r#"{"schema":"first","\u0073chema":"second"}"#,
            r#"{"/":1,"\/":2}"#,
            r#"{"\\":1,"\u005c":2}"#,
            r#"{"\u0022":1,"\"":2}"#,
            r#"{"\uD83D\uDE00":1,"\ud83d\ude00":2}"#,
        ] {
            assert!(
                parse_request_json(raw)
                    .unwrap_err()
                    .contains("duplicate JSON object key"),
                "raw={raw}"
            );
        }

        assert!(parse_request_json(r#"{"left":{"key":1},"right":{"key":2}}"#).is_ok());
    }

    #[test]
    fn strict_request_parser_preserves_arbitrary_precision_numbers() {
        let raw = r#"{"amount":340282366920938463463374607431768211456,"ratio":1e400}"#;
        let parsed = parse_request_json(raw).unwrap();
        assert_eq!(
            parsed["amount"].as_number().unwrap().to_string(),
            "340282366920938463463374607431768211456"
        );
        assert_eq!(parsed["ratio"].as_number().unwrap().to_string(), "1e400");
    }

    #[test]
    fn embedded_state_json_rejects_duplicate_keys() {
        assert!(parse_dex_snapshot_json(r#"{"pools":[],"pools":[]}"#)
            .unwrap_err()
            .contains("duplicate JSON object key"));
        for raw in [
            r#"{"accounts":[],"accounts":[]}"#,
            r#"{"balances":[],"balances":[]}"#,
        ] {
            assert!(strict_json::parse_value(raw)
                .unwrap_err()
                .contains("duplicate JSON object key"));
        }
    }

    #[test]
    fn recursive_json_inputs_reject_unknown_fields() {
        let mut baseline = serde_json::to_value(recursive_input()).unwrap();
        baseline["children"][0]["outbox_messages"] =
            json!([recursive_message("lane-a", "lane-b", 91)]);
        baseline["children"][0]["inbox_messages"] =
            json!([recursive_message("lane-b", "lane-a", 94)]);

        for pointer in [
            "",
            "/statement",
            "/children/0",
            "/children/0/descriptor",
            "/children/0/summary",
            "/children/0/asset_delta_rows/0",
            "/children/0/outbox_messages/0",
            "/children/0/inbox_messages/0",
        ] {
            let mut value = baseline.clone();
            value
                .pointer_mut(pointer)
                .and_then(Value::as_object_mut)
                .unwrap()
                .insert(
                    "uncommitted_note".to_string(),
                    Value::String("ignored before hardening".into()),
                );
            let request = json!({"recursive_input": value});
            assert!(
                parse_recursive_input(&request)
                    .unwrap_err()
                    .contains("unknown field `uncommitted_note`"),
                "pointer={pointer}"
            );
        }

        let mut summary = serde_json::to_value(recursive_summary_leaf_summary()).unwrap();
        summary["uncommitted_note"] = Value::Bool(true);
        assert!(
            parse_recursive_summary(&json!({"recursive_summary": summary}))
                .unwrap_err()
                .contains("unknown field `uncommitted_note`")
        );

        for result in [
            parse_spot_recursive_leaf_input(
                &json!({"spot_recursive_leaf_input": {"uncommitted_note": true}}),
            )
            .map(|_| ()),
            parse_perps_np_recursive_leaf_input(
                &json!({"perps_np_recursive_leaf_input": {"uncommitted_note": true}}),
            )
            .map(|_| ()),
            parse_zusd_recursive_leaf_input(
                &json!({"zusd_recursive_leaf_input": {"uncommitted_note": true}}),
            )
            .map(|_| ()),
        ] {
            assert!(result
                .unwrap_err()
                .contains("unknown field `uncommitted_note`"));
        }
    }

    #[test]
    fn recursive_wire_allowlists_match_serialized_typed_fields() {
        fn assert_fields(value: &Value, expected: &[&str]) {
            let actual = value
                .as_object()
                .unwrap()
                .keys()
                .map(String::as_str)
                .collect::<std::collections::BTreeSet<_>>();
            let expected = expected
                .iter()
                .copied()
                .collect::<std::collections::BTreeSet<_>>();
            assert_eq!(actual, expected);
        }

        let input = serde_json::to_value(recursive_input()).unwrap();
        assert_fields(&input, recursive_wire::COMPOSITION_FIELDS);
        assert_fields(&input["statement"], recursive_wire::STATEMENT_FIELDS);
        assert_fields(&input["children"][0], recursive_wire::CHILD_FIELDS);
        assert_fields(
            &input["children"][0]["descriptor"],
            recursive_wire::DESCRIPTOR_FIELDS,
        );
        assert_fields(
            &input["children"][0]["summary"],
            recursive_wire::SUMMARY_FIELDS,
        );
        assert_fields(
            &input["children"][0]["asset_delta_rows"][0],
            recursive_wire::ASSET_DELTA_FIELDS,
        );
        assert_fields(
            &serde_json::to_value(recursive_message("lane-a", "lane-b", 91)).unwrap(),
            recursive_wire::MESSAGE_FIELDS,
        );

        let spot_snapshot = DexStateV1::empty().to_snapshot();
        let spot = SpotRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "spot-lane".to_string(),
            risc0_image_id: recursive_image(41),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            spot_input: StateProofInputV1 {
                state_hash: h(1),
                block_timestamp: 1,
                pre_app_hash_present: true,
                pre_app_hash: h(2),
                pre_state: spot_snapshot,
                txs: Vec::new(),
                pre_nonces: Vec::new(),
                tx_ingress: Vec::new(),
                chain_balances_post: Vec::new(),
                expected_post_app_hash: h(3),
                protocol_fee_share_bps: 0,
                protocol_fee_recipient_pubkey: None,
                tx_execution_order: Vec::new(),
                route_price_intervals: Vec::new(),
                route_price_interval_authority: None,
                route_price_interval_authority_policy: None,
                route_price_interval_max_width_bps: None,
                shared_pool_frontier_signature_certificates: Vec::new(),
            },
        };
        let perps = PerpsNpRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "perps-lane".to_string(),
            risc0_image_id: recursive_image(42),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            perps_input: PerpsNpTransitionInputV1 {
                state_hash: h(1),
                chain_id: "tau-test".to_string(),
                pre_app_hash_present: true,
                pre_app_hash: h(2),
                pre_state: PerpsNpSnapshotV1::empty(),
                actions: Vec::new(),
                expected_post_app_hash: h(3),
                risc0_image_id: recursive_image(42),
            },
        };
        let zusd = ZusdRecursiveLeafInputV1 {
            chain_id: "tau-test".to_string(),
            epoch_id: 7,
            lane_id: "zusd-lane".to_string(),
            risc0_image_id: recursive_image(43),
            public_policy_hash: h(10),
            feature_suite_hash: h(11),
            dependency_lock_hash: h(12),
            toolchain_lock_hash: h(13),
            zusd_input: ZusdTransitionInputV1 {
                state_hash: h(1),
                chain_id: "tau-test".to_string(),
                pre_app_hash_present: true,
                pre_app_hash: h(2),
                pre_state: ZusdSnapshotV1::empty(),
                operation: ZusdOperationV1::DepositMint {
                    pubkey: "wallet-a".to_string(),
                    collateral_asset: "tAGRS".to_string(),
                    deposit_amount_e8: 1,
                    mint_amount_e8: 1,
                    oracle: OracleBindingV1 {
                        oracle_bridge_id: "oracle".to_string(),
                        oracle_bridge_hash: hx(4),
                        price_e8: 1,
                        price_timestamp: 1,
                        max_staleness_seconds: 1,
                        observed_at: 1,
                        pre_price_batch_commitment: hx(5),
                    },
                    mcr_bps: 1,
                    nonce: 1,
                },
                expected_post_app_hash: h(3),
                risc0_image_id: recursive_image(43),
            },
        };
        for (value, payload_field) in [
            (serde_json::to_value(spot).unwrap(), "spot_input"),
            (serde_json::to_value(perps).unwrap(), "perps_input"),
            (serde_json::to_value(zusd).unwrap(), "zusd_input"),
        ] {
            let mut expected = recursive_wire::LEAF_WRAPPER_FIELDS.to_vec();
            expected.push(payload_field);
            assert_fields(&value, &expected);
        }
    }

    #[test]
    fn recursive_wire_missing_fields_and_wrong_containers_fail_closed() {
        let mut missing_statement = serde_json::to_value(recursive_input()).unwrap();
        missing_statement
            .as_object_mut()
            .unwrap()
            .remove("statement");
        assert!(
            parse_recursive_input(&json!({"recursive_input": missing_statement}))
                .unwrap_err()
                .contains("missing field `statement`")
        );

        let mut wrong_children = serde_json::to_value(recursive_input()).unwrap();
        wrong_children["children"] = json!({});
        assert_eq!(
            parse_recursive_input(&json!({"recursive_input": wrong_children})).unwrap_err(),
            "recursive_input.children must be a list"
        );

        let mut wrong_descriptor = serde_json::to_value(recursive_input()).unwrap();
        wrong_descriptor["children"][0]["descriptor"] = json!([]);
        assert_eq!(
            parse_recursive_input(&json!({"recursive_input": wrong_descriptor})).unwrap_err(),
            "recursive_input.children[0].descriptor must be an object"
        );

        let mut wrong_rows = serde_json::to_value(recursive_input()).unwrap();
        wrong_rows["children"][0]["asset_delta_rows"] = json!({});
        assert_eq!(
            parse_recursive_input(&json!({"recursive_input": wrong_rows})).unwrap_err(),
            "recursive_input.children[0].asset_delta_rows must be a list"
        );
    }

    #[test]
    fn recursive_child_proofs_reject_omitted_child_receipt() {
        let input = recursive_input();
        let req = json!({
            "child_receipt_codec": RECEIPT_CODEC_V1,
            "child_proofs": [],
        });
        assert_eq!(
            parse_recursive_child_receipts(&req, &input).unwrap_err(),
            "child_proofs length mismatch"
        );
    }

    #[test]
    fn recursive_summary_leaf_meta_binds_summary_leaf_image_id() {
        let summary = recursive_summary_leaf_summary();
        let meta = recursive_summary_leaf_meta(&summary, ProofReceiptKind::Composite);
        assert_eq!(
            meta["risc0_image_id"],
            Value::String(hex_u32_words(TAU_STATE_PROOF_SUMMARY_LEAF_ID))
        );
        assert_eq!(meta["receipt_kind"], "composite");
        assert_eq!(
            meta["child_image_id"],
            Value::String(hex_u32_words(summary.risc0_image_id))
        );
        assert!(validate_recursive_effect_summary_shape_v1(&summary).is_ok());
    }

    #[test]
    fn recursive_spot_leaf_meta_binds_spot_leaf_image_id() {
        let summary = recursive_spot_leaf_summary();
        let meta = recursive_spot_leaf_meta(&summary, &[], ProofReceiptKind::Succinct);
        assert_eq!(
            meta["risc0_image_id"],
            Value::String(hex_u32_words(TAU_STATE_PROOF_SPOT_LEAF_ID))
        );
        assert_eq!(meta["receipt_kind"], "succinct");
        assert_eq!(
            meta["child_image_id"],
            Value::String(hex_u32_words(summary.risc0_image_id))
        );
        assert_eq!(
            meta["proof_type"],
            Value::String(PROOF_TYPE_RECURSIVE_SPOT_LEAF.to_string())
        );
        assert_eq!(
            meta["proof_profile"],
            Value::String(RECURSIVE_SPOT_LEAF_PROFILE_V1.to_string())
        );
        assert_eq!(meta["asset_delta_rows"], Value::Array(vec![]));
        assert!(validate_recursive_effect_summary_shape_v1(&summary).is_ok());
    }

    #[test]
    fn recursive_perps_np_leaf_meta_binds_perps_np_leaf_image_id() {
        let summary = recursive_perps_np_leaf_summary();
        let meta = recursive_perps_np_leaf_meta(&summary, &[], ProofReceiptKind::Succinct);
        assert_eq!(
            meta["risc0_image_id"],
            Value::String(hex_u32_words(TAU_STATE_PROOF_PERPS_NP_LEAF_ID))
        );
        assert_eq!(meta["receipt_kind"], "succinct");
        assert_eq!(
            meta["child_image_id"],
            Value::String(hex_u32_words(summary.risc0_image_id))
        );
        assert_eq!(
            meta["proof_type"],
            Value::String(PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF.to_string())
        );
        assert_eq!(
            meta["proof_profile"],
            Value::String(RECURSIVE_PERPS_NP_LEAF_PROFILE_V1.to_string())
        );
        assert_eq!(meta["lane_kind"], Value::String("perps_np".to_string()));
        assert_eq!(meta["asset_delta_rows"], Value::Array(vec![]));
        assert!(validate_recursive_effect_summary_shape_v1(&summary).is_ok());
    }

    #[test]
    fn recursive_zusd_leaf_meta_binds_zusd_leaf_image_id() {
        let summary = recursive_zusd_leaf_summary();
        let meta = recursive_zusd_leaf_meta(&summary, &[], ProofReceiptKind::Succinct);
        assert_eq!(
            meta["risc0_image_id"],
            Value::String(hex_u32_words(TAU_STATE_PROOF_ZUSD_LEAF_ID))
        );
        assert_eq!(meta["receipt_kind"], "succinct");
        assert_eq!(
            meta["child_image_id"],
            Value::String(hex_u32_words(summary.risc0_image_id))
        );
        assert_eq!(
            meta["proof_type"],
            Value::String(PROOF_TYPE_RECURSIVE_ZUSD_LEAF.to_string())
        );
        assert_eq!(
            meta["proof_profile"],
            Value::String(RECURSIVE_ZUSD_LEAF_PROFILE_V1.to_string())
        );
        assert_eq!(meta["lane_kind"], Value::String("zusd".to_string()));
        assert!(validate_recursive_effect_summary_shape_v1(&summary).is_ok());
    }

    #[test]
    fn recursive_zusd_leaf_meta_includes_exact_asset_delta_rows() {
        let mut summary = recursive_zusd_leaf_summary();
        let rows = vec![RecursiveAssetDeltaRowV1 {
            asset_id: "zUSD".to_string(),
            debit_atoms: 0,
            credit_atoms: 11,
            authorized_mint_atoms: 11,
            authorized_burn_atoms: 0,
            authority_root: h(10),
        }];
        summary.asset_delta_root = recursive_asset_delta_root_v1(&rows).unwrap();

        let meta = recursive_zusd_leaf_meta(&summary, &rows, ProofReceiptKind::Succinct);

        assert_eq!(
            meta["asset_delta_root"],
            Value::String(hex_lower(&summary.asset_delta_root))
        );
        assert_eq!(meta["asset_delta_rows"][0]["asset_id"], "zUSD");
        assert_eq!(meta["asset_delta_rows"][0]["debit_atoms"], "0");
        assert_eq!(meta["asset_delta_rows"][0]["credit_atoms"], "11");
        assert_eq!(meta["asset_delta_rows"][0]["authorized_mint_atoms"], "11");
        assert_eq!(meta["asset_delta_rows"][0]["authorized_burn_atoms"], "0");
        assert_eq!(
            meta["asset_delta_rows"][0]["authority_root"],
            Value::String(hx(10))
        );
    }

    #[test]
    fn recursive_spot_leaf_meta_includes_exact_asset_delta_rows() {
        let mut summary = recursive_spot_leaf_summary();
        let rows = vec![RecursiveAssetDeltaRowV1 {
            asset_id: "TEST".to_string(),
            debit_atoms: 0,
            credit_atoms: 7,
            authorized_mint_atoms: 7,
            authorized_burn_atoms: 0,
            authority_root: h(10),
        }];
        summary.asset_delta_root = recursive_asset_delta_root_v1(&rows).unwrap();

        let meta = recursive_spot_leaf_meta(&summary, &rows, ProofReceiptKind::Succinct);

        assert_eq!(
            meta["asset_delta_root"],
            Value::String(hex_lower(&summary.asset_delta_root))
        );
        assert_eq!(meta["asset_delta_rows"][0]["asset_id"], "TEST");
        assert_eq!(meta["asset_delta_rows"][0]["credit_atoms"], "7");
        assert_eq!(meta["asset_delta_rows"][0]["authorized_mint_atoms"], "7");
        let parsed = parse_recursive_asset_delta_rows_meta(meta.as_object().unwrap()).unwrap();
        assert_eq!(
            recursive_asset_delta_root_v1(&parsed).unwrap(),
            summary.asset_delta_root
        );
    }

    #[test]
    fn recursive_perps_np_leaf_meta_includes_exact_asset_delta_rows() {
        let mut summary = recursive_perps_np_leaf_summary();
        let rows = vec![RecursiveAssetDeltaRowV1 {
            asset_id: "USDC".to_string(),
            debit_atoms: 5,
            credit_atoms: 0,
            authorized_mint_atoms: 0,
            authorized_burn_atoms: 0,
            authority_root: [0u8; 32],
        }];
        summary.asset_delta_root = recursive_asset_delta_root_v1(&rows).unwrap();

        let meta = recursive_perps_np_leaf_meta(&summary, &rows, ProofReceiptKind::Succinct);

        assert_eq!(
            meta["asset_delta_root"],
            Value::String(hex_lower(&summary.asset_delta_root))
        );
        assert_eq!(meta["asset_delta_rows"][0]["asset_id"], "USDC");
        assert_eq!(meta["asset_delta_rows"][0]["debit_atoms"], "5");
        assert_eq!(
            meta["asset_delta_rows"][0]["authority_root"],
            Value::String(hx(0))
        );
        let parsed = parse_recursive_asset_delta_rows_meta(meta.as_object().unwrap()).unwrap();
        assert_eq!(
            recursive_asset_delta_root_v1(&parsed).unwrap(),
            summary.asset_delta_root
        );
    }

    #[test]
    fn recursive_leaf_meta_asset_delta_rows_reject_root_mismatch() {
        let mut summary = recursive_spot_leaf_summary();
        let rows = vec![RecursiveAssetDeltaRowV1 {
            asset_id: "TEST".to_string(),
            debit_atoms: 0,
            credit_atoms: 7,
            authorized_mint_atoms: 7,
            authorized_burn_atoms: 0,
            authority_root: h(10),
        }];
        summary.asset_delta_root = h(99);
        let proof = json!({
            "meta": recursive_spot_leaf_meta(&summary, &rows, ProofReceiptKind::Succinct),
        });

        assert_eq!(
            expect_recursive_asset_delta_rows_meta(&proof, summary.asset_delta_root).unwrap_err(),
            "proof.meta.asset_delta_rows root mismatch"
        );
    }

    fn spot_fee_journal(
        protocol_fee_share_bps: u32,
        protocol_fee_recipient_pubkey: Option<&str>,
    ) -> StateProofJournalV1 {
        StateProofJournalV1 {
            journal_version: 1,
            state_hash: h(1),
            txs_commitment: h(2),
            tx_execution_order_commitment: h(3),
            ingress_commitment: h(4),
            pre_nonce_root: h(5),
            post_nonce_root: h(6),
            accepted_receipts_root: h(7),
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            post_app_hash: h(8),
            protocol_fee_share_bps,
            protocol_fee_recipient_pubkey: protocol_fee_recipient_pubkey.map(str::to_string),
            route_price_interval_count: 0,
            route_price_intervals_root: route_price_intervals_root_v1(&[]).unwrap(),
            route_price_interval_authority_root: route_price_interval_authority_root_v1(None)
                .unwrap(),
            route_price_interval_authority_policy_root:
                route_price_interval_authority_policy_root_v1(None).unwrap(),
            route_price_interval_max_width_bps: None,
            shared_pool_frontier_signature_certificate_count: 0,
            shared_pool_frontier_signature_certificates_root:
                frontier_signature_certificates_root_v1(&[]).unwrap(),
        }
    }

    fn spot_proof_meta(protocol_fee_share_bps: u32, recipient: Value) -> Value {
        json!({
            "proof_type": PROOF_TYPE,
            "proof": "unused",
            "meta": {
                "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_GUEST_ID),
                "protocol_fee_share_bps": protocol_fee_share_bps,
                "protocol_fee_recipient_pubkey": recipient,
                "route_price_interval_count": 0,
                "route_price_intervals_root": hex_lower(
                    &route_price_intervals_root_v1(&[]).unwrap()
                ),
                "route_price_interval_authority_root": hex_lower(
                    &route_price_interval_authority_root_v1(None).unwrap()
                ),
                "route_price_interval_authority_policy_root": hex_lower(
                    &route_price_interval_authority_policy_root_v1(None).unwrap()
                ),
                "route_price_interval_max_width_bps": Value::Null,
                "shared_pool_frontier_signature_certificate_count": 0,
                "shared_pool_frontier_signature_certificates_root": hex_lower(
                    &frontier_signature_certificates_root_v1(&[]).unwrap()
                )
            }
        })
    }

    fn route_interval_authority_for_root(interval_root: [u8; 32]) -> RoutePriceIntervalAuthorityV1 {
        RoutePriceIntervalAuthorityV1 {
            schema: "zenodex.route_order.price_interval_authority.v1".to_string(),
            source_id: "test-route-interval-oracle".to_string(),
            source_root: h(7),
            price_timestamp: 10,
            max_staleness_seconds: 60,
            route_price_intervals_root: interval_root,
        }
    }

    fn route_interval_authority_json(authority: &RoutePriceIntervalAuthorityV1) -> Value {
        json!({
            "schema": authority.schema,
            "source_id": authority.source_id,
            "source_root": hex_lower(&authority.source_root),
            "price_timestamp": authority.price_timestamp,
            "max_staleness_seconds": authority.max_staleness_seconds,
            "route_price_intervals_root": hex_lower(&authority.route_price_intervals_root)
        })
    }

    fn route_interval_authority_policy_for(
        authority: &RoutePriceIntervalAuthorityV1,
    ) -> RoutePriceIntervalAuthorityPolicyV1 {
        RoutePriceIntervalAuthorityPolicyV1 {
            schema: "zenodex.route_order.price_interval_authority_policy.v1".to_string(),
            policy_id: "test-route-interval-policy".to_string(),
            sources: vec![RoutePriceIntervalAuthorityPolicySourceV1 {
                source_id: authority.source_id.clone(),
                source_root: authority.source_root,
                verification_root: h(8),
                verification_status: "verified".to_string(),
            }],
        }
    }

    fn route_interval_authority_policy_json(policy: &RoutePriceIntervalAuthorityPolicyV1) -> Value {
        let sources: Vec<Value> = policy
            .sources
            .iter()
            .map(|source| {
                json!({
                    "source_id": source.source_id,
                    "source_root": hex_lower(&source.source_root),
                    "verification_root": hex_lower(&source.verification_root),
                    "verification_status": source.verification_status,
                })
            })
            .collect();
        json!({
            "schema": policy.schema,
            "policy_id": policy.policy_id,
            "sources": sources,
        })
    }

    fn frontier_signature_certificate_json() -> Value {
        json!({
            "schema": "zenodex.mev.shared_pool_frontier_signature_certificate.v1",
            "pool_id": "pool:cpmm:frontier-delta-witness-min",
            "fee_bps": 0,
            "row_states": [
                {"reserve_a_atoms": 1, "reserve_b_atoms": 1},
                {"reserve_a_atoms": 1, "reserve_b_atoms": 2}
            ],
            "victims": [
                {"direction": "B_TO_A", "amount_in_atoms": 1, "min_out_atoms": 1},
                {"direction": "A_TO_B", "amount_in_atoms": 1, "min_out_atoms": 1}
            ],
            "signatures": [
                {
                    "state": {"reserve_a_atoms": 1, "reserve_b_atoms": 1},
                    "suffix_signature_masks": [0]
                },
                {
                    "state": {"reserve_a_atoms": 1, "reserve_b_atoms": 2},
                    "suffix_signature_masks": [0, 2, 3]
                }
            ],
            "claimed_frontier_states": [
                {"reserve_a_atoms": 1, "reserve_b_atoms": 2}
            ]
        })
    }

    fn route_intent_json(kind: &str) -> Value {
        let mut value = json!({
            "module": "TauSwap",
            "version": "v1",
            "kind": kind,
            "intent_id": "route-bdd",
            "sender_pubkey": "alice",
            "deadline": 100,
            "quote_receipt_hash": "0x1111111111111111111111111111111111111111111111111111111111111111",
            "asset_in": "A",
            "asset_out": "B",
            "leg_indices": [0],
            "legs": [{"hops": [{"pool_id": "pool"}]}],
            "recipient": "bob",
            "total_amount_in": 10,
            "total_min_amount_out": 1,
            "total_amount_out": 2,
            "total_max_amount_in": 20
        });
        match kind {
            "ROUTE_EXACT_IN" => {
                value.as_object_mut().unwrap().remove("total_amount_out");
                value.as_object_mut().unwrap().remove("total_max_amount_in");
            }
            "ROUTE_EXACT_OUT" => {
                value.as_object_mut().unwrap().remove("total_amount_in");
                value
                    .as_object_mut()
                    .unwrap()
                    .remove("total_min_amount_out");
            }
            _ => {}
        }
        value
    }

    fn swap_exact_out_intent_json() -> Value {
        json!({
            "module": "TauSwap",
            "version": "v1",
            "kind": "SWAP_EXACT_OUT",
            "intent_id": "swap-exact-out-bdd",
            "sender_pubkey": "alice",
            "deadline": 100,
            "pool_id": "pool",
            "asset_in": "A",
            "asset_out": "B",
            "amount_out": 2,
            "max_amount_in": 20,
            "recipient": "bob"
        })
    }

    fn create_pool_intent_json() -> Value {
        json!({
            "module": "TauSwap",
            "version": "v1",
            "kind": "CREATE_POOL",
            "intent_id": "create-pool-bdd",
            "sender_pubkey": "alice",
            "deadline": 100,
            "asset0": "A",
            "asset1": "B",
            "fee_bps": 30,
            "amount0": 10,
            "amount1": 20
        })
    }

    fn swap_exact_in_intent_json() -> Value {
        json!({
            "module": "TauSwap",
            "version": "v1",
            "kind": "SWAP_EXACT_IN",
            "intent_id": "swap-exact-in-bdd",
            "sender_pubkey": "alice",
            "deadline": 100,
            "pool_id": "pool",
            "asset_in": "A",
            "asset_out": "B",
            "amount_in": 10,
            "min_amount_out": 1,
            "recipient": "bob"
        })
    }

    fn add_liquidity_intent_json() -> Value {
        json!({
            "module": "TauSwap",
            "version": "v1",
            "kind": "ADD_LIQUIDITY",
            "intent_id": "add-liquidity-bdd",
            "sender_pubkey": "alice",
            "deadline": 100,
            "pool_id": "pool",
            "amount0_desired": 10,
            "amount1_desired": 20,
            "amount0_min": 1,
            "amount1_min": 2,
            "recipient": "bob"
        })
    }

    fn remove_liquidity_intent_json() -> Value {
        json!({
            "module": "TauSwap",
            "version": "v1",
            "kind": "REMOVE_LIQUIDITY",
            "intent_id": "remove-liquidity-bdd",
            "sender_pubkey": "alice",
            "deadline": 100,
            "pool_id": "pool",
            "lp_amount": 10,
            "amount0_min": 1,
            "amount1_min": 2,
            "recipient": "bob"
        })
    }

    #[test]
    fn strict_surface_bindings_accept_matching_context() {
        let req = strict_req();
        let proof = strict_proof_meta();
        verify_surface_request_bindings(&req, &proof, strict_binding_expectations("devnet"))
            .unwrap();
    }

    #[test]
    fn strict_surface_bindings_reject_wrong_chain_and_operation() {
        let req = strict_req();
        let proof = strict_proof_meta();
        let err = verify_surface_request_bindings(
            &req,
            &proof,
            strict_binding_expectations("other-chain"),
        )
        .unwrap_err();
        assert_eq!(err, "chain_id mismatch");

        let mut bad_req = strict_req();
        bad_req["context"]["operation_hash"] = Value::String(hx(9));
        let err = verify_surface_request_bindings(
            &bad_req,
            &proof,
            strict_binding_expectations("devnet"),
        )
        .unwrap_err();
        assert_eq!(err, "context.operation_hash mismatch");
    }

    #[test]
    fn strict_surface_bindings_reject_wrong_post_hash_and_image_id() {
        let mut req = strict_req();
        req["tau_state"]["app_hash"] = Value::String(hx(8));
        let proof = strict_proof_meta();
        let err =
            verify_surface_request_bindings(&req, &proof, strict_binding_expectations("devnet"))
                .unwrap_err();
        assert_eq!(err, "post_app_hash mismatch");

        let mut bad_image = strict_proof_meta();
        bad_image["meta"]["risc0_image_id"] = Value::String(hx(9));
        let err = check_proof_meta_image_id(&bad_image).unwrap_err();
        assert_eq!(err, "risc0_image_id mismatch");
    }

    #[test]
    fn spot_fee_bindings_accept_matching_meta_and_context() {
        let proof = spot_proof_meta(2500, Value::String("0xfee".to_string()));
        let req = json!({
            "context": {
                "protocol_fee_share_bps": 2500,
                "protocol_fee_recipient_pubkey": "0xfee"
            }
        });
        let journal = spot_fee_journal(2500, Some("0xfee"));

        check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap();
    }

    #[test]
    fn route_price_intervals_context_accepts_valid_values() {
        let context = json!({
            "route_price_intervals": [
                {"asset": "ASSET0", "low_e8": 1, "point_e8": 2, "high_e8": 3}
            ]
        });
        let obj = context.as_object().unwrap();

        let intervals = parse_route_price_intervals_context(obj).unwrap();

        assert_eq!(intervals.len(), 1);
        assert_ne!(
            route_price_intervals_root_v1(&intervals).unwrap(),
            route_price_intervals_root_v1(&[]).unwrap()
        );
    }

    #[test]
    fn route_price_interval_authority_context_accepts_valid_values() {
        let interval_root = h(3);
        let authority = route_interval_authority_for_root(interval_root);
        let context = json!({
            "route_price_interval_authority": route_interval_authority_json(&authority)
        });
        let obj = context.as_object().unwrap();

        let parsed = parse_route_price_interval_authority_context(obj).unwrap();

        assert_eq!(parsed, Some(authority));
    }

    #[test]
    fn route_price_interval_authority_policy_context_accepts_valid_values() {
        let interval_root = h(3);
        let authority = route_interval_authority_for_root(interval_root);
        let policy = route_interval_authority_policy_for(&authority);
        let context = json!({
            "route_price_interval_authority_policy": route_interval_authority_policy_json(&policy)
        });
        let obj = context.as_object().unwrap();

        let parsed = parse_route_price_interval_authority_policy_context(obj).unwrap();

        assert_eq!(parsed, Some(policy));
    }

    #[test]
    fn route_price_interval_max_width_context_accepts_string_or_number() {
        let numeric_context = json!({"route_price_interval_max_width_bps": 200});
        assert_eq!(
            parse_route_price_interval_max_width_bps_context(numeric_context.as_object().unwrap())
                .unwrap(),
            Some(200)
        );

        let string_context = json!({"route_price_interval_max_width_bps": "201"});
        assert_eq!(
            parse_route_price_interval_max_width_bps_context(string_context.as_object().unwrap())
                .unwrap(),
            Some(201)
        );
    }

    #[test]
    fn route_price_interval_max_width_context_rejects_over_u64() {
        let context = json!({"route_price_interval_max_width_bps": "18446744073709551616"});

        assert_eq!(
            parse_route_price_interval_max_width_bps_context(context.as_object().unwrap())
                .unwrap_err(),
            "context.route_price_interval_max_width_bps must be a u64"
        );
    }

    #[test]
    fn route_price_intervals_context_rejects_non_list() {
        let context = json!({"route_price_intervals": {}});
        let obj = context.as_object().unwrap();

        assert_eq!(
            parse_route_price_intervals_context(obj).unwrap_err(),
            "context.route_price_intervals must be a list"
        );
    }

    #[test]
    fn spot_route_price_interval_bindings_accept_matching_meta_and_context() {
        let intervals = vec![RoutePriceIntervalV1 {
            asset: "ASSET0".to_string(),
            low_e8: 1,
            point_e8: 2,
            high_e8: 3,
        }];
        let interval_root = route_price_intervals_root_v1(&intervals).unwrap();
        let authority = route_interval_authority_for_root(interval_root);
        let authority_root = route_price_interval_authority_root_v1(Some(&authority)).unwrap();
        let policy = route_interval_authority_policy_for(&authority);
        let policy_root = route_price_interval_authority_policy_root_v1(Some(&policy)).unwrap();
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_count"] = Value::from(1);
        proof["meta"]["route_price_intervals_root"] = Value::String(hex_lower(&interval_root));
        proof["meta"]["route_price_interval_authority_root"] =
            Value::String(hex_lower(&authority_root));
        proof["meta"]["route_price_interval_authority_policy_root"] =
            Value::String(hex_lower(&policy_root));
        proof["meta"]["route_price_interval_max_width_bps"] = Value::from(10_000);
        let req = json!({
            "trusted_route_price_interval_authority_policy_root": hex_lower(&policy_root),
            "context": {
                "route_price_interval_max_width_bps": 10000,
                "route_price_intervals": [
                    {"asset": "ASSET0", "low_e8": 1, "point_e8": 2, "high_e8": 3}
                ],
                "route_price_interval_authority": route_interval_authority_json(&authority),
                "route_price_interval_authority_policy": route_interval_authority_policy_json(&policy)
            }
        });
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_count = 1;
        journal.route_price_intervals_root = interval_root;
        journal.route_price_interval_authority_root = authority_root;
        journal.route_price_interval_authority_policy_root = policy_root;
        journal.route_price_interval_max_width_bps = Some(10_000);

        check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap();
    }

    #[test]
    fn spot_route_price_interval_bindings_reject_meta_max_width_mismatch() {
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_max_width_bps"] = Value::from(200);
        let req = json!({});
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_max_width_bps = Some(100);

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "proof.meta.route_price_interval_max_width_bps mismatch"
        );
    }

    #[test]
    fn spot_route_price_interval_bindings_reject_context_max_width_mismatch() {
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_max_width_bps"] = Value::from(100);
        let req = json!({
            "context": {
                "route_price_interval_max_width_bps": 200
            }
        });
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_max_width_bps = Some(100);

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "context.route_price_interval_max_width_bps mismatch"
        );
    }

    #[test]
    fn spot_route_price_interval_bindings_reject_tampered_meta_root() {
        let intervals = vec![RoutePriceIntervalV1 {
            asset: "ASSET0".to_string(),
            low_e8: 1,
            point_e8: 2,
            high_e8: 3,
        }];
        let authority =
            route_interval_authority_for_root(route_price_intervals_root_v1(&intervals).unwrap());
        let policy = route_interval_authority_policy_for(&authority);
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_count"] = Value::from(1);
        proof["meta"]["route_price_intervals_root"] = Value::String(hx(9));
        let req = json!({});
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_count = 1;
        journal.route_price_intervals_root = route_price_intervals_root_v1(&intervals).unwrap();
        journal.route_price_interval_authority_root =
            route_price_interval_authority_root_v1(Some(&authority)).unwrap();
        journal.route_price_interval_authority_policy_root =
            route_price_interval_authority_policy_root_v1(Some(&policy)).unwrap();

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "proof.meta.route_price_intervals_root mismatch"
        );
    }

    #[test]
    fn spot_route_price_interval_bindings_reject_missing_authority_meta_root() {
        let intervals = vec![RoutePriceIntervalV1 {
            asset: "ASSET0".to_string(),
            low_e8: 1,
            point_e8: 2,
            high_e8: 3,
        }];
        let interval_root = route_price_intervals_root_v1(&intervals).unwrap();
        let authority = route_interval_authority_for_root(interval_root);
        let authority_root = route_price_interval_authority_root_v1(Some(&authority)).unwrap();
        let policy = route_interval_authority_policy_for(&authority);
        let policy_root = route_price_interval_authority_policy_root_v1(Some(&policy)).unwrap();
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_count"] = Value::from(1);
        proof["meta"]["route_price_intervals_root"] = Value::String(hex_lower(&interval_root));
        proof["meta"]["route_price_interval_authority_policy_root"] =
            Value::String(hex_lower(&policy_root));
        proof["meta"]
            .as_object_mut()
            .unwrap()
            .remove("route_price_interval_authority_root");
        let req = json!({});
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_count = 1;
        journal.route_price_intervals_root = interval_root;
        journal.route_price_interval_authority_root = authority_root;
        journal.route_price_interval_authority_policy_root = policy_root;

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "proof.meta.route_price_interval_authority_root missing"
        );
    }

    #[test]
    fn spot_route_price_interval_bindings_reject_context_authority_root_mismatch() {
        let intervals = vec![RoutePriceIntervalV1 {
            asset: "ASSET0".to_string(),
            low_e8: 1,
            point_e8: 2,
            high_e8: 3,
        }];
        let interval_root = route_price_intervals_root_v1(&intervals).unwrap();
        let authority = route_interval_authority_for_root(interval_root);
        let authority_root = route_price_interval_authority_root_v1(Some(&authority)).unwrap();
        let policy = route_interval_authority_policy_for(&authority);
        let policy_root = route_price_interval_authority_policy_root_v1(Some(&policy)).unwrap();
        let mut wrong_authority = authority.clone();
        wrong_authority.source_root = h(8);
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_count"] = Value::from(1);
        proof["meta"]["route_price_intervals_root"] = Value::String(hex_lower(&interval_root));
        proof["meta"]["route_price_interval_authority_root"] =
            Value::String(hex_lower(&authority_root));
        proof["meta"]["route_price_interval_authority_policy_root"] =
            Value::String(hex_lower(&policy_root));
        let req = json!({
            "trusted_route_price_interval_authority_policy_root": hex_lower(&policy_root),
            "context": {
                "route_price_intervals": [
                    {"asset": "ASSET0", "low_e8": 1, "point_e8": 2, "high_e8": 3}
                ],
                "route_price_interval_authority": route_interval_authority_json(&wrong_authority),
                "route_price_interval_authority_policy": route_interval_authority_policy_json(&policy)
            }
        });
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_count = 1;
        journal.route_price_intervals_root = interval_root;
        journal.route_price_interval_authority_root = authority_root;
        journal.route_price_interval_authority_policy_root = policy_root;

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "context.route_price_interval_authority_root mismatch"
        );
    }

    #[test]
    fn spot_route_price_interval_bindings_reject_missing_trusted_policy_root() {
        let intervals = vec![RoutePriceIntervalV1 {
            asset: "ASSET0".to_string(),
            low_e8: 1,
            point_e8: 2,
            high_e8: 3,
        }];
        let interval_root = route_price_intervals_root_v1(&intervals).unwrap();
        let authority = route_interval_authority_for_root(interval_root);
        let authority_root = route_price_interval_authority_root_v1(Some(&authority)).unwrap();
        let policy = route_interval_authority_policy_for(&authority);
        let policy_root = route_price_interval_authority_policy_root_v1(Some(&policy)).unwrap();
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_count"] = Value::from(1);
        proof["meta"]["route_price_intervals_root"] = Value::String(hex_lower(&interval_root));
        proof["meta"]["route_price_interval_authority_root"] =
            Value::String(hex_lower(&authority_root));
        proof["meta"]["route_price_interval_authority_policy_root"] =
            Value::String(hex_lower(&policy_root));
        let req = json!({
            "context": {
                "route_price_intervals": [
                    {"asset": "ASSET0", "low_e8": 1, "point_e8": 2, "high_e8": 3}
                ],
                "route_price_interval_authority": route_interval_authority_json(&authority),
                "route_price_interval_authority_policy": route_interval_authority_policy_json(&policy)
            }
        });
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_count = 1;
        journal.route_price_intervals_root = interval_root;
        journal.route_price_interval_authority_root = authority_root;
        journal.route_price_interval_authority_policy_root = policy_root;

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "trusted_route_price_interval_authority_policy_root required"
        );
    }

    #[test]
    fn spot_route_price_interval_bindings_reject_self_selected_expected_policy_root() {
        let intervals = vec![RoutePriceIntervalV1 {
            asset: "ASSET0".to_string(),
            low_e8: 1,
            point_e8: 2,
            high_e8: 3,
        }];
        let interval_root = route_price_intervals_root_v1(&intervals).unwrap();
        let authority = route_interval_authority_for_root(interval_root);
        let authority_root = route_price_interval_authority_root_v1(Some(&authority)).unwrap();
        let policy = route_interval_authority_policy_for(&authority);
        let policy_root = route_price_interval_authority_policy_root_v1(Some(&policy)).unwrap();
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_count"] = Value::from(1);
        proof["meta"]["route_price_intervals_root"] = Value::String(hex_lower(&interval_root));
        proof["meta"]["route_price_interval_authority_root"] =
            Value::String(hex_lower(&authority_root));
        proof["meta"]["route_price_interval_authority_policy_root"] =
            Value::String(hex_lower(&policy_root));
        let req = json!({
            "expected_route_price_interval_authority_policy_root": hex_lower(&policy_root),
            "context": {
                "route_price_intervals": [
                    {"asset": "ASSET0", "low_e8": 1, "point_e8": 2, "high_e8": 3}
                ],
                "route_price_interval_authority": route_interval_authority_json(&authority),
                "route_price_interval_authority_policy": route_interval_authority_policy_json(&policy)
            }
        });
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_count = 1;
        journal.route_price_intervals_root = interval_root;
        journal.route_price_interval_authority_root = authority_root;
        journal.route_price_interval_authority_policy_root = policy_root;

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "trusted_route_price_interval_authority_policy_root required"
        );
    }

    #[test]
    fn spot_route_price_interval_bindings_reject_context_policy_root_mismatch() {
        let intervals = vec![RoutePriceIntervalV1 {
            asset: "ASSET0".to_string(),
            low_e8: 1,
            point_e8: 2,
            high_e8: 3,
        }];
        let interval_root = route_price_intervals_root_v1(&intervals).unwrap();
        let authority = route_interval_authority_for_root(interval_root);
        let authority_root = route_price_interval_authority_root_v1(Some(&authority)).unwrap();
        let policy = route_interval_authority_policy_for(&authority);
        let policy_root = route_price_interval_authority_policy_root_v1(Some(&policy)).unwrap();
        let mut wrong_policy = policy.clone();
        wrong_policy.sources[0].verification_root = h(9);
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["route_price_interval_count"] = Value::from(1);
        proof["meta"]["route_price_intervals_root"] = Value::String(hex_lower(&interval_root));
        proof["meta"]["route_price_interval_authority_root"] =
            Value::String(hex_lower(&authority_root));
        proof["meta"]["route_price_interval_authority_policy_root"] =
            Value::String(hex_lower(&policy_root));
        let req = json!({
            "trusted_route_price_interval_authority_policy_root": hex_lower(&policy_root),
            "context": {
                "route_price_intervals": [
                    {"asset": "ASSET0", "low_e8": 1, "point_e8": 2, "high_e8": 3}
                ],
                "route_price_interval_authority": route_interval_authority_json(&authority),
                "route_price_interval_authority_policy": route_interval_authority_policy_json(&wrong_policy)
            }
        });
        let mut journal = spot_fee_journal(0, None);
        journal.route_price_interval_count = 1;
        journal.route_price_intervals_root = interval_root;
        journal.route_price_interval_authority_root = authority_root;
        journal.route_price_interval_authority_policy_root = policy_root;

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "context.route_price_interval_authority_policy_root mismatch"
        );
    }

    #[test]
    fn spot_fee_bindings_reject_tampered_meta_share() {
        let proof = spot_proof_meta(1000, Value::String("0xfee".to_string()));
        let req = json!({});
        let journal = spot_fee_journal(2500, Some("0xfee"));

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "proof.meta.protocol_fee_share_bps mismatch"
        );
    }

    #[test]
    fn spot_fee_bindings_reject_tampered_context_recipient() {
        let proof = spot_proof_meta(2500, Value::String("0xfee".to_string()));
        let req = json!({
            "context": {
                "protocol_fee_share_bps": 2500,
                "protocol_fee_recipient_pubkey": "0xother"
            }
        });
        let journal = spot_fee_journal(2500, Some("0xfee"));

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "context.protocol_fee_recipient_pubkey mismatch"
        );
    }

    #[test]
    fn spot_fee_bindings_accept_legacy_missing_meta_fee_fields_for_zero_fee() {
        let proof = json!({"meta": {}});
        let req = json!({});
        let journal = spot_fee_journal(0, None);

        check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap();
    }

    #[test]
    fn spot_fee_bindings_reject_missing_meta_fee_fields_for_nonzero_journal() {
        let proof = json!({"meta": {}});
        let req = json!({});
        let journal = spot_fee_journal(2500, Some("0xfee"));

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "proof.meta.protocol_fee_share_bps mismatch"
        );
    }

    #[test]
    fn frontier_signature_cert_context_accepts_minimal_fixture() {
        let context = json!({
            "shared_pool_frontier_signature_certificates": [
                frontier_signature_certificate_json()
            ]
        });
        let obj = context.as_object().unwrap();

        let certificates = parse_frontier_signature_certificates_context(obj).unwrap();

        assert_eq!(certificates.len(), 1);
        assert_ne!(
            frontier_signature_certificates_root_v1(&certificates).unwrap(),
            frontier_signature_certificates_root_v1(&[]).unwrap()
        );
    }

    #[test]
    fn frontier_signature_cert_context_rejects_non_list() {
        let context = json!({
            "shared_pool_frontier_signature_certificates": {}
        });
        let obj = context.as_object().unwrap();

        assert_eq!(
            parse_frontier_signature_certificates_context(obj).unwrap_err(),
            "context.shared_pool_frontier_signature_certificates must be a list"
        );
    }

    #[test]
    fn spot_frontier_bindings_reject_missing_meta_fields_for_nonempty_journal() {
        let proof = json!({
            "meta": {
                "protocol_fee_share_bps": 0,
                "protocol_fee_recipient_pubkey": null
            }
        });
        let req = json!({});
        let mut journal = spot_fee_journal(0, None);
        journal.shared_pool_frontier_signature_certificate_count = 1;
        journal.shared_pool_frontier_signature_certificates_root = h(9);

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "proof.meta.shared_pool_frontier_signature_certificate_count missing/invalid"
        );
    }

    #[test]
    fn spot_frontier_bindings_reject_tampered_meta_root() {
        let mut proof = spot_proof_meta(0, Value::Null);
        proof["meta"]["shared_pool_frontier_signature_certificate_count"] = Value::from(1);
        proof["meta"]["shared_pool_frontier_signature_certificates_root"] = Value::String(hx(8));
        let req = json!({});
        let mut journal = spot_fee_journal(0, None);
        journal.shared_pool_frontier_signature_certificate_count = 1;
        journal.shared_pool_frontier_signature_certificates_root = h(9);

        assert_eq!(
            check_spot_protocol_fee_bindings(&req, &proof, &journal).unwrap_err(),
            "proof.meta.shared_pool_frontier_signature_certificates_root mismatch"
        );
    }

    #[test]
    fn route_parser_accepts_required_totals_for_both_kinds() {
        let exact_in =
            parse_intent_obj(route_intent_json("ROUTE_EXACT_IN").as_object().unwrap()).unwrap();
        match exact_in {
            tau_state_proof_risc0_shared::DexIntentV1::Route(route) => {
                assert_eq!(route.kind, "ROUTE_EXACT_IN");
                assert_eq!(route.total_amount_in, 10);
                assert_eq!(route.total_min_amount_out, 1);
                assert_eq!(route.total_amount_out, 0);
                assert_eq!(route.total_max_amount_in, 0);
            }
            _ => panic!("expected route intent"),
        }

        let exact_out =
            parse_intent_obj(route_intent_json("ROUTE_EXACT_OUT").as_object().unwrap()).unwrap();
        match exact_out {
            tau_state_proof_risc0_shared::DexIntentV1::Route(route) => {
                assert_eq!(route.kind, "ROUTE_EXACT_OUT");
                assert_eq!(route.total_amount_in, 0);
                assert_eq!(route.total_min_amount_out, 0);
                assert_eq!(route.total_amount_out, 2);
                assert_eq!(route.total_max_amount_in, 20);
            }
            _ => panic!("expected route intent"),
        }
    }

    #[test]
    fn create_pool_fee_bps_is_checked_before_u32_conversion() {
        let mut exact_max = create_pool_intent_json();
        exact_max["fee_bps"] = Value::from(u32::MAX);
        let parsed = parse_intent_obj(exact_max.as_object().unwrap()).unwrap();
        match parsed {
            tau_state_proof_risc0_shared::DexIntentV1::CreatePool(intent) => {
                assert_eq!(intent.fee_bps, u32::MAX);
            }
            _ => panic!("expected create-pool intent"),
        }

        let mut overflow = create_pool_intent_json();
        overflow["fee_bps"] = Value::from(u64::from(u32::MAX) + 1);
        assert_eq!(
            parse_intent_obj(overflow.as_object().unwrap()).unwrap_err(),
            "intent.fee_bps must fit in a u32"
        );

        let mut alias = create_pool_intent_json();
        alias["fee_bps"] = Value::from((1u64 << 32) + 30);
        assert_eq!(
            parse_intent_obj(alias.as_object().unwrap()).unwrap_err(),
            "intent.fee_bps must fit in a u32"
        );

        for invalid in [json!(-1), json!(1.5)] {
            let mut intent = create_pool_intent_json();
            intent["fee_bps"] = invalid;
            assert_eq!(
                parse_intent_obj(intent.as_object().unwrap()).unwrap_err(),
                "intent.fee_bps missing or invalid"
            );
        }
    }

    #[test]
    fn swap_exact_out_parser_accepts_string_encoded_u128_amounts() {
        let mut v = swap_exact_out_intent_json();
        let amount_out = (u64::MAX as u128) + 1;
        let max_amount_in = amount_out + 9;
        v["amount_out"] = Value::String(amount_out.to_string());
        v["max_amount_in"] = Value::String(max_amount_in.to_string());

        let intent = parse_intent_obj(v.as_object().unwrap()).unwrap();
        match intent {
            tau_state_proof_risc0_shared::DexIntentV1::SwapExactOut(swap) => {
                assert_eq!(swap.amount_out, amount_out);
                assert_eq!(swap.max_amount_in, max_amount_in);
            }
            _ => panic!("expected exact-out intent"),
        }
    }

    #[test]
    fn route_parser_rejects_malformed_total_min_amount_out() {
        let mut v = route_intent_json("ROUTE_EXACT_IN");
        v["total_min_amount_out"] = Value::String("not-a-number".to_string());

        assert_eq!(
            parse_intent_obj(v.as_object().unwrap()).unwrap_err(),
            "total_min_amount_out must be a u128"
        );
    }

    #[test]
    fn route_parser_rejects_missing_required_exact_out_total_max() {
        let mut v = route_intent_json("ROUTE_EXACT_OUT");
        v.as_object_mut().unwrap().remove("total_max_amount_in");

        assert_eq!(
            parse_intent_obj(v.as_object().unwrap()).unwrap_err(),
            "total_max_amount_in missing"
        );
    }

    #[test]
    fn route_parser_rejects_ambiguous_unused_totals() {
        let mut exact_in = route_intent_json("ROUTE_EXACT_IN");
        exact_in["total_amount_out"] = Value::String("2".to_string());
        assert_eq!(
            parse_intent_obj(exact_in.as_object().unwrap()).unwrap_err(),
            "total_amount_out must be absent or zero for ROUTE_EXACT_IN"
        );

        let mut exact_out = route_intent_json("ROUTE_EXACT_OUT");
        exact_out["total_amount_in"] = Value::String("10".to_string());
        assert_eq!(
            parse_intent_obj(exact_out.as_object().unwrap()).unwrap_err(),
            "total_amount_in must be absent or zero for ROUTE_EXACT_OUT"
        );
    }

    #[test]
    fn route_parser_rejects_zero_required_totals() {
        let mut exact_in = route_intent_json("ROUTE_EXACT_IN");
        exact_in["total_amount_in"] = Value::from(0);
        assert_eq!(
            parse_intent_obj(exact_in.as_object().unwrap()).unwrap_err(),
            "total_amount_in must be positive"
        );

        let mut exact_out = route_intent_json("ROUTE_EXACT_OUT");
        exact_out["total_amount_out"] = Value::from(0);
        assert_eq!(
            parse_intent_obj(exact_out.as_object().unwrap()).unwrap_err(),
            "total_amount_out must be positive"
        );

        let mut exact_out_max = route_intent_json("ROUTE_EXACT_OUT");
        exact_out_max["total_max_amount_in"] = Value::from(0);
        assert_eq!(
            parse_intent_obj(exact_out_max.as_object().unwrap()).unwrap_err(),
            "total_max_amount_in must be positive"
        );
    }

    #[test]
    fn block_parser_prefers_tx_sender_pubkey_and_rejects_alias_split() {
        let txs = json!([
            {
                "tx_sender_pubkey": "canonical-sender",
                "operations": {}
            },
            {
                "sender_pubkey": "legacy-sender",
                "tx_sender_pubkey": "legacy-sender",
                "operations": {}
            }
        ]);

        let parsed = parse_block_txs(Some(&txs)).unwrap();

        assert_eq!(parsed[0].sender_pubkey, "canonical-sender");
        assert_eq!(parsed[1].sender_pubkey, "legacy-sender");

        let bad = json!([
            {
                "sender_pubkey": "alias",
                "tx_sender_pubkey": "canonical-sender",
                "operations": {}
            }
        ]);
        assert_eq!(
            parse_block_txs(Some(&bad)).unwrap_err(),
            "tx.sender_pubkey must match tx_sender_pubkey"
        );
    }

    #[test]
    fn ingress_parser_uses_same_tx_sender_identity_rule() {
        let txs = json!([
            {
                "tx_sender_pubkey": "canonical-sender",
                "nonce": 7,
                "operations": {}
            }
        ]);

        let parsed = parse_block_ingress_facts(Some(&txs)).unwrap();

        assert_eq!(parsed[0].sender_pubkey, "canonical-sender");
        assert_eq!(parsed[0].nonce, 7);

        let bad = json!([
            {
                "sender_pubkey": "alias",
                "tx_sender_pubkey": "canonical-sender",
                "nonce": 7,
                "operations": {}
            }
        ]);
        assert_eq!(
            parse_block_ingress_facts(Some(&bad)).unwrap_err(),
            "tx.sender_pubkey must match tx_sender_pubkey"
        );
    }

    #[test]
    fn block_parser_accepts_projected_route_body_shape() {
        let mut route = route_intent_json("ROUTE_EXACT_IN");
        route["sender_pubkey"] = Value::String("route-sender".to_string());
        route["quote_receipt"] = json!({
            "body": {
                "schema": "zenodex/route_quote_receipt/v1",
                "kind": "exact_in",
                "asset_in": "A",
                "asset_out": "B",
                "amount_in": 10,
                "amount_out": 2,
                "legs": [
                    {
                        "amount_in": 10,
                        "amount_out": 2,
                        "hops": [
                            {
                                "pool_id": "pool",
                                "asset_in": "A",
                                "asset_out": "B",
                                "amount_in": 10,
                                "amount_out": 2
                            }
                        ]
                    }
                ],
                "pools": {"pool": "fingerprint"}
            },
            "receipt_hash": "0x2222222222222222222222222222222222222222222222222222222222222222",
            "risc0_route_quote_receipt_binding_hash": "0x1111111111111111111111111111111111111111111111111111111111111111"
        });
        let txs = json!([
            {
                "tx_sender_pubkey": "route-sender",
                "sender_pubkey": "route-sender",
                "nonce": 7,
                "operations": {"2": [route]}
            }
        ]);

        let parsed = parse_block_txs(Some(&txs)).unwrap();

        assert_eq!(parsed[0].sender_pubkey, "route-sender");
        assert_eq!(parsed[0].app_ops.intents.len(), 1);
        match &parsed[0].app_ops.intents[0].intent {
            tau_state_proof_risc0_shared::DexIntentV1::Route(route) => {
                assert_eq!(route.sender_pubkey, "route-sender");
                assert_eq!(route.kind, "ROUTE_EXACT_IN");
                assert_eq!(route.quote_receipt_hash, format!("0x{}", hx(0x11)));
                assert_eq!(route.total_amount_in, 10);
                assert_eq!(route.total_min_amount_out, 1);
                assert_eq!(route.total_amount_out, 0);
                assert_eq!(route.total_max_amount_in, 0);
            }
            _ => panic!("expected route intent"),
        }
    }

    #[test]
    fn txs_commitment_command_uses_rust_block_parser() {
        let mut route = route_intent_json("ROUTE_EXACT_IN");
        route["sender_pubkey"] = Value::String("route-sender".to_string());
        let txs = json!([
            {
                "tx_sender_pubkey": "route-sender",
                "sender_pubkey": "route-sender",
                "nonce": 7,
                "operations": {"2": [route]}
            }
        ]);
        let req = json!({
            "schema": "tau_state_proof_txs_commitment",
            "schema_version": 1,
            "transactions": txs
        });

        let out = txs_commitment_response(&req).unwrap();
        let parsed = parse_block_txs(req.get("transactions")).unwrap();

        assert_eq!(out["schema"], "tau_state_proof_txs_commitment_result");
        assert_eq!(out["schema_version"], 1);
        assert_eq!(out["ok"], true);
        assert_eq!(out["tx_count"], 1);
        assert_eq!(
            out["txs_commitment"],
            Value::String(hex_lower(&txs_commitment_v1(&parsed)))
        );
    }

    #[test]
    fn txs_commitment_command_rejects_sender_alias_split() {
        let req = json!({
            "schema": "tau_state_proof_txs_commitment",
            "schema_version": 1,
            "transactions": [
                {
                    "tx_sender_pubkey": "tx-sender",
                    "operations": {"2": [[swap_exact_in_intent_json(), "0xsig"]]}
                }
            ]
        });

        assert_eq!(
            txs_commitment_response(&req).unwrap_err(),
            "intent.sender_pubkey must match tx.sender_pubkey"
        );
    }

    #[test]
    fn block_parser_rejects_intent_sender_alias_split_for_all_intent_kinds() {
        for intent in [
            create_pool_intent_json(),
            swap_exact_in_intent_json(),
            add_liquidity_intent_json(),
            remove_liquidity_intent_json(),
            swap_exact_out_intent_json(),
            route_intent_json("ROUTE_EXACT_IN"),
            route_intent_json("ROUTE_EXACT_OUT"),
        ] {
            let kind = intent
                .get("kind")
                .and_then(Value::as_str)
                .unwrap_or("missing-kind");
            let txs = json!([
                {
                    "tx_sender_pubkey": "tx-sender",
                    "operations": {"2": [intent]}
                }
            ]);

            assert_eq!(
                parse_block_txs(Some(&txs)).unwrap_err(),
                "intent.sender_pubkey must match tx.sender_pubkey",
                "kind={kind}"
            );
        }
    }

    #[test]
    fn block_parser_rejects_signed_pair_intent_sender_alias_split() {
        let txs = json!([
            {
                "tx_sender_pubkey": "tx-sender",
                "operations": {"2": [[swap_exact_in_intent_json(), "0xsig"]]}
            }
        ]);

        assert_eq!(
            parse_block_txs(Some(&txs)).unwrap_err(),
            "intent.sender_pubkey must match tx.sender_pubkey"
        );
    }

    #[test]
    fn protocol_fee_context_defaults_when_absent() {
        let context = json!({});
        let obj = context.as_object().unwrap();
        assert_eq!(
            parse_protocol_fee_context(obj).unwrap(),
            ProtocolFeeFields {
                share_bps: 0,
                recipient_pubkey: None,
            }
        );
    }

    #[test]
    fn protocol_fee_context_accepts_valid_values() {
        let context = json!({
            "protocol_fee_share_bps": 2500,
            "protocol_fee_recipient_pubkey": "0xfee"
        });
        let obj = context.as_object().unwrap();
        assert_eq!(
            parse_protocol_fee_context(obj).unwrap(),
            ProtocolFeeFields {
                share_bps: 2500,
                recipient_pubkey: Some("0xfee".to_string()),
            }
        );
    }

    #[test]
    fn protocol_fee_context_rejects_non_numeric_share() {
        let context = json!({"protocol_fee_share_bps": "2500"});
        let obj = context.as_object().unwrap();
        assert_eq!(
            parse_protocol_fee_context(obj).unwrap_err(),
            "context.protocol_fee_share_bps must be a u32"
        );
    }

    #[test]
    fn protocol_fee_context_rejects_oversized_share() {
        let context = json!({"protocol_fee_share_bps": (u32::MAX as u64) + 1});
        let obj = context.as_object().unwrap();
        assert_eq!(
            parse_protocol_fee_context(obj).unwrap_err(),
            "context.protocol_fee_share_bps must be a u32"
        );
    }

    #[test]
    fn protocol_fee_context_rejects_share_above_bps_scale() {
        let context = json!({"protocol_fee_share_bps": 10001});
        let obj = context.as_object().unwrap();
        assert_eq!(
            parse_protocol_fee_context(obj).unwrap_err(),
            "context.protocol_fee_share_bps out of range"
        );
    }

    #[test]
    fn protocol_fee_context_rejects_non_string_recipient() {
        let context = json!({"protocol_fee_recipient_pubkey": 7});
        let obj = context.as_object().unwrap();
        assert_eq!(
            parse_protocol_fee_context(obj).unwrap_err(),
            "context.protocol_fee_recipient_pubkey must be a string"
        );
    }

    #[test]
    fn protocol_fee_context_rejects_positive_share_with_blank_recipient() {
        let context = json!({
            "protocol_fee_share_bps": 1,
            "protocol_fee_recipient_pubkey": "  "
        });
        let obj = context.as_object().unwrap();
        assert_eq!(
            parse_protocol_fee_context(obj).unwrap_err(),
            "context.protocol_fee_recipient_pubkey required when share_bps > 0"
        );
    }

    #[test]
    fn protocol_fee_meta_rejects_positive_share_with_null_recipient() {
        let meta = json!({
            "protocol_fee_share_bps": 1,
            "protocol_fee_recipient_pubkey": null
        });
        let obj = meta.as_object().unwrap();
        assert_eq!(
            parse_protocol_fee_meta(obj).unwrap_err(),
            "proof.meta.protocol_fee_recipient_pubkey required when share_bps > 0"
        );
    }
}
