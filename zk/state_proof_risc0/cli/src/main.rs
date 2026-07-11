use std::io::{Read, Write};

use base64::Engine;
use risc0_zkvm::{default_prover, ExecutorEnv, Receipt};
use serde::de::DeserializeOwned;
use serde_json::{json, Value};

use tau_state_proof_risc0_methods::{
    TAU_STATE_PROOF_RISC0_GUEST_ELF as TAU_STATE_PROOF_GUEST_ELF,
    TAU_STATE_PROOF_RISC0_GUEST_ID as TAU_STATE_PROOF_GUEST_ID,
};
use tau_state_proof_risc0_shared::{
    accepted_receipts_root_v1, ingress_commitment_v1, perps_np_collateral_bindings_hash_v1,
    perps_np_operation_hash_v1, perps_np_oracle_bindings_hash_v1, txs_commitment_v1,
    zusd_operation_hash_v1, zusd_operation_oracle_binding_hash_v1, ChainBalanceV1,
    CollateralBindingV1, DexSnapshotV1, DexStateV1, NonceEntryV1, NonceStateV1, OracleBindingV1,
    PerpsAccountV1, PerpsIntentV1, PerpsMarketParamsV1, PerpsNpActionV1, PerpsNpSnapshotV1,
    PerpsNpTransitionInputV1, PerpsNpTransitionJournalV1, StateProofInputV1, StateProofJournalV1,
    TauTxAppOpsV1, TauTxV1, TxIngressFactV1, ZenoProofInputV1, ZusdBalanceEntryV1, ZusdOperationV1,
    ZusdSnapshotV1, ZusdTransitionInputV1, ZusdTransitionJournalV1, ZusdVaultEntryV1,
    JOURNAL_VERSION, PROOF_TYPE, PROOF_TYPE_PERPS_NP, PROOF_TYPE_ZUSD,
};

fn main() {
    let mut stdin = String::new();
    if std::io::stdin().read_to_string(&mut stdin).is_err() {
        eprintln!("failed to read stdin");
        std::process::exit(2);
    }

    let req: Value = match serde_json::from_str(&stdin) {
        Ok(v) => v,
        Err(e) => {
            eprintln!("stdin must be valid JSON: {e}");
            std::process::exit(2);
        }
    };

    let schema = req.get("schema").and_then(Value::as_str).unwrap_or("");
    match schema {
        "tau_state_proof_request" => handle_generate(&req),
        "tau_state_proof_verify" => handle_verify(&req),
        _ => {
            eprintln!("unexpected schema");
            std::process::exit(2);
        }
    }
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
        _ => die("unsupported proof_type"),
    }
}

fn handle_generate_spot(req: &Value) {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        die("unexpected schema_version (expected tau_state_proof_request v1)");
    }

    validate_embedded_methods();

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

    let input = StateProofInputV1 {
        state_hash,
        block_timestamp,
        pre_app_hash_present,
        pre_app_hash,
        pre_state,
        txs,
        pre_nonces,
        tx_ingress,
        chain_balances_post,
        expected_post_app_hash,
    };

    let guest_input = ZenoProofInputV1::Spot(input);
    let (receipt, journal): (Receipt, StateProofJournalV1) = prove_guest_input(&guest_input);

    if journal.state_hash != state_hash {
        die("journal.state_hash mismatch");
    }

    let receipt_bytes = bincode::serialize(&receipt)
        .unwrap_or_else(|e| die(&format!("failed to serialize receipt: {e}")));
    let proof_b64 = base64::engine::general_purpose::STANDARD.encode(receipt_bytes);

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
        "meta": perps_np_meta(&journal),
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
        "meta": zusd_meta(&journal),
    });
    write_json_stdout(&out);
}

fn handle_verify(req: &Value) {
    let out = match try_verify(req) {
        Ok(()) => json!({ "ok": true }),
        Err(err) => json!({ "ok": false, "error": err }),
    };
    write_json_stdout(&out);
}

fn try_verify(req: &Value) -> Result<(), String> {
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
        return try_verify_perps_np(req, proof, expected_state_hash);
    }
    if proof_type == PROOF_TYPE_ZUSD {
        return try_verify_zusd(req, proof, expected_state_hash);
    }
    if proof_type != PROOF_TYPE {
        return Err("unsupported proof_type".into());
    }
    check_proof_meta_image_id(proof)?;

    let proof_b64 = proof
        .get("proof")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof.proof missing".to_string())?;
    let proof_bytes = base64::engine::general_purpose::STANDARD
        .decode(proof_b64)
        .map_err(|e| format!("invalid base64 proof: {e}"))?;

    let receipt: Receipt =
        bincode::deserialize(&proof_bytes).map_err(|e| format!("invalid receipt bytes: {e}"))?;

    receipt
        .verify(TAU_STATE_PROOF_GUEST_ID)
        .map_err(|e| format!("receipt verification failed: {e}"))?;

    let journal: StateProofJournalV1 = decode_postcard_journal(&receipt, "spot journal")?;

    if journal.state_hash != expected_state_hash {
        return Err("journal.state_hash mismatch".into());
    }
    verify_spot_meta_bindings(proof, &journal)?;

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

    Ok(())
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
        &journal.chain_id,
        journal.pre_app_hash_present,
        journal.pre_app_hash,
        journal.post_app_hash,
        journal.operation_hash,
        journal.state_delta_hash,
        journal.oracle_binding_hash,
        journal.participant_set_hash,
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
        &journal.chain_id,
        journal.pre_app_hash_present,
        journal.pre_app_hash,
        journal.post_app_hash,
        journal.operation_hash,
        journal.state_delta_hash,
        journal.oracle_binding_hash,
        journal.participant_set_hash,
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

fn verify_surface_request_bindings(
    req: &Value,
    proof: &Value,
    journal_chain_id: &str,
    pre_app_hash_present: bool,
    pre_app_hash: [u8; 32],
    post_app_hash: [u8; 32],
    operation_hash: [u8; 32],
    state_delta_hash: [u8; 32],
    oracle_binding_hash: [u8; 32],
    participant_set_hash: [u8; 32],
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
    if expected_chain != journal_chain_id {
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
    if expected_post != post_app_hash {
        return Err("post_app_hash mismatch".into());
    }
    let expected_pre_raw = context
        .get("app_hash_pre")
        .and_then(Value::as_str)
        .ok_or_else(|| "context.app_hash_pre missing".to_string())?;
    if expected_pre_raw.trim().is_empty() {
        if pre_app_hash_present {
            return Err("pre_app_hash present but expected empty".into());
        }
    } else {
        let expected_pre = parse_hex32(expected_pre_raw)?;
        if !pre_app_hash_present {
            return Err("pre_app_hash missing but expected present".into());
        }
        if expected_pre != pre_app_hash {
            return Err("pre_app_hash mismatch".into());
        }
    }
    expect_meta_hash(proof, "post_app_hash", post_app_hash)?;
    expect_meta_pre_hash(proof, pre_app_hash_present, pre_app_hash)?;
    expect_meta_hash(proof, "operation_hash", operation_hash)?;
    expect_meta_hash(proof, "state_delta_hash", state_delta_hash)?;
    expect_meta_hash(proof, "oracle_binding_hash", oracle_binding_hash)?;
    expect_meta_hash(proof, "participant_set_hash", participant_set_hash)?;
    expect_context_hash(context, "operation_hash", operation_hash)?;
    expect_context_hash(context, "state_delta_hash", state_delta_hash)?;
    expect_context_hash(context, "oracle_binding_hash", oracle_binding_hash)?;
    expect_context_hash(context, "participant_set_hash", participant_set_hash)?;
    Ok(())
}

fn validate_embedded_methods() {
    if TAU_STATE_PROOF_GUEST_ELF.is_empty() {
        die("Risc0 guest ELF is empty (methods not embedded). Install the Risc0 toolchain/target and rebuild.");
    }
    if TAU_STATE_PROOF_GUEST_ID.iter().all(|w| *w == 0) {
        die("Risc0 guest image ID is all-zero (methods not embedded). Install the Risc0 toolchain/target and rebuild.");
    }
}

fn prove_guest_input<T>(guest_input: &ZenoProofInputV1) -> (Receipt, T)
where
    T: DeserializeOwned,
{
    let input_bytes = postcard::to_allocvec(guest_input)
        .unwrap_or_else(|e| die(&format!("failed to encode postcard input: {e}")));
    let input_len: u32 = input_bytes
        .len()
        .try_into()
        .unwrap_or_else(|_| die("guest input too large"));
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]).write_slice(&input_bytes);
    let env = builder
        .build()
        .unwrap_or_else(|e| die(&format!("failed to build env: {e}")));

    let prover = default_prover();
    let prove_info = prover
        .prove(env, TAU_STATE_PROOF_GUEST_ELF)
        .unwrap_or_else(|e| die(&format!("proving failed: {e}")));
    let receipt = prove_info.receipt;
    receipt
        .verify(TAU_STATE_PROOF_GUEST_ID)
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

fn encode_receipt(receipt: &Receipt) -> String {
    let receipt_bytes = bincode::serialize(receipt)
        .unwrap_or_else(|e| die(&format!("failed to serialize receipt: {e}")));
    base64::engine::general_purpose::STANDARD.encode(receipt_bytes)
}

fn decode_verified_receipt_from_proof(proof: &Value) -> Result<Receipt, String> {
    let proof_b64 = proof
        .get("proof")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof.proof missing".to_string())?;
    let proof_bytes = base64::engine::general_purpose::STANDARD
        .decode(proof_b64)
        .map_err(|e| format!("invalid base64 proof: {e}"))?;
    let receipt: Receipt =
        bincode::deserialize(&proof_bytes).map_err(|e| format!("invalid receipt bytes: {e}"))?;
    receipt
        .verify(TAU_STATE_PROOF_GUEST_ID)
        .map_err(|e| format!("receipt verification failed: {e}"))?;
    Ok(receipt)
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
        let parsed: Value = serde_json::from_str(s)
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
        let parsed: Value = serde_json::from_str(s)
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

fn check_proof_meta_image_id(proof: &Value) -> Result<(), String> {
    let meta = proof_meta_obj(proof)?;
    let image_id = meta
        .get("risc0_image_id")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof.meta.risc0_image_id missing".to_string())?;
    let expected = hex_u32_words(TAU_STATE_PROOF_GUEST_ID);
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

fn strict_context_obj(req: &Value) -> Result<&serde_json::Map<String, Value>, String> {
    req.get("context")
        .and_then(Value::as_object)
        .ok_or_else(|| "context must be an object for strict surface verification".to_string())
}

/// DbC invariant: proposer-controlled spot proof metadata must match the
/// verified receipt journal before the adapter can bind it into header metadata.
fn verify_spot_meta_bindings(proof: &Value, journal: &StateProofJournalV1) -> Result<(), String> {
    expect_meta_hash(proof, "txs_commitment", journal.txs_commitment)?;
    expect_meta_hash(proof, "ingress_commitment", journal.ingress_commitment)?;
    expect_meta_hash(proof, "pre_nonce_root", journal.pre_nonce_root)?;
    expect_meta_hash(proof, "post_nonce_root", journal.post_nonce_root)?;
    expect_meta_hash(
        proof,
        "accepted_receipts_root",
        journal.accepted_receipts_root,
    )?;
    expect_meta_pre_hash(proof, journal.pre_app_hash_present, journal.pre_app_hash)?;
    expect_meta_hash(proof, "post_app_hash", journal.post_app_hash)?;
    Ok(())
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
    let v: Value = serde_json::from_str(app_state_json)
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
        let sender = tx_obj
            .get("sender_pubkey")
            .and_then(Value::as_str)
            .ok_or_else(|| "tx.sender_pubkey missing".to_string())?
            .to_string();
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
    let txs = v
        .and_then(Value::as_array)
        .ok_or_else(|| "block.transactions must be a list".to_string())?;
    let mut out = Vec::with_capacity(txs.len());
    for tx in txs {
        let tx_obj = tx
            .as_object()
            .ok_or_else(|| "tx must be an object".to_string())?;
        let sender = tx_obj
            .get("sender_pubkey")
            .and_then(Value::as_str)
            .ok_or_else(|| "tx.sender_pubkey missing".to_string())?
            .to_string();

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
            (true, parse_intents(v2)?)
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

fn parse_intents(v2: &Value) -> Result<Vec<tau_state_proof_risc0_shared::SignedIntentV1>, String> {
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
        out.push(tau_state_proof_risc0_shared::SignedIntentV1 {
            intent,
            signature: None,
        });
    }
    Ok(out)
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
            let fee_bps = obj
                .get("fee_bps")
                .and_then(Value::as_u64)
                .ok_or_else(|| "intent.fee_bps missing".to_string())?;
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
                    fee_bps: fee_bps as u32,
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
        _ => Err("unsupported intent.kind".into()),
    }
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

fn hex_u32_words(words: [u32; 8]) -> String {
    let mut out = String::with_capacity(64);
    for w in words {
        out.push_str(&format!("{w:08x}"));
    }
    out
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

    fn h(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn hx(byte: u8) -> String {
        hex::encode(h(byte))
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

    fn spot_proof_meta() -> Value {
        json!({
            "proof_type": PROOF_TYPE,
            "proof": "unused",
            "meta": {
                "risc0_image_id": hex_u32_words(TAU_STATE_PROOF_GUEST_ID),
                "txs_commitment": hx(3),
                "ingress_commitment": hx(4),
                "pre_nonce_root": hx(5),
                "post_nonce_root": hx(6),
                "accepted_receipts_root": hx(7),
                "pre_app_hash": "",
                "post_app_hash": hx(2)
            }
        })
    }

    fn spot_journal() -> StateProofJournalV1 {
        StateProofJournalV1 {
            journal_version: JOURNAL_VERSION,
            state_hash: h(1),
            txs_commitment: h(3),
            ingress_commitment: h(4),
            pre_nonce_root: h(5),
            post_nonce_root: h(6),
            accepted_receipts_root: h(7),
            pre_app_hash_present: false,
            pre_app_hash: [0u8; 32],
            post_app_hash: h(2),
        }
    }

    #[test]
    fn spot_meta_bindings_accept_matching_journal() {
        let proof = spot_proof_meta();
        let journal = spot_journal();
        verify_spot_meta_bindings(&proof, &journal).unwrap();
    }

    #[test]
    fn spot_meta_bindings_reject_forged_nonce_and_receipt_roots() {
        let journal = spot_journal();

        let mut bad_receipts_root = spot_proof_meta();
        bad_receipts_root["meta"]["accepted_receipts_root"] = Value::String(hx(9));
        let err = verify_spot_meta_bindings(&bad_receipts_root, &journal).unwrap_err();
        assert_eq!(err, "proof.meta.accepted_receipts_root mismatch");

        let mut bad_pre_nonce = spot_proof_meta();
        bad_pre_nonce["meta"]["pre_nonce_root"] = Value::String(hx(8));
        let err = verify_spot_meta_bindings(&bad_pre_nonce, &journal).unwrap_err();
        assert_eq!(err, "proof.meta.pre_nonce_root mismatch");
    }

    #[test]
    fn strict_surface_bindings_accept_matching_context() {
        let req = strict_req();
        let proof = strict_proof_meta();
        verify_surface_request_bindings(
            &req,
            &proof,
            "devnet",
            false,
            [0u8; 32],
            h(2),
            h(3),
            h(4),
            h(5),
            h(6),
        )
        .unwrap();
    }

    #[test]
    fn strict_surface_bindings_reject_wrong_chain_and_operation() {
        let req = strict_req();
        let proof = strict_proof_meta();
        let err = verify_surface_request_bindings(
            &req,
            &proof,
            "other-chain",
            false,
            [0u8; 32],
            h(2),
            h(3),
            h(4),
            h(5),
            h(6),
        )
        .unwrap_err();
        assert_eq!(err, "chain_id mismatch");

        let mut bad_req = strict_req();
        bad_req["context"]["operation_hash"] = Value::String(hx(9));
        let err = verify_surface_request_bindings(
            &bad_req,
            &proof,
            "devnet",
            false,
            [0u8; 32],
            h(2),
            h(3),
            h(4),
            h(5),
            h(6),
        )
        .unwrap_err();
        assert_eq!(err, "context.operation_hash mismatch");
    }

    #[test]
    fn strict_surface_bindings_reject_wrong_post_hash_and_image_id() {
        let mut req = strict_req();
        req["tau_state"]["app_hash"] = Value::String(hx(8));
        let proof = strict_proof_meta();
        let err = verify_surface_request_bindings(
            &req,
            &proof,
            "devnet",
            false,
            [0u8; 32],
            h(2),
            h(3),
            h(4),
            h(5),
            h(6),
        )
        .unwrap_err();
        assert_eq!(err, "post_app_hash mismatch");

        let mut bad_image = strict_proof_meta();
        bad_image["meta"]["risc0_image_id"] = Value::String(hx(9));
        let err = check_proof_meta_image_id(&bad_image).unwrap_err();
        assert_eq!(err, "risc0_image_id mismatch");
    }

    /// Locks the nonzero-image-id gate: the all-zero placeholder image id
    /// (`methods/build.rs` writes `[0u32; 8]` when `RISC0_SKIP_BUILD=1` / no
    /// toolchain) must NEVER pass `check_proof_meta_image_id`. This is what
    /// keeps a placeholder / echo build from ever being treated as a real
    /// RISC0 proof surface. The expected real id (`TAU_STATE_PROOF_GUEST_ID`)
    /// is only all-zero in a placeholder build; in that build the guards in
    /// `validate_embedded_methods` fail closed before any verify path runs, so
    /// the placeholder meta id can never coincide with a real expected id.
    #[test]
    fn check_proof_meta_image_id_rejects_all_zero_placeholder() {
        let mut placeholder = strict_proof_meta();
        // "00".."00" (32 zero bytes) is the placeholder image id written by
        // methods/build.rs for a non-embedded (echo) build.
        placeholder["meta"]["risc0_image_id"] = Value::String(hx(0));
        // Only meaningful to assert rejection when the real embedded id is not
        // itself all-zero (i.e. a real toolchain build). In a placeholder build
        // the generate/verify entrypoints already die in validate_embedded_methods.
        if !TAU_STATE_PROOF_GUEST_ID.iter().all(|w| *w == 0) {
            let err = check_proof_meta_image_id(&placeholder).unwrap_err();
            assert_eq!(err, "risc0_image_id mismatch");
        }
        // The all-zero placeholder build must always fail closed at the embed gate.
        if TAU_STATE_PROOF_GUEST_ID.iter().all(|w| *w == 0) {
            assert!(TAU_STATE_PROOF_GUEST_ELF.is_empty());
        }
    }

    /// Locks fail-closed behavior when the proof carries no meta image id: a
    /// proof without `meta.risc0_image_id` must be rejected, never silently
    /// accepted as if the binding were satisfied.
    #[test]
    fn check_proof_meta_image_id_rejects_missing_meta_image_id() {
        let mut no_image = strict_proof_meta();
        no_image["meta"]
            .as_object_mut()
            .expect("meta object")
            .remove("risc0_image_id");
        let err = check_proof_meta_image_id(&no_image).unwrap_err();
        assert_eq!(err, "proof.meta.risc0_image_id missing");
    }
}
