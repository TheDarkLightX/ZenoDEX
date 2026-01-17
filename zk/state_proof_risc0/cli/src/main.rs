use std::io::{Read, Write};

use base64::Engine;
use risc0_zkvm::{default_prover, ExecutorEnv, Receipt};
use serde_json::{json, Value};

use tau_state_proof_risc0_methods::{TAU_STATE_PROOF_GUEST_ELF, TAU_STATE_PROOF_GUEST_ID};
use tau_state_proof_risc0_shared::{
    txs_commitment_v1, ChainBalanceV1, DexSnapshotV1, DexStateV1, StateProofInputV1,
    StateProofJournalV1, TauTxAppOpsV1, TauTxV1, PROOF_TYPE,
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
    let expected_post_app_hash = parse_hex32(&expected_post_app_hash_hex).unwrap_or_else(|e| die(&e));

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
        (true, parse_hex32(&pre_app_hash_hex).unwrap_or_else(|e| die(&e)))
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

    let input = StateProofInputV1 {
        state_hash,
        block_timestamp,
        pre_app_hash_present,
        pre_app_hash,
        pre_state,
        txs,
        chain_balances_post,
        expected_post_app_hash,
    };

    let env = ExecutorEnv::builder()
        .write(&input)
        .unwrap_or_else(|e| die(&format!("failed to write input: {e}")))
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

    let journal: StateProofJournalV1 = receipt
        .journal
        .decode()
        .unwrap_or_else(|e| die(&format!("failed to decode journal: {e}")));

    if journal.state_hash != state_hash {
        die("journal.state_hash mismatch");
    }

    let receipt_bytes =
        bincode::serialize(&receipt).unwrap_or_else(|e| die(&format!("failed to serialize receipt: {e}")));
    let proof_b64 = base64::engine::general_purpose::STANDARD.encode(receipt_bytes);

    let mut meta = serde_json::Map::new();
    meta.insert("risc0_image_id".to_string(), Value::String(hex_u32_words(TAU_STATE_PROOF_GUEST_ID)));
    meta.insert("txs_commitment".to_string(), Value::String(hex_lower(&journal.txs_commitment)));
    meta.insert(
        "pre_app_hash".to_string(),
        Value::String(if journal.pre_app_hash_present {
            hex_lower(&journal.pre_app_hash)
        } else {
            "".to_string()
        }),
    );
    meta.insert("post_app_hash".to_string(), Value::String(hex_lower(&journal.post_app_hash)));

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

    let proof_type = proof.get("proof_type").and_then(Value::as_str).unwrap_or("");
    if proof_type != PROOF_TYPE {
        return Err("unsupported proof_type".into());
    }

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

    let journal: StateProofJournalV1 = receipt
        .journal
        .decode()
        .map_err(|e| format!("failed to decode journal: {e}"))?;

    if journal.state_hash != expected_state_hash {
        return Err("journal.state_hash mismatch".into());
    }

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

    if let Some(context) = req.get("context") {
        if !context.is_object() {
            return Err("context must be an object".into());
        }
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

fn parse_dex_snapshot_json(app_state_json: &str) -> Result<DexSnapshotV1, String> {
    let v: Value = serde_json::from_str(app_state_json).map_err(|e| format!("app_state_pre invalid JSON: {e}"))?;
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
                .or_else(|| amt.as_i64().and_then(|i| if i >= 0 { Some(i as u64) } else { None }))
                .unwrap_or_else(|| die(&format!("{name}: invalid amount for pubkey")));
            out.push(ChainBalanceV1 {
                pubkey: pk.clone(),
                amount: n as u128,
            });
        }
    }
    out
}

fn parse_block_txs(v: Option<&Value>) -> Result<Vec<TauTxV1>, String> {
    let txs = v
        .and_then(Value::as_array)
        .ok_or_else(|| "block.transactions must be a list".to_string())?;
    let mut out = Vec::with_capacity(txs.len());
    for tx in txs {
        let tx_obj = tx.as_object().ok_or_else(|| "tx must be an object".to_string())?;
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
            let pk = arr[0].as_str().ok_or_else(|| "mint pubkey must be a string".to_string())?;
            let asset = arr[1].as_str().ok_or_else(|| "mint asset must be a string".to_string())?;
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
        let obj = entry.as_object().ok_or_else(|| "mint entry must be list or object".to_string())?;
        let pk = obj.get("pubkey").and_then(Value::as_str).ok_or_else(|| "mint pubkey missing".to_string())?;
        let asset = obj.get("asset").and_then(Value::as_str).ok_or_else(|| "mint asset missing".to_string())?;
        let amount = obj.get("amount").and_then(Value::as_u64).ok_or_else(|| "mint amount missing".to_string())?;
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
            out.push(tau_state_proof_risc0_shared::SignedIntentV1 { intent, signature: sig });
            continue;
        }
        let obj = entry.as_object().ok_or_else(|| "intent entry must be [intent, sig] or object".to_string())?;
        let intent = parse_intent_obj(obj)?;
        out.push(tau_state_proof_risc0_shared::SignedIntentV1 { intent, signature: None });
    }
    Ok(out)
}

fn parse_intent_obj(obj: &serde_json::Map<String, Value>) -> Result<tau_state_proof_risc0_shared::DexIntentV1, String> {
    let module = obj.get("module").and_then(Value::as_str).ok_or_else(|| "intent.module missing".to_string())?;
    let version = obj.get("version").and_then(Value::as_str).ok_or_else(|| "intent.version missing".to_string())?;
    let kind = obj.get("kind").and_then(Value::as_str).ok_or_else(|| "intent.kind missing".to_string())?;
    let intent_id = obj.get("intent_id").and_then(Value::as_str).ok_or_else(|| "intent.intent_id missing".to_string())?;
    let sender = obj.get("sender_pubkey").and_then(Value::as_str).ok_or_else(|| "intent.sender_pubkey missing".to_string())?;
    let deadline = obj.get("deadline").and_then(Value::as_u64).ok_or_else(|| "intent.deadline missing".to_string())?;
    let salt = obj.get("salt").and_then(Value::as_str).map(|s| s.to_string());

    match kind {
        "CREATE_POOL" => {
            let asset0 = obj.get("asset0").and_then(Value::as_str).ok_or_else(|| "intent.asset0 missing".to_string())?;
            let asset1 = obj.get("asset1").and_then(Value::as_str).ok_or_else(|| "intent.asset1 missing".to_string())?;
            let fee_bps = obj.get("fee_bps").and_then(Value::as_u64).ok_or_else(|| "intent.fee_bps missing".to_string())?;
            let amount0 = obj.get("amount0").and_then(Value::as_u64).ok_or_else(|| "intent.amount0 missing".to_string())?;
            let amount1 = obj.get("amount1").and_then(Value::as_u64).ok_or_else(|| "intent.amount1 missing".to_string())?;
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
            let pool_id = obj.get("pool_id").and_then(Value::as_str).ok_or_else(|| "intent.pool_id missing".to_string())?;
            let asset_in = obj.get("asset_in").and_then(Value::as_str).ok_or_else(|| "intent.asset_in missing".to_string())?;
            let asset_out = obj.get("asset_out").and_then(Value::as_str).ok_or_else(|| "intent.asset_out missing".to_string())?;
            let amount_in = obj.get("amount_in").and_then(Value::as_u64).ok_or_else(|| "intent.amount_in missing".to_string())?;
            let min_amount_out = obj.get("min_amount_out").and_then(Value::as_u64).ok_or_else(|| "intent.min_amount_out missing".to_string())?;
            let recipient = obj.get("recipient").and_then(Value::as_str).ok_or_else(|| "intent.recipient missing".to_string())?;
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
