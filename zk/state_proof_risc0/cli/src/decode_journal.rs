//! WS2 `tau_state_proof_decode_journal`: verify a receipt, then echo its journal.
//!
//! The refuse-by-default client core (`src/integration/client_admission_decision.py`)
//! needs the VERIFIED journal back so its policy gates run on receipt-committed
//! bytes, not host-asserted JSON. `tau_state_proof_verify` only answers ok/err
//! against caller-supplied expecteds; this command is the missing decode half:
//! `receipt.verify(TAU_STATE_PROOF_GUEST_ID)` FIRST (no journal is ever echoed for
//! an unverified receipt), then the complete journal as JSON, plus the binary's
//! compiled-in `verifier_image_id` so the caller can enforce its own client pin
//! against the verifier identity (not the proof's claim).
//!
//! Per-lane unconditional invariants mirror the try_verify_* lane checks in
//! `main.rs` (the request-binding checks stay with the client policy core).

use base64::Engine;
use risc0_zkvm::Receipt;
use serde_json::{json, Value};

use tau_state_proof_risc0_methods::TAU_STATE_PROOF_RISC0_GUEST_ID as TAU_STATE_PROOF_GUEST_ID;
use tau_state_proof_risc0_shared::clob::{
    clob_fee_rule_hash, clob_matching_rule_hash, ClobTransitionJournalV1, PROOF_TYPE_CLOB,
};
use tau_state_proof_risc0_shared::{
    PerpsNpTransitionJournalV1, ZusdTransitionJournalV1, PROOF_TYPE_PERPS_NP, PROOF_TYPE_ZUSD,
};

use crate::{decode_postcard_journal, hex_lower, hex_u32_words, validate_embedded_methods, write_json_stdout};

/// Emit the verifier binary's own identity: its compiled-in guest image id and the
/// proof types it can decode. This is the pin-BOOTSTRAP surface (a local operator
/// reads it once, out-of-band, when authoring a client pinset); the admission loop
/// itself never trusts it at decision time — it re-checks the id on every decode.
pub(crate) fn handle_verifier_identity(_req: &Value) {
    validate_embedded_methods();
    write_json_stdout(&json!({
        "ok": true,
        "verifier_image_id": hex_u32_words(TAU_STATE_PROOF_GUEST_ID),
        "verifier_image_id_words": image_id_words(TAU_STATE_PROOF_GUEST_ID),
        "proof_types": [PROOF_TYPE_PERPS_NP, PROOF_TYPE_ZUSD, PROOF_TYPE_CLOB],
    }));
}

pub(crate) fn handle_decode_journal(req: &Value) {
    let out = match try_decode_journal(req) {
        Ok(journal) => json!({
            "ok": true,
            "verifier_image_id": hex_u32_words(TAU_STATE_PROOF_GUEST_ID),
            "verifier_image_id_words": image_id_words(TAU_STATE_PROOF_GUEST_ID),
            "journal": journal,
        }),
        Err(err) => json!({ "ok": false, "error": err }),
    };
    write_json_stdout(&out);
}

fn try_decode_journal(req: &Value) -> Result<Value, String> {
    if req.get("schema_version").and_then(Value::as_i64) != Some(1) {
        return Err("unexpected schema_version (expected tau_state_proof_decode_journal v1)".into());
    }
    validate_embedded_methods();

    let requested_proof_type = req
        .get("proof_type")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof_type missing".to_string())?;

    let proof_b64 = req
        .get("proof")
        .and_then(Value::as_str)
        .ok_or_else(|| "proof missing (base64 receipt string)".to_string())?;
    let proof_bytes = base64::engine::general_purpose::STANDARD
        .decode(proof_b64)
        .map_err(|e| format!("invalid base64 proof: {e}"))?;
    let receipt: Receipt =
        bincode::deserialize(&proof_bytes).map_err(|e| format!("invalid receipt bytes: {e}"))?;

    // Fail-closed ordering: cryptographic verification BEFORE any journal echo.
    receipt
        .verify(TAU_STATE_PROOF_GUEST_ID)
        .map_err(|e| format!("receipt verification failed: {e}"))?;

    match requested_proof_type {
        PROOF_TYPE_PERPS_NP => decode_perps_np(&receipt),
        PROOF_TYPE_ZUSD => decode_zusd(&receipt),
        PROOF_TYPE_CLOB => decode_clob(&receipt),
        _ => Err("unsupported proof_type".into()),
    }
}

fn decode_perps_np(receipt: &Receipt) -> Result<Value, String> {
    let journal: PerpsNpTransitionJournalV1 =
        decode_postcard_journal(receipt, "perps np journal")?;
    if journal.proof_type != PROOF_TYPE_PERPS_NP {
        return Err("journal proof_type mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_GUEST_ID {
        return Err("journal.risc0_image_id mismatch".into());
    }
    // Structural identity only. Settlement-epoch invariants (participant_count >= 4,
    // net_position_base == 0) are enforced by the GUEST for the run_epoch op that
    // requires them; re-checking them here would wrongly reject a valid
    // deposit_collateral receipt for a bootstrapping market (1-3 participants).
    // The client policy binds operation semantics via the requested-op rebind.
    Ok(json!({
        "proof_type": journal.proof_type,
        "risc0_image_id": image_id_words(journal.risc0_image_id),
        "state_hash": hex_lower(&journal.state_hash),
        "chain_id": journal.chain_id,
        "pre_app_hash_present": journal.pre_app_hash_present,
        "pre_app_hash": hex_lower(&journal.pre_app_hash),
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
    }))
}

fn decode_zusd(receipt: &Receipt) -> Result<Value, String> {
    let journal: ZusdTransitionJournalV1 = decode_postcard_journal(receipt, "zUSD journal")?;
    if journal.proof_type != PROOF_TYPE_ZUSD {
        return Err("journal proof_type mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_GUEST_ID {
        return Err("journal.risc0_image_id mismatch".into());
    }
    // Structural identity only: minted_zusd_e8 > 0 is an operation-semantic
    // invariant of the mint op, enforced by the guest where it applies; the
    // generic decoder must not gate on it.
    Ok(json!({
        "proof_type": journal.proof_type,
        "risc0_image_id": image_id_words(journal.risc0_image_id),
        "state_hash": hex_lower(&journal.state_hash),
        "chain_id": journal.chain_id,
        "pre_app_hash_present": journal.pre_app_hash_present,
        "pre_app_hash": hex_lower(&journal.pre_app_hash),
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
    }))
}

fn decode_clob(receipt: &Receipt) -> Result<Value, String> {
    let journal: ClobTransitionJournalV1 = decode_postcard_journal(receipt, "CLOB journal")?;
    if journal.proof_type != PROOF_TYPE_CLOB {
        return Err("journal proof_type mismatch".into());
    }
    if journal.risc0_image_id != TAU_STATE_PROOF_GUEST_ID {
        return Err("journal.risc0_image_id mismatch".into());
    }
    if journal.post_app_hash != journal.post_book_root {
        return Err("journal post_app_hash/post_book_root mismatch".into());
    }
    if journal.operation_hash != journal.event_log_root {
        return Err("journal operation_hash/event_log_root mismatch".into());
    }
    if journal.matching_rule_hash != clob_matching_rule_hash() {
        return Err("matching_rule_hash mismatch".into());
    }
    if journal.fee_rule_hash != clob_fee_rule_hash() {
        return Err("fee_rule_hash mismatch".into());
    }
    if journal.fee_total != 0 {
        return Err("journal fee_total must be zero for CLOB v1".into());
    }
    Ok(json!({
        "proof_type": journal.proof_type,
        "risc0_image_id": image_id_words(journal.risc0_image_id),
        "state_hash": hex_lower(&journal.state_hash),
        "chain_id": journal.chain_id,
        "pre_app_hash_present": journal.pre_app_hash_present,
        "pre_app_hash": hex_lower(&journal.pre_app_hash),
        "post_app_hash": hex_lower(&journal.post_app_hash),
        "pre_book_root": hex_lower(&journal.pre_book_root),
        "post_book_root": hex_lower(&journal.post_book_root),
        "operation_hash": hex_lower(&journal.operation_hash),
        "state_delta_hash": hex_lower(&journal.state_delta_hash),
        "event_log_root": hex_lower(&journal.event_log_root),
        "matching_rule_hash": hex_lower(&journal.matching_rule_hash),
        "fee_rule_hash": hex_lower(&journal.fee_rule_hash),
        "fee_total": journal.fee_total.to_string(),
        "resting_taker_qty": journal.resting_taker_qty,
        "fill_count": journal.fills.len(),
    }))
}

fn image_id_words(words: [u32; 8]) -> Vec<u32> {
    words.to_vec()
}
