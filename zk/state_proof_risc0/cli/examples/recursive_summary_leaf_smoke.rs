use std::{env, fs::File, io::Read, path::Path};

use risc0_zkvm::Digest;
use serde_json::{json, Value};
use tau_state_proof_risc0_methods::TAU_STATE_PROOF_RISC0_AGGREGATE_ID;
use tau_state_proof_risc0_shared::{
    compose_recursive_epoch_journal_v1, recursive_asset_delta_root_v1,
    recursive_authority_set_root_v1, recursive_child_journal_hash_v1,
    recursive_child_verification_claim_hash_v1, recursive_child_verifier_id_v1,
    recursive_cross_shard_messages_root_v1, recursive_effect_summary_hash_v1,
    recursive_lane_state_vector_root_v1, recursive_receipt_ids_root_v1,
    recursive_verifier_set_root_v1, sha256_canonical_perps_np_snapshot_v1,
    sha256_canonical_zusd_snapshot_v1, DexStateV1, OracleBindingV1, PerpsAccountV1,
    PerpsMarketParamsV1, PerpsNpActionV1, PerpsNpRecursiveLeafInputV1, PerpsNpSnapshotV1,
    PerpsNpTransitionInputV1, RecursiveAssetDeltaRowV1, RecursiveChildDescriptorV1,
    RecursiveChildEffectV1, RecursiveCompositionInputV1, RecursiveCompositionStatementV1,
    RecursiveEffectSummaryV1, RecursiveEpochJournalV1, SpotRecursiveLeafInputV1, StateProofInputV1,
    ZusdBalanceEntryV1, ZusdOperationV1, ZusdRecursiveLeafInputV1, ZusdSnapshotV1,
    ZusdTransitionInputV1, ZusdVaultEntryV1, RECURSIVE_DOMAIN_SEPARATOR_V1,
    RECURSIVE_EFFECT_SUMMARY_VERSION_V1, RECURSIVE_EPOCH_PROFILE_V1,
    RECURSIVE_PERPS_NP_LEAF_MAX_INPUT_BYTES, RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES,
    RECURSIVE_STATEMENT_VERSION_V1, RECURSIVE_STRICT_CROSS_SHARD_MODE_V1,
    RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES, RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
    RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES,
};

#[path = "../src/strict_json.rs"]
mod strict_json;

const MAX_PROOF_JSON_BYTES: usize = 16 * 1024 * 1024;

fn root(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn hex_bytes(bytes: &[u8]) -> String {
    hex::encode(bytes)
}

const RECEIPT_CODEC_V1: &str = "risc0_receipt_canonical_serde_json_depth128_v1";

fn hex_image_id(words: [u32; 8]) -> String {
    Digest::from(words).to_string()
}

fn parse_hex32(value: &str) -> Result<[u8; 32], String> {
    let bytes = hex::decode(value).map_err(|e| format!("invalid hex32: {e}"))?;
    bytes
        .try_into()
        .map_err(|_| "hex32 must decode to 32 bytes".to_string())
}

fn parse_image_id(value: &str) -> Result<[u32; 8], String> {
    let bytes = hex::decode(value).map_err(|e| format!("invalid image id hex: {e}"))?;
    if bytes.len() != 32 {
        return Err("image id must decode to 32 bytes".to_string());
    }
    let mut out = [0u32; 8];
    for (slot, chunk) in out.iter_mut().zip(bytes.chunks_exact(4)) {
        *slot = u32::from_le_bytes(chunk.try_into().expect("chunk length is fixed"));
    }
    Ok(out)
}

fn parse_proof_json_bytes(bytes: &[u8]) -> Result<Value, String> {
    if bytes.len() > MAX_PROOF_JSON_BYTES {
        return Err("proof JSON exceeds byte limit".to_string());
    }
    let text =
        std::str::from_utf8(bytes).map_err(|error| format!("proof JSON is not UTF-8: {error}"))?;
    strict_json::parse_value(text).map_err(|error| format!("proof json: {error}"))
}

fn load_proof_json(path: &Path) -> Result<Value, String> {
    let file = File::open(path).map_err(|error| format!("open proof json: {error}"))?;
    let mut bytes = Vec::new();
    file.take((MAX_PROOF_JSON_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read proof json: {error}"))?;
    parse_proof_json_bytes(&bytes)
}

fn summary(image_id_hex: &str) -> Result<RecursiveEffectSummaryV1, String> {
    let empty_asset_rows = Vec::new();
    let empty_messages = Vec::new();
    let empty_receipts = Vec::new();
    Ok(RecursiveEffectSummaryV1 {
        summary_version: RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
        lane_id: "summary-leaf-root-child-0001".to_string(),
        lane_kind: "recursive_summary_leaf_smoke".to_string(),
        chain_id: "tau-devnet-recursive-smoke".to_string(),
        epoch_id: 1,
        proof_profile: RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1.to_string(),
        risc0_image_id: parse_image_id(image_id_hex)?,
        statement_hash: root(1),
        pre_state_root: root(2),
        post_state_root: root(3),
        tx_root: root(4),
        evidence_root: root(5),
        receipt_root: root(6),
        accepted_receipts_root: recursive_receipt_ids_root_v1(&empty_receipts)
            .map_err(|e| format!("{e:?}"))?,
        rejected_receipts_root: recursive_receipt_ids_root_v1(&empty_receipts)
            .map_err(|e| format!("{e:?}"))?,
        asset_delta_root: recursive_asset_delta_root_v1(&empty_asset_rows)
            .map_err(|e| format!("{e:?}"))?,
        cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)
            .map_err(|e| format!("{e:?}"))?,
        cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&empty_messages)
            .map_err(|e| format!("{e:?}"))?,
        write_set_root: root(7),
        public_policy_hash: root(8),
        feature_suite_hash: root(9),
        dependency_lock_hash: root(10),
        toolchain_lock_hash: root(11),
    })
}

fn print_summary_request(image_id_hex: &str) -> Result<(), String> {
    let summary = summary(image_id_hex)?;
    let bytes = postcard::to_allocvec(&summary).map_err(|e| format!("postcard summary: {e}"))?;
    if bytes.len() > RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES as usize {
        return Err("summary exceeds summary-leaf input byte cap".to_string());
    }
    println!(
        "{}",
        serde_json::to_string(&json!({
            "schema": "tau_state_proof_request",
            "schema_version": 1,
            "state_hash": hex_bytes(&summary.post_state_root),
            "proof_type": "risc0.zenodex_recursive_summary_leaf.v1",
            "receipt_kind": "composite",
            "recursive_summary": summary,
        }))
        .map_err(|e| format!("summary request json: {e}"))?
    );
    Ok(())
}

fn print_spot_request(image_id_hex: &str) -> Result<(), String> {
    let snapshot = DexStateV1::empty().to_snapshot();
    let app_hash = DexStateV1::from_snapshot(snapshot.clone())
        .map_err(|e| format!("spot pre-state rejected: {e:?}"))?
        .canonical_app_hash_sha256();
    let input = SpotRecursiveLeafInputV1 {
        chain_id: "tau-devnet-recursive-smoke".to_string(),
        epoch_id: 1,
        lane_id: "spot-root-child-0001".to_string(),
        risc0_image_id: parse_image_id(image_id_hex)?,
        public_policy_hash: root(8),
        feature_suite_hash: root(9),
        dependency_lock_hash: root(10),
        toolchain_lock_hash: root(11),
        spot_input: StateProofInputV1 {
            state_hash: app_hash,
            block_timestamp: 1,
            pre_app_hash_present: true,
            pre_app_hash: app_hash,
            pre_state: snapshot,
            txs: Vec::new(),
            pre_nonces: Vec::new(),
            tx_ingress: Vec::new(),
            chain_balances_post: Vec::new(),
            expected_post_app_hash: app_hash,
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
    let bytes = postcard::to_allocvec(&input).map_err(|e| format!("postcard spot leaf: {e}"))?;
    if bytes.len() > RECURSIVE_SPOT_LEAF_MAX_INPUT_BYTES as usize {
        return Err("spot leaf input exceeds input byte cap".to_string());
    }
    println!(
        "{}",
        serde_json::to_string(&json!({
            "schema": "tau_state_proof_request",
            "schema_version": 1,
            "state_hash": hex_bytes(&app_hash),
            "proof_type": "risc0.zenodex_recursive_spot_leaf.v1",
            "receipt_kind": "succinct",
            "spot_recursive_leaf_input": input,
        }))
        .map_err(|e| format!("spot request json: {e}"))?
    );
    Ok(())
}

fn smoke_oracle(price_e8: i128) -> OracleBindingV1 {
    OracleBindingV1 {
        oracle_bridge_id: "oracle-bridge-a".to_string(),
        oracle_bridge_hash: "1111111111111111111111111111111111111111111111111111111111111111"
            .to_string(),
        price_e8,
        price_timestamp: 10,
        max_staleness_seconds: 10,
        observed_at: 12,
        pre_price_batch_commitment:
            "2222222222222222222222222222222222222222222222222222222222222222".to_string(),
    }
}

fn print_zusd_request(image_id_hex: &str) -> Result<(), String> {
    let e8 = 100_000_000u128;
    let image_id = parse_image_id(image_id_hex)?;
    let pre_state = ZusdSnapshotV1::empty();
    let pre_app_hash = sha256_canonical_zusd_snapshot_v1(&pre_state);
    let operation = ZusdOperationV1::DepositMint {
        pubkey: "wallet-a".to_string(),
        collateral_asset: "tAGRS".to_string(),
        deposit_amount_e8: 2_000 * e8,
        mint_amount_e8: 1_000 * e8,
        oracle: smoke_oracle(e8 as i128),
        mcr_bps: 11_000,
        nonce: 1,
    };
    let post_state = ZusdSnapshotV1 {
        version: 1,
        vaults: vec![ZusdVaultEntryV1 {
            pubkey: "wallet-a".to_string(),
            collateral_asset: "tAGRS".to_string(),
            collateral_amount_e8: 2_000 * e8,
            debt_zusd_e8: 1_000 * e8,
            nonce: 1,
        }],
        balances: vec![ZusdBalanceEntryV1 {
            pubkey: "wallet-a".to_string(),
            amount_e8: 1_000 * e8,
        }],
        total_debt_zusd_e8: 1_000 * e8,
    };
    let post_app_hash = sha256_canonical_zusd_snapshot_v1(&post_state);
    let input = ZusdRecursiveLeafInputV1 {
        chain_id: "tau-devnet-recursive-smoke".to_string(),
        epoch_id: 1,
        lane_id: "zusd-root-child-0001".to_string(),
        risc0_image_id: image_id,
        public_policy_hash: root(8),
        feature_suite_hash: root(9),
        dependency_lock_hash: root(10),
        toolchain_lock_hash: root(11),
        zusd_input: ZusdTransitionInputV1 {
            state_hash: post_app_hash,
            chain_id: "tau-devnet-recursive-smoke".to_string(),
            pre_app_hash_present: true,
            pre_app_hash,
            pre_state,
            operation,
            expected_post_app_hash: post_app_hash,
            risc0_image_id: image_id,
        },
    };
    let bytes = postcard::to_allocvec(&input).map_err(|e| format!("postcard zUSD leaf: {e}"))?;
    if bytes.len() > RECURSIVE_ZUSD_LEAF_MAX_INPUT_BYTES as usize {
        return Err("zUSD leaf input exceeds input byte cap".to_string());
    }
    println!(
        "{}",
        serde_json::to_string(&json!({
            "schema": "tau_state_proof_request",
            "schema_version": 1,
            "state_hash": hex_bytes(&post_app_hash),
            "proof_type": "risc0.zenodex_recursive_zusd_leaf.v1",
            "receipt_kind": "succinct",
            "zusd_recursive_leaf_input": input,
        }))
        .map_err(|e| format!("zUSD request json: {e}"))?
    );
    Ok(())
}

fn perps_snapshot(now_epoch: u64) -> PerpsNpSnapshotV1 {
    let e8 = 100_000_000i128;
    PerpsNpSnapshotV1 {
        version: 1,
        market_id: "BTC-PERP".to_string(),
        collateral_asset: "zUSD".to_string(),
        index_price_e8: 100 * e8,
        params: PerpsMarketParamsV1::default(),
        accounts: ["wallet-a", "wallet-b", "wallet-c", "wallet-d"]
            .iter()
            .map(|wallet| PerpsAccountV1 {
                pubkey: (*wallet).to_string(),
                position_base: 0,
                entry_price_e8: 0,
                collateral_e8: 2_000 * e8,
                funding_paid_cum_e8: 0,
                nonce: 1,
            })
            .collect(),
        pending_intents: Vec::new(),
        now_epoch,
        fee_pool_e8: 0,
        insurance_e8: 1_000_000_000,
        insurance_ext_e8: 1_000_000_000,
        claims_paid_e8: 0,
        net_deposited_e8: 4 * 2_000 * e8,
    }
}

fn print_perps_request(image_id_hex: &str) -> Result<(), String> {
    let e8 = 100_000_000i128;
    let image_id = parse_image_id(image_id_hex)?;
    let pre_state = perps_snapshot(0);
    let post_state = perps_snapshot(1);
    let pre_app_hash = sha256_canonical_perps_np_snapshot_v1(&pre_state);
    let post_app_hash = sha256_canonical_perps_np_snapshot_v1(&post_state);
    let input = PerpsNpRecursiveLeafInputV1 {
        chain_id: "tau-devnet-recursive-smoke".to_string(),
        epoch_id: 1,
        lane_id: "perps-np-root-child-0001".to_string(),
        risc0_image_id: image_id,
        public_policy_hash: root(8),
        feature_suite_hash: root(9),
        dependency_lock_hash: root(10),
        toolchain_lock_hash: root(11),
        perps_input: PerpsNpTransitionInputV1 {
            state_hash: post_app_hash,
            chain_id: "tau-devnet-recursive-smoke".to_string(),
            pre_app_hash_present: true,
            pre_app_hash,
            pre_state,
            actions: vec![PerpsNpActionV1::RunEpoch {
                oracle: smoke_oracle(100 * e8),
                clearing_price_e8: 100 * e8,
                funding_rate_bps: 0,
                intents: Vec::new(),
            }],
            expected_post_app_hash: post_app_hash,
            risc0_image_id: image_id,
        },
    };
    let bytes =
        postcard::to_allocvec(&input).map_err(|e| format!("postcard perps NP leaf: {e}"))?;
    if bytes.len() > RECURSIVE_PERPS_NP_LEAF_MAX_INPUT_BYTES as usize {
        return Err("perps NP leaf input exceeds input byte cap".to_string());
    }
    println!(
        "{}",
        serde_json::to_string(&json!({
            "schema": "tau_state_proof_request",
            "schema_version": 1,
            "state_hash": hex_bytes(&post_app_hash),
            "proof_type": "risc0.zenodex_recursive_perps_np_leaf.v1",
            "receipt_kind": "succinct",
            "perps_np_recursive_leaf_input": input,
        }))
        .map_err(|e| format!("perps NP request json: {e}"))?
    );
    Ok(())
}

fn summary_from_meta(meta: &Value) -> Result<RecursiveEffectSummaryV1, String> {
    Ok(RecursiveEffectSummaryV1 {
        summary_version: meta["summary_version"]
            .as_u64()
            .ok_or("summary_version missing")? as u32,
        lane_id: meta["lane_id"]
            .as_str()
            .ok_or("lane_id missing")?
            .to_string(),
        lane_kind: meta["lane_kind"]
            .as_str()
            .ok_or("lane_kind missing")?
            .to_string(),
        chain_id: meta["chain_id"]
            .as_str()
            .ok_or("chain_id missing")?
            .to_string(),
        epoch_id: meta["epoch_id"].as_u64().ok_or("epoch_id missing")?,
        proof_profile: meta["proof_profile"]
            .as_str()
            .ok_or("proof_profile missing")?
            .to_string(),
        risc0_image_id: parse_image_id(
            meta["risc0_image_id"]
                .as_str()
                .ok_or("risc0_image_id missing")?,
        )?,
        statement_hash: parse_hex32(meta["statement_hash"].as_str().ok_or("statement_hash")?)?,
        pre_state_root: parse_hex32(meta["pre_state_root"].as_str().ok_or("pre_state_root")?)?,
        post_state_root: parse_hex32(meta["post_state_root"].as_str().ok_or("post_state_root")?)?,
        tx_root: parse_hex32(meta["tx_root"].as_str().ok_or("tx_root")?)?,
        evidence_root: parse_hex32(meta["evidence_root"].as_str().ok_or("evidence_root")?)?,
        receipt_root: parse_hex32(meta["receipt_root"].as_str().ok_or("receipt_root")?)?,
        accepted_receipts_root: parse_hex32(
            meta["accepted_receipts_root"]
                .as_str()
                .ok_or("accepted_receipts_root")?,
        )?,
        rejected_receipts_root: parse_hex32(
            meta["rejected_receipts_root"]
                .as_str()
                .ok_or("rejected_receipts_root")?,
        )?,
        asset_delta_root: parse_hex32(
            meta["asset_delta_root"]
                .as_str()
                .ok_or("asset_delta_root")?,
        )?,
        cross_shard_outbox_root: parse_hex32(
            meta["cross_shard_outbox_root"]
                .as_str()
                .ok_or("cross_shard_outbox_root")?,
        )?,
        cross_shard_inbox_root: parse_hex32(
            meta["cross_shard_inbox_root"]
                .as_str()
                .ok_or("cross_shard_inbox_root")?,
        )?,
        write_set_root: parse_hex32(meta["write_set_root"].as_str().ok_or("write_set_root")?)?,
        public_policy_hash: parse_hex32(
            meta["public_policy_hash"]
                .as_str()
                .ok_or("public_policy_hash")?,
        )?,
        feature_suite_hash: parse_hex32(
            meta["feature_suite_hash"]
                .as_str()
                .ok_or("feature_suite_hash")?,
        )?,
        dependency_lock_hash: parse_hex32(
            meta["dependency_lock_hash"]
                .as_str()
                .ok_or("dependency_lock_hash")?,
        )?,
        toolchain_lock_hash: parse_hex32(
            meta["toolchain_lock_hash"]
                .as_str()
                .ok_or("toolchain_lock_hash")?,
        )?,
    })
}

fn parse_u128_meta(value: &Value, field: &str) -> Result<u128, String> {
    if let Some(s) = value.as_str() {
        return s
            .parse::<u128>()
            .map_err(|e| format!("{field} invalid u128 string: {e}"));
    }
    if let Some(n) = value.as_u64() {
        return Ok(n as u128);
    }
    Err(format!(
        "{field} must be a decimal string or nonnegative integer"
    ))
}

fn asset_delta_rows_from_meta(meta: &Value) -> Result<Vec<RecursiveAssetDeltaRowV1>, String> {
    let Some(raw_rows) = meta.get("asset_delta_rows") else {
        return Ok(Vec::new());
    };
    let rows = raw_rows
        .as_array()
        .ok_or("asset_delta_rows must be an array")?;
    let mut out = Vec::with_capacity(rows.len());
    for row in rows {
        let obj = row
            .as_object()
            .ok_or("asset_delta_rows entry must be an object")?;
        let asset_id = obj
            .get("asset_id")
            .and_then(Value::as_str)
            .ok_or("asset_delta_rows.asset_id missing")?
            .to_string();
        let debit_atoms = parse_u128_meta(
            obj.get("debit_atoms")
                .ok_or("asset_delta_rows.debit_atoms missing")?,
            "asset_delta_rows.debit_atoms",
        )?;
        let credit_atoms = parse_u128_meta(
            obj.get("credit_atoms")
                .ok_or("asset_delta_rows.credit_atoms missing")?,
            "asset_delta_rows.credit_atoms",
        )?;
        let authorized_mint_atoms = parse_u128_meta(
            obj.get("authorized_mint_atoms")
                .ok_or("asset_delta_rows.authorized_mint_atoms missing")?,
            "asset_delta_rows.authorized_mint_atoms",
        )?;
        let authorized_burn_atoms = parse_u128_meta(
            obj.get("authorized_burn_atoms")
                .ok_or("asset_delta_rows.authorized_burn_atoms missing")?,
            "asset_delta_rows.authorized_burn_atoms",
        )?;
        let authority_root = parse_hex32(
            obj.get("authority_root")
                .and_then(Value::as_str)
                .ok_or("asset_delta_rows.authority_root missing")?,
        )?;
        out.push(RecursiveAssetDeltaRowV1 {
            asset_id,
            debit_atoms,
            credit_atoms,
            authorized_mint_atoms,
            authorized_burn_atoms,
            authority_root,
        });
    }
    recursive_asset_delta_root_v1(&out).map_err(|e| format!("asset_delta_rows invalid: {e:?}"))?;
    Ok(out)
}

fn child_from_proof_json(proof_json: &Value) -> Result<(String, RecursiveChildEffectV1), String> {
    if proof_json["meta"]["receipt_codec"].as_str() != Some(RECEIPT_CODEC_V1) {
        return Err("meta.receipt_codec mismatch".to_string());
    }
    let receipt_kind = proof_json["meta"]["receipt_kind"]
        .as_str()
        .ok_or("meta.receipt_kind missing")?;
    if receipt_kind != "succinct" {
        return Err("recursive root child receipt_kind must be succinct".to_string());
    }
    let summary = summary_from_meta(&proof_json["meta"])?;
    let asset_delta_rows = asset_delta_rows_from_meta(&proof_json["meta"])?;
    let asset_delta_root =
        recursive_asset_delta_root_v1(&asset_delta_rows).map_err(|e| format!("{e:?}"))?;
    if asset_delta_root != summary.asset_delta_root {
        return Err("asset_delta_rows root mismatch".to_string());
    }
    let child_journal_bytes =
        postcard::to_allocvec(&summary).map_err(|e| format!("postcard summary: {e}"))?;
    let child_verification_claim_hash =
        recursive_child_verification_claim_hash_v1(&summary.risc0_image_id, &child_journal_bytes)
            .map_err(|e| format!("{e:?}"))?;
    let child_journal_hash =
        recursive_child_journal_hash_v1(&child_journal_bytes).map_err(|e| format!("{e:?}"))?;
    let child_effect_summary_hash = recursive_effect_summary_hash_v1(&summary);
    let child_verifier_id =
        recursive_child_verifier_id_v1(&summary.risc0_image_id, &summary.proof_profile)
            .map_err(|e| format!("{e:?}"))?;
    let proof = proof_json["proof"]
        .as_str()
        .ok_or("proof field missing")?
        .to_string();
    let child = RecursiveChildEffectV1 {
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
        summary: summary.clone(),
        asset_delta_rows,
        outbox_messages: Vec::new(),
        inbox_messages: Vec::new(),
        accepted_receipt_ids: Vec::new(),
        rejected_receipt_ids: Vec::new(),
    };
    Ok((proof, child))
}

fn print_root_request(proof_paths: &[String]) -> Result<(), String> {
    let mut child_proofs = Vec::new();
    let mut children = Vec::new();
    let mut receipt_profile: Option<(String, String, String)> = None;
    for proof_path in proof_paths {
        let proof_json = load_proof_json(Path::new(proof_path))?;
        let current_profile = (
            proof_json["meta"]["receipt_hashfn"]
                .as_str()
                .ok_or("meta.receipt_hashfn missing")?
                .to_string(),
            proof_json["meta"]["receipt_verifier_parameters"]
                .as_str()
                .ok_or("meta.receipt_verifier_parameters missing")?
                .to_string(),
            proof_json["meta"]["receipt_control_id"]
                .as_str()
                .ok_or("meta.receipt_control_id missing")?
                .to_string(),
        );
        if receipt_profile
            .as_ref()
            .is_some_and(|expected| expected != &current_profile)
        {
            return Err("child receipt security profile mismatch".to_string());
        }
        receipt_profile.get_or_insert(current_profile);
        let (proof, child) = child_from_proof_json(&proof_json)?;
        child_proofs.push((child.summary.lane_id.clone(), proof));
        children.push(child);
    }
    children.sort_by(|left, right| left.summary.lane_id.cmp(&right.summary.lane_id));
    child_proofs.sort_by(|left, right| left.0.cmp(&right.0));

    let summary = children
        .first()
        .ok_or("at least one recursive leaf proof required")?
        .summary
        .clone();
    for child in &children {
        if child.summary.chain_id != summary.chain_id {
            return Err("child chain_id mismatch".to_string());
        }
        if child.summary.epoch_id != summary.epoch_id {
            return Err("child epoch_id mismatch".to_string());
        }
        if child.summary.public_policy_hash != summary.public_policy_hash {
            return Err("child public_policy_hash mismatch".to_string());
        }
        if child.summary.feature_suite_hash != summary.feature_suite_hash {
            return Err("child feature_suite_hash mismatch".to_string());
        }
        if child.summary.dependency_lock_hash != summary.dependency_lock_hash {
            return Err("child dependency_lock_hash mismatch".to_string());
        }
        if child.summary.toolchain_lock_hash != summary.toolchain_lock_hash {
            return Err("child toolchain_lock_hash mismatch".to_string());
        }
    }

    let mut verifier_ids: Vec<[u8; 32]> = children
        .iter()
        .map(|child| child.descriptor.child_verifier_id)
        .collect();
    verifier_ids.sort();
    verifier_ids.dedup();
    let mut authority_roots: Vec<[u8; 32]> = children
        .iter()
        .flat_map(|child| child.asset_delta_rows.iter())
        .map(|row| row.authority_root)
        .filter(|root| *root != [0u8; 32])
        .collect();
    authority_roots.sort();
    authority_roots.dedup();
    let pre_state_roots: Vec<(String, [u8; 32])> = children
        .iter()
        .map(|child| (child.summary.lane_id.clone(), child.summary.pre_state_root))
        .collect();
    let post_state_roots: Vec<(String, [u8; 32])> = children
        .iter()
        .map(|child| (child.summary.lane_id.clone(), child.summary.post_state_root))
        .collect();
    let child_count =
        u32::try_from(children.len()).map_err(|_| "too many child proofs".to_string())?;
    let max_total_child_journal_bytes = RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES
        .checked_mul(child_count)
        .ok_or("max_total_child_journal_bytes overflow")?;
    let expected_pre_state_root = recursive_lane_state_vector_root_v1(
        b"zenodex.risc0.recursive.pre_state_vector_root.v1",
        &pre_state_roots,
    )
    .map_err(|e| format!("{e:?}"))?;
    let expected_post_state_root = recursive_lane_state_vector_root_v1(
        b"zenodex.risc0.recursive.post_state_vector_root.v1",
        &post_state_roots,
    )
    .map_err(|e| format!("{e:?}"))?;
    let input = RecursiveCompositionInputV1 {
        statement: RecursiveCompositionStatementV1 {
            domain_separator: RECURSIVE_DOMAIN_SEPARATOR_V1.to_string(),
            schema_version: RECURSIVE_STATEMENT_VERSION_V1,
            chain_id: summary.chain_id.clone(),
            epoch_id: summary.epoch_id,
            proof_profile: RECURSIVE_EPOCH_PROFILE_V1.to_string(),
            verifier_set_root: recursive_verifier_set_root_v1(&verifier_ids)
                .map_err(|e| format!("{e:?}"))?,
            allowed_authority_roots_root: recursive_authority_set_root_v1(&authority_roots)
                .map_err(|e| format!("{e:?}"))?,
            public_policy_hash: summary.public_policy_hash,
            feature_suite_hash: summary.feature_suite_hash,
            dependency_lock_hash: summary.dependency_lock_hash,
            toolchain_lock_hash: summary.toolchain_lock_hash,
            expected_pre_state_root,
            expected_post_state_root,
            conflict_schedule_hash: root(12),
            carry_queue_pre_root: root(13),
            carry_queue_post_root: root(13),
            data_availability_root: root(14),
            expected_child_count: child_count,
            max_children: 8,
            max_child_journal_bytes: RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES,
            max_total_child_journal_bytes,
            max_asset_delta_rows: 16,
            max_cross_shard_messages: 16,
            max_receipt_ids: 16,
            cross_shard_mode: RECURSIVE_STRICT_CROSS_SHARD_MODE_V1.to_string(),
        },
        allowed_verifier_ids: verifier_ids,
        allowed_authority_roots: authority_roots,
        children,
    };
    let child_proofs: Vec<String> = child_proofs.into_iter().map(|(_, proof)| proof).collect();
    let expected_journal = compose_recursive_epoch_journal_v1(&input)
        .map_err(|e| format!("local recursive fixture rejected: {e:?}"))?;
    let receipt_profile = receipt_profile.ok_or("child receipt security profile missing")?;
    let recursive_expectations =
        local_fixture_recursive_expectations(&expected_journal, &receipt_profile);
    println!(
        "{}",
        serde_json::to_string(&json!({
            "schema": "tau_state_proof_request",
            "schema_version": 1,
            "state_hash": hex_bytes(&expected_post_state_root),
            "proof_type": "risc0.zenodex_recursive_epoch.v1",
            "receipt_kind": "succinct",
            "child_receipt_codec": RECEIPT_CODEC_V1,
            "recursive_expectations": recursive_expectations,
            "recursive_input": input,
            "child_proofs": child_proofs,
        }))
        .map_err(|e| format!("root request json: {e}"))?
    );
    Ok(())
}

fn local_fixture_recursive_expectations(
    journal: &RecursiveEpochJournalV1,
    receipt_profile: &(String, String, String),
) -> Value {
    json!({
        "risc0_image_id": hex_image_id(TAU_STATE_PROOF_RISC0_AGGREGATE_ID),
        "receipt_codec": RECEIPT_CODEC_V1,
        "receipt_kind": "succinct",
        "receipt_hashfn": receipt_profile.0.as_str(),
        "receipt_verifier_parameters": receipt_profile.1.as_str(),
        "receipt_control_id": receipt_profile.2.as_str(),
        "journal_version": journal.journal_version,
        "proof_type": journal.proof_type.as_str(),
        "domain_separator": journal.domain_separator.as_str(),
        "chain_id": journal.chain_id.as_str(),
        "epoch_id": journal.epoch_id,
        "proof_profile": journal.proof_profile.as_str(),
        "statement_hash": hex_bytes(&journal.statement_hash),
        "verifier_set_root": hex_bytes(&journal.verifier_set_root),
        "allowed_authority_roots_root": hex_bytes(&journal.allowed_authority_roots_root),
        "child_verification_claims_root": hex_bytes(&journal.child_verification_claims_root),
        "child_journals_root": hex_bytes(&journal.child_journals_root),
        "child_effect_summaries_root": hex_bytes(&journal.child_effect_summaries_root),
        "child_count": journal.child_count,
        "pre_state_root": hex_bytes(&journal.pre_state_root),
        "post_state_root": hex_bytes(&journal.post_state_root),
        "tx_root": hex_bytes(&journal.tx_root),
        "evidence_root": hex_bytes(&journal.evidence_root),
        "receipt_root": hex_bytes(&journal.receipt_root),
        "accepted_receipts_root": hex_bytes(&journal.accepted_receipts_root),
        "rejected_receipts_root": hex_bytes(&journal.rejected_receipts_root),
        "aggregate_asset_delta_root": hex_bytes(&journal.aggregate_asset_delta_root),
        "cross_shard_outbox_root": hex_bytes(&journal.cross_shard_outbox_root),
        "cross_shard_inbox_root": hex_bytes(&journal.cross_shard_inbox_root),
        "cross_shard_message_ids_root": hex_bytes(&journal.cross_shard_message_ids_root),
        "carry_queue_pre_root": hex_bytes(&journal.carry_queue_pre_root),
        "carry_queue_post_root": hex_bytes(&journal.carry_queue_post_root),
        "conflict_schedule_hash": hex_bytes(&journal.conflict_schedule_hash),
        "data_availability_root": hex_bytes(&journal.data_availability_root),
        "public_policy_hash": hex_bytes(&journal.public_policy_hash),
        "feature_suite_hash": hex_bytes(&journal.feature_suite_hash),
        "dependency_lock_hash": hex_bytes(&journal.dependency_lock_hash),
        "toolchain_lock_hash": hex_bytes(&journal.toolchain_lock_hash),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_PROOF_FIXTURE_ID: AtomicU64 = AtomicU64::new(0);

    struct ProofFixture {
        path: String,
    }

    impl ProofFixture {
        fn new(label: &str, proof: &Value) -> Self {
            let fixture_id = NEXT_PROOF_FIXTURE_ID.fetch_add(1, Ordering::Relaxed);
            let path = env::temp_dir().join(format!(
                "zenodex-recursive-summary-leaf-smoke-{}-{fixture_id}-{label}.json",
                std::process::id()
            ));
            fs::write(
                &path,
                serde_json::to_vec(proof).expect("serialize proof fixture"),
            )
            .expect("write proof fixture");
            Self {
                path: path.to_string_lossy().into_owned(),
            }
        }
    }

    impl Drop for ProofFixture {
        fn drop(&mut self) {
            let _ = fs::remove_file(&self.path);
        }
    }

    fn image_hex(words: [u32; 8]) -> String {
        hex_image_id(words)
    }

    fn row_json(row: &RecursiveAssetDeltaRowV1) -> Value {
        json!({
            "asset_id": row.asset_id.as_str(),
            "debit_atoms": row.debit_atoms.to_string(),
            "credit_atoms": row.credit_atoms.to_string(),
            "authorized_mint_atoms": row.authorized_mint_atoms.to_string(),
            "authorized_burn_atoms": row.authorized_burn_atoms.to_string(),
            "authority_root": hex_bytes(&row.authority_root),
        })
    }

    fn proof_json(summary: &RecursiveEffectSummaryV1, rows: &[RecursiveAssetDeltaRowV1]) -> Value {
        json!({
            "proof": "opaque-child-proof",
            "meta": {
                "receipt_codec": RECEIPT_CODEC_V1,
                "receipt_kind": "succinct",
                "receipt_hashfn": "sha-256",
                "receipt_verifier_parameters": "smoke-verifier-parameters",
                "receipt_control_id": "smoke-control-id",
                "summary_version": summary.summary_version,
                "lane_id": summary.lane_id,
                "lane_kind": summary.lane_kind,
                "chain_id": summary.chain_id,
                "epoch_id": summary.epoch_id,
                "proof_profile": summary.proof_profile,
                "risc0_image_id": image_hex(summary.risc0_image_id),
                "statement_hash": hex_bytes(&summary.statement_hash),
                "pre_state_root": hex_bytes(&summary.pre_state_root),
                "post_state_root": hex_bytes(&summary.post_state_root),
                "tx_root": hex_bytes(&summary.tx_root),
                "evidence_root": hex_bytes(&summary.evidence_root),
                "receipt_root": hex_bytes(&summary.receipt_root),
                "accepted_receipts_root": hex_bytes(&summary.accepted_receipts_root),
                "rejected_receipts_root": hex_bytes(&summary.rejected_receipts_root),
                "asset_delta_root": hex_bytes(&summary.asset_delta_root),
                "asset_delta_rows": rows.iter().map(row_json).collect::<Vec<_>>(),
                "cross_shard_outbox_root": hex_bytes(&summary.cross_shard_outbox_root),
                "cross_shard_inbox_root": hex_bytes(&summary.cross_shard_inbox_root),
                "write_set_root": hex_bytes(&summary.write_set_root),
                "public_policy_hash": hex_bytes(&summary.public_policy_hash),
                "feature_suite_hash": hex_bytes(&summary.feature_suite_hash),
                "dependency_lock_hash": hex_bytes(&summary.dependency_lock_hash),
                "toolchain_lock_hash": hex_bytes(&summary.toolchain_lock_hash),
            },
        })
    }

    fn zusd_mint_row() -> RecursiveAssetDeltaRowV1 {
        RecursiveAssetDeltaRowV1 {
            asset_id: "zUSD".to_string(),
            debit_atoms: 0,
            credit_atoms: 100,
            authorized_mint_atoms: 100,
            authorized_burn_atoms: 0,
            authority_root: root(8),
        }
    }

    fn admissible_same_profile_summary(lane_id: &str) -> RecursiveEffectSummaryV1 {
        let mut summary = summary(&hex_bytes(&root(1))).expect("build summary fixture");
        summary.lane_id = lane_id.to_string();
        summary.lane_kind = "spot".to_string();
        summary.proof_profile =
            tau_state_proof_risc0_shared::RECURSIVE_SPOT_LEAF_PROFILE_V1.to_string();
        summary
    }

    #[test]
    fn child_from_proof_json_carries_asset_delta_rows() {
        let rows = vec![zusd_mint_row()];
        let mut summary = summary(&hex_bytes(&root(1))).unwrap();
        summary.asset_delta_root = recursive_asset_delta_root_v1(&rows).unwrap();
        let proof = proof_json(&summary, &rows);

        let (_receipt, child) = child_from_proof_json(&proof).unwrap();

        assert_eq!(child.asset_delta_rows, rows);
        assert_eq!(child.summary.asset_delta_root, summary.asset_delta_root);
    }

    #[test]
    fn child_from_proof_json_rejects_asset_delta_row_root_mismatch() {
        let rows = vec![zusd_mint_row()];
        let summary = summary(&hex_bytes(&root(1))).unwrap();
        let proof = proof_json(&summary, &rows);

        assert_eq!(
            child_from_proof_json(&proof).unwrap_err(),
            "asset_delta_rows root mismatch"
        );
    }

    #[test]
    fn root_request_accepts_two_distinct_children_with_same_verifier_profile() {
        let left = admissible_same_profile_summary("spot-lane-a");
        let right = admissible_same_profile_summary("spot-lane-b");
        let left_fixture = ProofFixture::new("same-profile-left", &proof_json(&left, &[]));
        let right_fixture = ProofFixture::new("same-profile-right", &proof_json(&right, &[]));

        assert_eq!(
            print_root_request(&[left_fixture.path.clone(), right_fixture.path.clone()]),
            Ok(())
        );
    }

    #[test]
    fn root_request_still_rejects_an_exact_duplicate_child() {
        let child = admissible_same_profile_summary("spot-lane-a");
        let fixture = ProofFixture::new("duplicate-child", &proof_json(&child, &[]));

        assert_eq!(
            print_root_request(&[fixture.path.clone(), fixture.path.clone()]),
            Err("InvalidInput(\"recursive lane state ids not sorted unique\")".to_string())
        );
    }

    #[test]
    fn proof_json_boundary_rejects_ambiguous_or_trailing_json() {
        for raw in [
            r#"{"meta":{},"meta":null}"#,
            r#"{"meta":{},"m\u0065ta":null}"#,
            r#"{"outer":{"key":1,"key":2}}"#,
            r#"{"proof":"value"} {}"#,
        ] {
            assert!(parse_proof_json_bytes(raw.as_bytes()).is_err(), "raw={raw}");
        }
    }

    #[test]
    fn proof_json_boundary_is_byte_bounded() {
        let oversized = vec![b' '; MAX_PROOF_JSON_BYTES + 1];
        assert_eq!(
            parse_proof_json_bytes(&oversized).unwrap_err(),
            "proof JSON exceeds byte limit"
        );
    }
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let result = match args.as_slice() {
        [_, mode, image_id_hex] if mode == "summary" => print_summary_request(image_id_hex),
        [_, mode, image_id_hex] if mode == "perps" => print_perps_request(image_id_hex),
        [_, mode, image_id_hex] if mode == "spot" => print_spot_request(image_id_hex),
        [_, mode, image_id_hex] if mode == "zusd" => print_zusd_request(image_id_hex),
        [_, mode, proof_paths @ ..] if mode == "root" && !proof_paths.is_empty() => {
            print_root_request(proof_paths)
        }
        _ => Err("usage: recursive_summary_leaf_smoke summary <image-id-hex> | perps <image-id-hex> | spot <image-id-hex> | zusd <image-id-hex> | root <recursive-leaf-proof-json> [more-leaf-proof-json...]".to_string()),
    };
    if let Err(err) = result {
        eprintln!("{err}");
        std::process::exit(2);
    }
}
