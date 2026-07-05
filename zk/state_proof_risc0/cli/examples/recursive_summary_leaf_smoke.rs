use std::{env, fs};

use serde_json::{json, Value};
use tau_state_proof_risc0_shared::{
    recursive_asset_delta_root_v1, recursive_authority_set_root_v1,
    recursive_child_journal_hash_v1, recursive_child_verification_claim_hash_v1,
    recursive_child_verifier_id_v1, recursive_cross_shard_messages_root_v1,
    recursive_effect_summary_hash_v1, recursive_receipt_ids_root_v1, recursive_vector_root_v1,
    recursive_verifier_set_root_v1, RecursiveChildDescriptorV1, RecursiveChildEffectV1,
    RecursiveCompositionInputV1, RecursiveCompositionStatementV1, RecursiveEffectSummaryV1,
    RECURSIVE_DOMAIN_SEPARATOR_V1, RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
    RECURSIVE_STATEMENT_VERSION_V1, RECURSIVE_STRICT_CROSS_SHARD_MODE_V1,
    RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES, RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
};

fn root(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn hex_bytes(bytes: &[u8]) -> String {
    hex::encode(bytes)
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
        *slot = u32::from_be_bytes(chunk.try_into().expect("chunk length is fixed"));
    }
    Ok(out)
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
            "recursive_summary": summary,
        }))
        .map_err(|e| format!("summary request json: {e}"))?
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

fn print_root_request(proof_path: &str) -> Result<(), String> {
    let proof_json: Value = serde_json::from_str(
        &fs::read_to_string(proof_path).map_err(|e| format!("read proof json: {e}"))?,
    )
    .map_err(|e| format!("proof json: {e}"))?;
    let proof = proof_json["proof"]
        .as_str()
        .ok_or("proof field missing")?
        .to_string();
    let summary = summary_from_meta(&proof_json["meta"])?;
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
        asset_delta_rows: Vec::new(),
        outbox_messages: Vec::new(),
        inbox_messages: Vec::new(),
        accepted_receipt_ids: Vec::new(),
        rejected_receipt_ids: Vec::new(),
    };
    let verifier_ids = vec![child_verifier_id];
    let authority_roots = vec![summary.public_policy_hash];
    let expected_pre_state_root = recursive_vector_root_v1(
        b"zenodex.risc0.recursive.pre_state_vector_root.v1",
        &[summary.pre_state_root],
    )
    .map_err(|e| format!("{e:?}"))?;
    let expected_post_state_root = recursive_vector_root_v1(
        b"zenodex.risc0.recursive.post_state_vector_root.v1",
        &[summary.post_state_root],
    )
    .map_err(|e| format!("{e:?}"))?;
    let input = RecursiveCompositionInputV1 {
        statement: RecursiveCompositionStatementV1 {
            domain_separator: RECURSIVE_DOMAIN_SEPARATOR_V1.to_string(),
            schema_version: RECURSIVE_STATEMENT_VERSION_V1,
            chain_id: summary.chain_id.clone(),
            epoch_id: summary.epoch_id,
            proof_profile: summary.proof_profile.clone(),
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
            expected_child_count: 1,
            max_children: 8,
            max_child_journal_bytes: RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES,
            max_total_child_journal_bytes: RECURSIVE_SUMMARY_LEAF_MAX_INPUT_BYTES,
            max_asset_delta_rows: 16,
            max_cross_shard_messages: 16,
            max_receipt_ids: 16,
            cross_shard_mode: RECURSIVE_STRICT_CROSS_SHARD_MODE_V1.to_string(),
        },
        allowed_verifier_ids: verifier_ids,
        allowed_authority_roots: authority_roots,
        children: vec![child],
    };
    println!(
        "{}",
        serde_json::to_string(&json!({
            "schema": "tau_state_proof_request",
            "schema_version": 1,
            "state_hash": hex_bytes(&expected_post_state_root),
            "proof_type": "risc0.zenodex_recursive_epoch.v1",
            "recursive_input": input,
            "child_proofs": [proof],
        }))
        .map_err(|e| format!("root request json: {e}"))?
    );
    Ok(())
}

fn main() {
    let args: Vec<String> = env::args().collect();
    let result = match args.as_slice() {
        [_, mode, image_id_hex] if mode == "summary" => print_summary_request(image_id_hex),
        [_, mode, proof_path] if mode == "root" => print_root_request(proof_path),
        _ => Err("usage: recursive_summary_leaf_smoke summary <image-id-hex> | root <summary-leaf-proof-json>".to_string()),
    };
    if let Err(err) = result {
        eprintln!("{err}");
        std::process::exit(2);
    }
}
