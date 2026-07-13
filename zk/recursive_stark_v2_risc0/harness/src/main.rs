use std::{env, fs, path::PathBuf};

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use risc0_zkvm::{
    compute_image_id, default_executor, default_prover, sha::Digestible, Digest, ExecutorEnv,
    InnerReceipt, MaybePruned, ProverOpts, Receipt, ReceiptClaim,
};
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use tau_state_proof_risc0_recursive_v2_methods::{
    TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ELF, TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID,
};
use tau_state_proof_risc0_shared::{
    compose_recursive_epoch_journal_v1, recursive_asset_delta_root_v1,
    recursive_authority_set_root_v1, recursive_child_journal_hash_v1,
    recursive_child_verification_claim_hash_v1, recursive_child_verifier_id_v1,
    recursive_cross_shard_messages_root_v1, recursive_effect_summary_hash_v1,
    recursive_lane_state_vector_root_v1, recursive_receipt_ids_root_v1,
    recursive_verifier_set_root_v1, validate_recursive_effect_summary_shape_v1,
    RecursiveAssetDeltaRowV1, RecursiveChildDescriptorV1, RecursiveChildEffectV1,
    RecursiveCompositionInputV1, RecursiveCompositionStatementV1, RecursiveEffectSummaryV1,
    PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF, PROOF_TYPE_RECURSIVE_SPOT_LEAF,
    PROOF_TYPE_RECURSIVE_ZUSD_LEAF, RECURSIVE_DOMAIN_SEPARATOR_V1, RECURSIVE_EPOCH_PROFILE_V1,
    RECURSIVE_PERPS_NP_LEAF_PROFILE_V1, RECURSIVE_SPOT_LEAF_PROFILE_V1,
    RECURSIVE_STATEMENT_VERSION_V1, RECURSIVE_STRICT_CROSS_SHARD_MODE_V1,
    RECURSIVE_ZUSD_LEAF_PROFILE_V1,
};
use tau_state_proof_risc0_shared_v2::{
    compose_recursive_node_journal_v2, decode_exact_postcard_v2,
    derive_recursive_node_commitments_v2, preflight_recursive_node_input_v2,
    recursive_immediate_verifier_set_root_v2, recursive_node_journal_bytes_hash_v2,
    recursive_node_verification_claim_hash_v2, recursive_node_verifier_id_v2,
    RecursiveImmediateChildV2, RecursiveNodeBoundsV2, RecursiveNodeChildDescriptorV2,
    RecursiveNodeInputV2, RecursiveNodeJournalV2, RecursiveNodeLevelV2, RecursiveNodeProfileV2,
    RecursiveNodeStatementV2, PROOF_TYPE_RECURSIVE_NODE_V2, RECURSIVE_NODE_DOMAIN_SEPARATOR_V2,
    RECURSIVE_NODE_SCHEMA_VERSION_V2, RECURSIVE_NODE_V2_MAX_CHILD_JOURNAL_BYTES,
    RECURSIVE_NODE_V2_MAX_FLAT_DISCLOSURE_BYTES, RECURSIVE_NODE_V2_MAX_FLAT_LEAVES,
    RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN, RECURSIVE_NODE_V2_MAX_INPUT_BYTES,
    RECURSIVE_NODE_V2_MAX_TOTAL_CHILD_JOURNAL_BYTES,
};

mod evidence_policy;

use evidence_policy::RECURSIVE_V2_LOCAL_NONCLAIMS;

const RECEIPT_CODEC_V1: &str = "risc0_receipt_canonical_serde_json_depth128_v1";
const MAX_PROOF_FILE_BYTES: usize = 16 * 1024 * 1024;
const DEFAULT_INNER_OUTPUT: &str = "/tmp/recursive-stark-v4-inner-node-v2.proof.json";
const DEFAULT_ROOT_OUTPUT: &str = "/tmp/recursive-stark-v4-epoch-root-v2.proof.json";
// These IDs are the byte-pinned v1 authority surface. The harness verifies the
// receipt against the selected ID and also requires matching authenticated
// journal and artifact metadata.
const PINNED_V1_PERPS_NP_LEAF_ID: [u32; 8] = [
    1_193_257_500,
    3_246_547_665,
    1_821_074_706,
    1_301_237_187,
    328_426_728,
    4_111_146_241,
    448_382_032,
    905_639_576,
];
const PINNED_V1_SPOT_LEAF_ID: [u32; 8] = [
    1_106_212_114,
    3_876_807_999,
    30_284_647,
    3_707_445_917,
    3_791_588_337,
    1_758_404_023,
    1_845_828_211,
    57_936_497,
];
const PINNED_V1_ZUSD_LEAF_ID: [u32; 8] = [
    19_873_599,
    252_308_233,
    1_468_752_926,
    1_474_425_934,
    3_641_025_494,
    2_887_030_159,
    2_180_993_514,
    1_290_180_508,
];
#[derive(Clone, Copy)]
struct LeafSurface {
    proof_type: &'static str,
    profile: &'static str,
    image_id: [u32; 8],
}

struct VerifiedLeaf {
    receipt: Receipt,
    disclosure: RecursiveChildEffectV1,
}

struct Options {
    leaf_proofs: Vec<PathBuf>,
    dry_run: bool,
    expect_missing_assumption_reject: bool,
    inner_output: PathBuf,
    root_output: PathBuf,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let options = parse_options(env::args().skip(1))?;
    reject_dev_mode()?;
    validate_aggregate_method()?;

    let mut verified_leaves = options
        .leaf_proofs
        .iter()
        .map(load_verified_leaf)
        .collect::<Result<Vec<_>, _>>()?;
    verified_leaves.sort_by(|left, right| {
        left.disclosure
            .summary
            .lane_id
            .cmp(&right.disclosure.summary.lane_id)
    });
    let leaf_receipt_sha256s = verified_leaves
        .iter()
        .map(|leaf| receipt_sha256(&leaf.receipt))
        .collect::<Result<Vec<_>, _>>()?;
    let leaf_receipts = verified_leaves
        .iter()
        .map(|leaf| leaf.receipt.clone())
        .collect::<Vec<_>>();
    let leaf_disclosures = verified_leaves
        .iter()
        .map(|leaf| leaf.disclosure.clone())
        .collect::<Vec<_>>();
    let aggregate_image_id = TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID;
    let flat_statement = flat_statement_for_leaves(&leaf_disclosures)?;
    let leaf_verifier_ids = canonical_leaf_verifier_ids(&leaf_disclosures);

    let inner_input = bind_node_commitments(RecursiveNodeInputV2 {
        statement: provisional_node_statement(
            RecursiveNodeLevelV2::ClosedSubtreeOverLeaves,
            RecursiveNodeProfileV2::ClosedSubtree,
            aggregate_image_id,
            flat_statement.clone(),
            leaf_verifier_ids.clone(),
        )?,
        allowed_immediate_verifier_ids: leaf_verifier_ids.clone(),
        allowed_flat_leaf_verifier_ids: leaf_verifier_ids,
        allowed_authority_roots: authority_roots(&leaf_disclosures),
        children: leaf_disclosures
            .iter()
            .cloned()
            .map(|child| RecursiveImmediateChildV2::LeafV1 {
                child: Box::new(child),
            })
            .collect(),
    })?;
    let expected_inner = compose_node(&inner_input, "inner node")?;

    if options.expect_missing_assumption_reject {
        execute_missing_assumption_reject(&inner_input, aggregate_image_id)?;
        return Ok(());
    }

    if options.dry_run {
        let inner_journal_bytes = canonical_postcard(&expected_inner, "inner journal")?;
        let root_input = root_input_from_inner(
            aggregate_image_id,
            flat_statement,
            &leaf_disclosures,
            &expected_inner,
            inner_journal_bytes,
        )?;
        let expected_root = compose_node(&root_input, "epoch root")?;
        print_report(
            true,
            &options,
            aggregate_image_id,
            &leaf_receipt_sha256s,
            &expected_inner,
            None,
            &expected_root,
            None,
        )?;
        return Ok(());
    }

    let (inner_receipt, inner_journal) =
        prove_node(&inner_input, &leaf_receipts, &expected_inner, "inner node")?;
    let inner_journal_bytes = inner_receipt.journal.bytes.clone();
    let root_input = root_input_from_inner(
        aggregate_image_id,
        flat_statement,
        &leaf_disclosures,
        &inner_journal,
        inner_journal_bytes,
    )?;
    let expected_root = compose_node(&root_input, "epoch root")?;
    let (root_receipt, root_journal) = prove_node(
        &root_input,
        core::slice::from_ref(&inner_receipt),
        &expected_root,
        "epoch root",
    )?;
    root_receipt
        .verify(aggregate_image_id)
        .map_err(|error| format!("final receipt verification failed: {error}"))?;

    write_receipt_artifact(&options.inner_output, &inner_receipt, &inner_journal)?;
    write_receipt_artifact(&options.root_output, &root_receipt, &root_journal)?;
    print_report(
        false,
        &options,
        aggregate_image_id,
        &leaf_receipt_sha256s,
        &inner_journal,
        Some(&inner_receipt),
        &root_journal,
        Some(&root_receipt),
    )?;
    Ok(())
}

fn parse_options(args: impl Iterator<Item = String>) -> Result<Options, String> {
    let mut leaf_proofs = Vec::new();
    let mut dry_run = false;
    let mut expect_missing_assumption_reject = false;
    let mut inner_output = PathBuf::from(DEFAULT_INNER_OUTPUT);
    let mut root_output = PathBuf::from(DEFAULT_ROOT_OUTPUT);
    let mut args = args.peekable();
    while let Some(arg) = args.next() {
        match arg.as_str() {
            "--dry-run" => dry_run = true,
            "--expect-missing-assumption-reject" => {
                expect_missing_assumption_reject = true;
            }
            "--inner-out" => {
                inner_output = PathBuf::from(
                    args.next()
                        .ok_or_else(|| "--inner-out requires a path".to_string())?,
                );
            }
            "--root-out" => {
                root_output = PathBuf::from(
                    args.next()
                        .ok_or_else(|| "--root-out requires a path".to_string())?,
                );
            }
            _ if arg.starts_with('-') => return Err(format!("unsupported option: {arg}")),
            _ => leaf_proofs.push(PathBuf::from(arg)),
        }
    }
    if dry_run && expect_missing_assumption_reject {
        return Err(
            "--dry-run and --expect-missing-assumption-reject are mutually exclusive".to_string(),
        );
    }
    if leaf_proofs.is_empty()
        || leaf_proofs.len() > RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN as usize
    {
        return Err(format!(
            "expected 1..={} v1 Succinct leaf proof paths",
            RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN
        ));
    }
    Ok(Options {
        leaf_proofs,
        dry_run,
        expect_missing_assumption_reject,
        inner_output,
        root_output,
    })
}

fn reject_dev_mode() -> Result<(), String> {
    let enabled = env::var("RISC0_DEV_MODE").ok().is_some_and(|value| {
        !matches!(
            value.trim().to_ascii_lowercase().as_str(),
            "" | "0" | "false" | "no" | "off"
        )
    });
    if enabled {
        return Err("RISC0_DEV_MODE set: recursive node smoke refuses dev mode".to_string());
    }
    Ok(())
}

fn validate_aggregate_method() -> Result<(), String> {
    if TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ELF.is_empty()
        || TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID
            .iter()
            .all(|word| *word == 0)
    {
        return Err("aggregate v2 method is not embedded".to_string());
    }
    let computed = compute_image_id(TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ELF)
        .map_err(|error| format!("aggregate v2 image ID computation failed: {error}"))?;
    if computed != Digest::from(TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID) {
        return Err("aggregate v2 ELF/image ID mismatch".to_string());
    }
    Ok(())
}

fn leaf_surface(proof_type: &str) -> Result<LeafSurface, String> {
    match proof_type {
        PROOF_TYPE_RECURSIVE_SPOT_LEAF => Ok(LeafSurface {
            proof_type: PROOF_TYPE_RECURSIVE_SPOT_LEAF,
            profile: RECURSIVE_SPOT_LEAF_PROFILE_V1,
            image_id: PINNED_V1_SPOT_LEAF_ID,
        }),
        PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF => Ok(LeafSurface {
            proof_type: PROOF_TYPE_RECURSIVE_PERPS_NP_LEAF,
            profile: RECURSIVE_PERPS_NP_LEAF_PROFILE_V1,
            image_id: PINNED_V1_PERPS_NP_LEAF_ID,
        }),
        PROOF_TYPE_RECURSIVE_ZUSD_LEAF => Ok(LeafSurface {
            proof_type: PROOF_TYPE_RECURSIVE_ZUSD_LEAF,
            profile: RECURSIVE_ZUSD_LEAF_PROFILE_V1,
            image_id: PINNED_V1_ZUSD_LEAF_ID,
        }),
        _ => Err("leaf proof type is not an admissible production v1 recursive leaf".to_string()),
    }
}

fn load_verified_leaf(path: &PathBuf) -> Result<VerifiedLeaf, String> {
    let metadata = fs::metadata(path).map_err(|error| format!("leaf proof metadata: {error}"))?;
    if metadata.len() > MAX_PROOF_FILE_BYTES as u64 {
        return Err("leaf proof file exceeds harness byte limit".to_string());
    }
    let bytes = fs::read(path).map_err(|error| format!("read leaf proof: {error}"))?;
    if bytes.len() > MAX_PROOF_FILE_BYTES {
        return Err("leaf proof file exceeds harness byte limit".to_string());
    }
    let proof: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("leaf proof JSON: {error}"))?;
    let proof_type = proof
        .get("proof_type")
        .and_then(Value::as_str)
        .ok_or_else(|| "leaf proof_type missing".to_string())?;
    let surface = leaf_surface(proof_type)?;
    if surface.image_id.iter().all(|word| *word == 0) {
        return Err("selected leaf method image ID is not embedded".to_string());
    }
    let meta = proof
        .get("meta")
        .and_then(Value::as_object)
        .ok_or_else(|| "leaf proof meta must be an object".to_string())?;
    expect_meta_str(meta, "proof_type", surface.proof_type)?;
    expect_meta_str(meta, "proof_profile", surface.profile)?;
    expect_meta_str(meta, "risc0_image_id", &image_id_hex(surface.image_id))?;
    expect_meta_str(meta, "receipt_codec", RECEIPT_CODEC_V1)?;
    expect_meta_str(meta, "receipt_kind", "succinct")?;

    let proof_b64 = proof
        .get("proof")
        .and_then(Value::as_str)
        .ok_or_else(|| "leaf proof bytes missing".to_string())?;
    if proof_b64.len() > MAX_PROOF_FILE_BYTES.div_ceil(3) * 4 {
        return Err("leaf receipt base64 exceeds harness byte limit".to_string());
    }
    let receipt_bytes = BASE64_STANDARD
        .decode(proof_b64)
        .map_err(|error| format!("leaf proof base64: {error}"))?;
    if receipt_bytes.len() > MAX_PROOF_FILE_BYTES {
        return Err("leaf receipt bytes exceed harness byte limit".to_string());
    }
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)
        .map_err(|error| format!("leaf receipt JSON: {error}"))?;
    let canonical_receipt =
        serde_json::to_vec(&receipt).map_err(|error| format!("leaf receipt encode: {error}"))?;
    if canonical_receipt != receipt_bytes {
        return Err("leaf receipt is not canonical for the declared codec".to_string());
    }
    require_succinct_receipt(&receipt, "leaf")?;
    receipt
        .verify(surface.image_id)
        .map_err(|error| format!("leaf receipt verification failed: {error}"))?;
    verify_receipt_security_meta(meta, &receipt)?;

    let summary: RecursiveEffectSummaryV1 =
        decode_exact_postcard_v2(&receipt.journal.bytes).map_err(v2_error("leaf journal"))?;
    validate_recursive_effect_summary_shape_v1(&summary)
        .map_err(|error| format!("leaf summary rejected: {error:?}"))?;
    if summary.proof_profile != surface.profile || summary.risc0_image_id != surface.image_id {
        return Err("authenticated leaf journal surface binding mismatch".to_string());
    }
    expect_meta_str(meta, "chain_id", &summary.chain_id)?;
    expect_meta_str(meta, "lane_id", &summary.lane_id)?;
    expect_meta_str(meta, "statement_hash", &hex32(&summary.statement_hash))?;
    expect_meta_str(meta, "post_state_root", &hex32(&summary.post_state_root))?;
    let state_hash = proof
        .get("state_hash")
        .and_then(Value::as_str)
        .ok_or_else(|| "leaf state_hash missing".to_string())?;
    if state_hash != hex32(&summary.post_state_root) {
        return Err("leaf state_hash does not match authenticated post-state root".to_string());
    }

    let asset_delta_rows = asset_delta_rows_from_meta(meta)?;
    require_empty_undisclosed_sets(&summary)?;
    let child_journal_bytes = receipt.journal.bytes.clone();
    let child = RecursiveChildEffectV1 {
        descriptor: RecursiveChildDescriptorV1 {
            child_verification_claim_hash: recursive_child_verification_claim_hash_v1(
                &summary.risc0_image_id,
                &child_journal_bytes,
            )
            .map_err(v1_error("leaf claim hash"))?,
            child_journal_hash: recursive_child_journal_hash_v1(&child_journal_bytes)
                .map_err(v1_error("leaf journal hash"))?,
            child_effect_summary_hash: recursive_effect_summary_hash_v1(&summary),
            child_statement_hash: summary.statement_hash,
            child_image_id: summary.risc0_image_id,
            child_verifier_id: recursive_child_verifier_id_v1(
                &summary.risc0_image_id,
                &summary.proof_profile,
            )
            .map_err(v1_error("leaf verifier ID"))?,
            child_profile: summary.proof_profile.clone(),
        },
        child_journal_bytes,
        summary,
        asset_delta_rows,
        outbox_messages: Vec::new(),
        inbox_messages: Vec::new(),
        accepted_receipt_ids: Vec::new(),
        rejected_receipt_ids: Vec::new(),
    };
    Ok(VerifiedLeaf {
        receipt,
        disclosure: child,
    })
}

fn require_empty_undisclosed_sets(summary: &RecursiveEffectSummaryV1) -> Result<(), String> {
    let empty_messages = Vec::new();
    let empty_receipts = Vec::new();
    let empty_message_root = recursive_cross_shard_messages_root_v1(&empty_messages)
        .map_err(v1_error("empty message root"))?;
    let empty_receipt_root =
        recursive_receipt_ids_root_v1(&empty_receipts).map_err(v1_error("empty receipt root"))?;
    if summary.cross_shard_outbox_root != empty_message_root
        || summary.cross_shard_inbox_root != empty_message_root
        || summary.accepted_receipts_root != empty_receipt_root
        || summary.rejected_receipts_root != empty_receipt_root
    {
        return Err(
            "leaf proof metadata does not disclose nonempty messages or receipt IDs; smoke fails closed"
                .to_string(),
        );
    }
    Ok(())
}

fn asset_delta_rows_from_meta(
    meta: &serde_json::Map<String, Value>,
) -> Result<Vec<RecursiveAssetDeltaRowV1>, String> {
    let rows = meta
        .get("asset_delta_rows")
        .and_then(Value::as_array)
        .ok_or_else(|| "leaf meta.asset_delta_rows must be an array".to_string())?;
    let mut decoded = Vec::with_capacity(rows.len());
    for row in rows {
        let row = row
            .as_object()
            .ok_or_else(|| "asset delta row must be an object".to_string())?;
        decoded.push(RecursiveAssetDeltaRowV1 {
            asset_id: required_str(row, "asset_id")?.to_string(),
            debit_atoms: required_u128(row, "debit_atoms")?,
            credit_atoms: required_u128(row, "credit_atoms")?,
            authorized_mint_atoms: required_u128(row, "authorized_mint_atoms")?,
            authorized_burn_atoms: required_u128(row, "authorized_burn_atoms")?,
            authority_root: parse_hex32(required_str(row, "authority_root")?)?,
        });
    }
    let root =
        recursive_asset_delta_root_v1(&decoded).map_err(v1_error("asset delta disclosure root"))?;
    let expected = parse_hex32(required_str(meta, "asset_delta_root")?)?;
    if root != expected {
        return Err("asset delta disclosure root mismatch".to_string());
    }
    Ok(decoded)
}

fn required_str<'a>(
    object: &'a serde_json::Map<String, Value>,
    field: &str,
) -> Result<&'a str, String> {
    object
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{field} missing or not a string"))
}

fn required_u128(object: &serde_json::Map<String, Value>, field: &str) -> Result<u128, String> {
    let value = object
        .get(field)
        .ok_or_else(|| format!("{field} missing"))?;
    if let Some(text) = value.as_str() {
        return text
            .parse::<u128>()
            .map_err(|error| format!("{field} invalid u128: {error}"));
    }
    value
        .as_u64()
        .map(u128::from)
        .ok_or_else(|| format!("{field} must be an unsigned integer or decimal string"))
}

fn verify_receipt_security_meta(
    meta: &serde_json::Map<String, Value>,
    receipt: &Receipt,
) -> Result<(), String> {
    let InnerReceipt::Succinct(inner) = &receipt.inner else {
        return Err("leaf receipt must be succinct".to_string());
    };
    expect_meta_str(
        meta,
        "receipt_verifier_parameters",
        &receipt.metadata.verifier_parameters.to_string(),
    )?;
    expect_meta_str(meta, "receipt_hashfn", &inner.hashfn)?;
    expect_meta_str(meta, "receipt_control_id", &inner.control_id.to_string())?;
    Ok(())
}

fn require_succinct_receipt(receipt: &Receipt, label: &str) -> Result<(), String> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(format!("{label} receipt must be succinct"));
    }
    Ok(())
}

fn flat_statement_for_leaves(
    children: &[RecursiveChildEffectV1],
) -> Result<RecursiveCompositionStatementV1, String> {
    let first = children
        .first()
        .ok_or_else(|| "flat statement requires at least one leaf".to_string())?;
    for child in &children[1..] {
        if child.summary.chain_id != first.summary.chain_id
            || child.summary.epoch_id != first.summary.epoch_id
            || child.summary.public_policy_hash != first.summary.public_policy_hash
            || child.summary.feature_suite_hash != first.summary.feature_suite_hash
            || child.summary.dependency_lock_hash != first.summary.dependency_lock_hash
            || child.summary.toolchain_lock_hash != first.summary.toolchain_lock_hash
        {
            return Err("leaf scope and policy bindings must match".to_string());
        }
    }
    let mut lane_ids = children
        .iter()
        .map(|child| child.summary.lane_id.as_str())
        .collect::<Vec<_>>();
    lane_ids.sort_unstable();
    if lane_ids.windows(2).any(|pair| pair[0] == pair[1]) {
        return Err("leaf lane IDs must be unique".to_string());
    }
    let verifier_ids = canonical_leaf_verifier_ids(children);
    let authority_roots = authority_roots(children);
    let pre_state = children
        .iter()
        .map(|child| (child.summary.lane_id.clone(), child.summary.pre_state_root))
        .collect::<Vec<_>>();
    let post_state = children
        .iter()
        .map(|child| (child.summary.lane_id.clone(), child.summary.post_state_root))
        .collect::<Vec<_>>();
    Ok(RecursiveCompositionStatementV1 {
        domain_separator: RECURSIVE_DOMAIN_SEPARATOR_V1.to_string(),
        schema_version: RECURSIVE_STATEMENT_VERSION_V1,
        chain_id: first.summary.chain_id.clone(),
        epoch_id: first.summary.epoch_id,
        proof_profile: RECURSIVE_EPOCH_PROFILE_V1.to_string(),
        verifier_set_root: recursive_verifier_set_root_v1(&verifier_ids)
            .map_err(v1_error("flat verifier set root"))?,
        allowed_authority_roots_root: recursive_authority_set_root_v1(&authority_roots)
            .map_err(v1_error("flat authority set root"))?,
        public_policy_hash: first.summary.public_policy_hash,
        feature_suite_hash: first.summary.feature_suite_hash,
        dependency_lock_hash: first.summary.dependency_lock_hash,
        toolchain_lock_hash: first.summary.toolchain_lock_hash,
        expected_pre_state_root: recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.pre_state_vector_root.v1",
            &pre_state,
        )
        .map_err(v1_error("flat pre-state vector root"))?,
        expected_post_state_root: recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.post_state_vector_root.v1",
            &post_state,
        )
        .map_err(v1_error("flat post-state vector root"))?,
        conflict_schedule_hash: [12; 32],
        carry_queue_pre_root: [13; 32],
        carry_queue_post_root: [13; 32],
        data_availability_root: [14; 32],
        expected_child_count: u32::try_from(children.len())
            .map_err(|_| "leaf count exceeds u32".to_string())?,
        max_children: RECURSIVE_NODE_V2_MAX_FLAT_LEAVES,
        max_child_journal_bytes: RECURSIVE_NODE_V2_MAX_CHILD_JOURNAL_BYTES,
        max_total_child_journal_bytes: RECURSIVE_NODE_V2_MAX_TOTAL_CHILD_JOURNAL_BYTES,
        max_asset_delta_rows: 16,
        max_cross_shard_messages: 16,
        max_receipt_ids: 16,
        cross_shard_mode: RECURSIVE_STRICT_CROSS_SHARD_MODE_V1.to_string(),
    })
}

fn canonical_leaf_verifier_ids(children: &[RecursiveChildEffectV1]) -> Vec<[u8; 32]> {
    let mut verifier_ids = children
        .iter()
        .map(|child| child.descriptor.child_verifier_id)
        .collect::<Vec<_>>();
    verifier_ids.sort_unstable();
    verifier_ids.dedup();
    verifier_ids
}

fn authority_roots(children: &[RecursiveChildEffectV1]) -> Vec<[u8; 32]> {
    let mut roots = children
        .iter()
        .flat_map(|child| child.asset_delta_rows.iter())
        .map(|row| row.authority_root)
        .filter(|root| *root != [0; 32])
        .collect::<Vec<_>>();
    roots.sort_unstable();
    roots.dedup();
    roots
}

fn provisional_node_statement(
    level: RecursiveNodeLevelV2,
    profile: RecursiveNodeProfileV2,
    image_id: [u32; 8],
    flat_statement: RecursiveCompositionStatementV1,
    mut immediate_verifier_ids: Vec<[u8; 32]>,
) -> Result<RecursiveNodeStatementV2, String> {
    immediate_verifier_ids.sort_unstable();
    immediate_verifier_ids.dedup();
    Ok(RecursiveNodeStatementV2 {
        schema_version: RECURSIVE_NODE_SCHEMA_VERSION_V2,
        domain_separator: RECURSIVE_NODE_DOMAIN_SEPARATOR_V2.to_string(),
        level,
        profile,
        self_image_id: image_id,
        flat_statement,
        immediate_verifier_set_root: recursive_immediate_verifier_set_root_v2(
            &immediate_verifier_ids,
        )
        .map_err(v2_error("immediate verifier set root"))?,
        expected_immediate_child_count: 1,
        expected_flat_leaf_count: 1,
        expected_tree_height: level.tree_height(),
        expected_subtree_node_count: 1,
        expected_assigned_leaf_ids_root: [0xff; 32],
        expected_descendant_claims_root: [0xff; 32],
        expected_descendant_sources_root: [0xff; 32],
        expected_partition_plan_root: [0xff; 32],
        bounds: RecursiveNodeBoundsV2 {
            max_immediate_children: RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN,
            max_flat_leaves: RECURSIVE_NODE_V2_MAX_FLAT_LEAVES,
            max_child_journal_bytes: RECURSIVE_NODE_V2_MAX_CHILD_JOURNAL_BYTES,
            max_total_child_journal_bytes: RECURSIVE_NODE_V2_MAX_TOTAL_CHILD_JOURNAL_BYTES,
            max_flat_disclosure_bytes: RECURSIVE_NODE_V2_MAX_FLAT_DISCLOSURE_BYTES,
        },
    })
}

fn bind_node_commitments(mut input: RecursiveNodeInputV2) -> Result<RecursiveNodeInputV2, String> {
    let commitments = derive_recursive_node_commitments_v2(&input)
        .map_err(v2_error("derive node commitments"))?;
    input.statement.expected_immediate_child_count = commitments.immediate_child_count;
    input.statement.expected_flat_leaf_count = commitments.flat_leaf_count;
    input.statement.expected_tree_height = commitments.tree_height;
    input.statement.expected_subtree_node_count = commitments.subtree_node_count;
    input.statement.expected_assigned_leaf_ids_root = commitments.assigned_leaf_ids_root;
    input.statement.expected_descendant_claims_root = commitments.descendant_claims_root;
    input.statement.expected_descendant_sources_root = commitments.descendant_sources_root;
    input.statement.expected_partition_plan_root = commitments.partition_plan_root;
    let rebound = derive_recursive_node_commitments_v2(&input)
        .map_err(v2_error("rederive node commitments"))?;
    if rebound != commitments {
        return Err("node commitment derivation changed after expectation binding".to_string());
    }
    preflight_recursive_node_input_v2(&input).map_err(v2_error("node preflight"))?;
    Ok(input)
}

fn root_input_from_inner(
    aggregate_image_id: [u32; 8],
    flat_statement: RecursiveCompositionStatementV1,
    leaf_disclosures: &[RecursiveChildEffectV1],
    inner_journal: &RecursiveNodeJournalV2,
    inner_journal_bytes: Vec<u8>,
) -> Result<RecursiveNodeInputV2, String> {
    let node_verifier_id =
        recursive_node_verifier_id_v2(&aggregate_image_id, RecursiveNodeProfileV2::ClosedSubtree)
            .map_err(v2_error("inner node verifier ID"))?;
    let descriptor = RecursiveNodeChildDescriptorV2 {
        child_image_id: aggregate_image_id,
        child_profile: RecursiveNodeProfileV2::ClosedSubtree,
        child_verifier_id: node_verifier_id,
        child_verification_claim_hash: recursive_node_verification_claim_hash_v2(
            &aggregate_image_id,
            &inner_journal_bytes,
        )
        .map_err(v2_error("inner node claim hash"))?,
        child_journal_hash: recursive_node_journal_bytes_hash_v2(&inner_journal_bytes)
            .map_err(v2_error("inner node journal hash"))?,
        child_statement_hash: inner_journal.statement_hash,
    };
    bind_node_commitments(RecursiveNodeInputV2 {
        statement: provisional_node_statement(
            RecursiveNodeLevelV2::EpochRootOverSubtrees,
            RecursiveNodeProfileV2::EpochRoot,
            aggregate_image_id,
            flat_statement,
            vec![node_verifier_id],
        )?,
        allowed_immediate_verifier_ids: vec![node_verifier_id],
        allowed_flat_leaf_verifier_ids: canonical_leaf_verifier_ids(leaf_disclosures),
        allowed_authority_roots: authority_roots(leaf_disclosures),
        children: vec![RecursiveImmediateChildV2::NodeV2 {
            descriptor: Box::new(descriptor),
            journal_bytes: Box::new(inner_journal_bytes),
            flat_leaf_disclosures: Box::new(leaf_disclosures.to_vec()),
        }],
    })
}

fn compose_node(
    input: &RecursiveNodeInputV2,
    label: &str,
) -> Result<RecursiveNodeJournalV2, String> {
    let journal =
        compose_recursive_node_journal_v2(input).map_err(v2_error(&format!("compose {label}")))?;
    let mut flat_children = Vec::new();
    for child in &input.children {
        match child {
            RecursiveImmediateChildV2::LeafV1 { child } => {
                flat_children.push(child.as_ref().clone());
            }
            RecursiveImmediateChildV2::NodeV2 {
                flat_leaf_disclosures,
                ..
            } => flat_children.extend(flat_leaf_disclosures.iter().cloned()),
        }
    }
    let flat_input = RecursiveCompositionInputV1 {
        statement: input.statement.flat_statement.clone(),
        allowed_verifier_ids: input.allowed_flat_leaf_verifier_ids.clone(),
        allowed_authority_roots: input.allowed_authority_roots.clone(),
        children: flat_children,
    };
    let direct_flat = compose_recursive_epoch_journal_v1(&flat_input)
        .map_err(v1_error(&format!("direct flat projection for {label}")))?;
    if direct_flat != journal.flat_v1_projection {
        return Err(format!("{label} flat v1 projection mismatch"));
    }
    Ok(journal)
}

fn prove_node(
    input: &RecursiveNodeInputV2,
    assumptions: &[Receipt],
    expected_journal: &RecursiveNodeJournalV2,
    label: &str,
) -> Result<(Receipt, RecursiveNodeJournalV2), String> {
    let (input_len, input_bytes) = encoded_node_input(input, label)?;
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[input_len]).write_slice(&input_bytes);
    for assumption in assumptions {
        require_succinct_receipt(assumption, &format!("{label} assumption"))?;
        builder.add_assumption(assumption.clone());
    }
    let executor_env = builder
        .build()
        .map_err(|error| format!("{label} executor environment: {error}"))?;
    let prove_info = default_prover()
        .prove_with_opts(
            executor_env,
            TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("{label} proving failed: {error}"))?;
    let receipt = prove_info.receipt;
    require_succinct_receipt(&receipt, label)?;
    receipt
        .verify(TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID)
        .map_err(|error| format!("{label} receipt verification failed: {error}"))?;
    let journal: RecursiveNodeJournalV2 = decode_exact_postcard_v2(&receipt.journal.bytes)
        .map_err(v2_error(&format!("{label} authenticated journal")))?;
    let expected_bytes =
        canonical_postcard(expected_journal, &format!("expected {label} journal"))?;
    if receipt.journal.bytes != expected_bytes {
        return Err(format!("{label} journal byte binding mismatch"));
    }
    Ok((receipt, journal))
}

fn encoded_node_input(input: &RecursiveNodeInputV2, label: &str) -> Result<(u32, Vec<u8>), String> {
    let input_bytes = canonical_postcard(input, &format!("{label} input"))?;
    if input_bytes.is_empty() || input_bytes.len() > RECURSIVE_NODE_V2_MAX_INPUT_BYTES as usize {
        return Err(format!("{label} input byte length unsupported"));
    }
    let input_len = u32::try_from(input_bytes.len())
        .map_err(|_| format!("{label} input length exceeds u32"))?;
    Ok((input_len, input_bytes))
}

fn expected_missing_assumption_reason(input: &RecursiveNodeInputV2) -> Result<String, String> {
    let claim = preflight_recursive_node_input_v2(input)
        .map_err(v2_error("missing-assumption preflight"))?
        .into_iter()
        .next()
        .ok_or_else(|| "recursive immediate child set empty".to_string())?;
    let journal_digest = claim.journal_bytes.as_slice().digest();
    let claim_digest = ReceiptClaim::ok(
        claim.image_id,
        MaybePruned::<Vec<u8>>::Pruned(journal_digest),
    )
    .digest();
    Ok(format!(
        "sys_verify_integrity: no receipt found to resolve assumption: claim digest {claim_digest}, control root {}",
        Digest::ZERO
    ))
}

fn execute_missing_assumption_reject(
    input: &RecursiveNodeInputV2,
    aggregate_image_id: [u32; 8],
) -> Result<(), String> {
    let (input_len, input_bytes) = encoded_node_input(input, "missing-assumption inner node")?;
    let executor_env = ExecutorEnv::builder()
        .write_slice(&[input_len])
        .write_slice(&input_bytes)
        .build()
        .map_err(|error| format!("missing-assumption executor environment: {error}"))?;
    let expected_reason = expected_missing_assumption_reason(input)?;
    match default_executor().execute(executor_env, TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ELF) {
        Ok(_) => Err("aggregate v2 execution accepted a missing child assumption".to_string()),
        Err(error)
            if error
                .chain()
                .any(|cause| cause.to_string() == expected_reason) =>
        {
            println!(
                "{}",
                json!({
                    "aggregate_v2_image_id": image_id_hex(aggregate_image_id),
                    "ok": true,
                    "status": "missing_child_assumption_rejected",
                })
            );
            Ok(())
        }
        Err(error) => Err(format!(
            "aggregate v2 execution failed without the exact missing-assumption reason: {error:#}"
        )),
    }
}

fn write_receipt_artifact(
    path: &PathBuf,
    receipt: &Receipt,
    journal: &RecursiveNodeJournalV2,
) -> Result<(), String> {
    let canonical_receipt =
        serde_json::to_vec(receipt).map_err(|error| format!("receipt artifact encode: {error}"))?;
    let journal_bytes = canonical_postcard(journal, "receipt artifact journal")?;
    let artifact = json!({
        "schema": "tau_recursive_node_v2_receipt_artifact",
        "schema_version": 2,
        "proof_type": PROOF_TYPE_RECURSIVE_NODE_V2,
        "receipt_codec": RECEIPT_CODEC_V1,
        "receipt_kind": "succinct",
        "risc0_image_id": image_id_hex(TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID),
        "receipt_sha256": sha256_hex(&canonical_receipt),
        "journal_sha256": sha256_hex(&journal_bytes),
        "protocol_journal_hash": hex32(
            &recursive_node_journal_bytes_hash_v2(&journal_bytes)
                .map_err(v2_error("artifact journal hash"))?
        ),
        "journal": journal,
        "proof": BASE64_STANDARD.encode(canonical_receipt),
        "nonclaims": RECURSIVE_V2_LOCAL_NONCLAIMS,
    });
    let bytes = serde_json::to_vec(&artifact)
        .map_err(|error| format!("receipt artifact JSON encode: {error}"))?;
    fs::write(path, bytes).map_err(|error| format!("write {}: {error}", path.display()))
}

#[allow(clippy::too_many_arguments)]
fn print_report(
    dry_run: bool,
    options: &Options,
    aggregate_image_id: [u32; 8],
    leaf_receipt_sha256s: &[String],
    inner_journal: &RecursiveNodeJournalV2,
    inner_receipt: Option<&Receipt>,
    root_journal: &RecursiveNodeJournalV2,
    root_receipt: Option<&Receipt>,
) -> Result<(), String> {
    let journal_report = |journal: &RecursiveNodeJournalV2| -> Result<Value, String> {
        let bytes = canonical_postcard(journal, "report journal")?;
        Ok(json!({
            "profile": journal.profile,
            "statement_hash": hex32(&journal.statement_hash),
            "aggregation_scope_hash": hex32(&journal.aggregation_scope_hash),
            "journal_sha256": sha256_hex(&bytes),
            "protocol_journal_hash": hex32(
                &recursive_node_journal_bytes_hash_v2(&bytes)
                    .map_err(v2_error("report journal hash"))?
            ),
            "tree_height": journal.tree_height,
            "immediate_child_count": journal.immediate_child_count,
            "flat_leaf_count": journal.flat_leaf_count,
            "subtree_node_count": journal.subtree_node_count,
            "leaf_disclosures_root": hex32(&journal.leaf_disclosures_root),
            "assigned_leaf_ids_root": hex32(&journal.assigned_leaf_ids_root),
            "descendant_claims_root": hex32(&journal.descendant_claims_root),
            "partition_plan_root": hex32(&journal.partition_plan_root),
            "flat_v1_statement_hash": hex32(&journal.flat_v1_projection.statement_hash),
            "flat_v1_post_state_root": hex32(&journal.flat_v1_projection.post_state_root),
        }))
    };
    let receipt_hash = |receipt: Option<&Receipt>| -> Result<Value, String> {
        receipt
            .map(receipt_sha256)
            .transpose()
            .map(|value| value.map(Value::String).unwrap_or(Value::Null))
    };
    println!(
        "{}",
        serde_json::to_string_pretty(&json!({
            "ok": true,
            "dry_run": dry_run,
            "aggregate_v2_image_id": image_id_hex(aggregate_image_id),
            "input_leaf_count": leaf_receipt_sha256s.len(),
            "input_leaf_receipt_sha256s": leaf_receipt_sha256s,
            "inner": journal_report(inner_journal)?,
            "inner_receipt_sha256": receipt_hash(inner_receipt)?,
            "epoch_root": journal_report(root_journal)?,
            "epoch_root_receipt_sha256": receipt_hash(root_receipt)?,
            "inner_artifact": if dry_run { Value::Null } else { Value::String(options.inner_output.display().to_string()) },
            "epoch_root_artifact": if dry_run { Value::Null } else { Value::String(options.root_output.display().to_string()) },
            "nonclaims": RECURSIVE_V2_LOCAL_NONCLAIMS,
        }))
        .map_err(|error| format!("report JSON encode: {error}"))?
    );
    Ok(())
}

fn receipt_sha256(receipt: &Receipt) -> Result<String, String> {
    let bytes = serde_json::to_vec(receipt)
        .map_err(|error| format!("receipt hash serialization failed: {error}"))?;
    Ok(sha256_hex(&bytes))
}

fn canonical_postcard<T: serde::Serialize>(value: &T, label: &str) -> Result<Vec<u8>, String> {
    postcard::to_allocvec(value).map_err(|error| format!("{label} postcard encode: {error}"))
}

fn parse_hex32(value: &str) -> Result<[u8; 32], String> {
    let bytes = hex::decode(value).map_err(|error| format!("invalid hex32: {error}"))?;
    bytes
        .try_into()
        .map_err(|_| "hex32 must decode to 32 bytes".to_string())
}

fn expect_meta_str(
    meta: &serde_json::Map<String, Value>,
    field: &str,
    expected: &str,
) -> Result<(), String> {
    let actual = required_str(meta, field)?;
    if actual != expected {
        return Err(format!("leaf meta.{field} mismatch"));
    }
    Ok(())
}

fn image_id_hex(image_id: [u32; 8]) -> String {
    Digest::from(image_id).to_string()
}

fn hex32(value: &[u8; 32]) -> String {
    hex::encode(value)
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn v1_error(
    label: &str,
) -> impl FnOnce(tau_state_proof_risc0_shared::TransitionError) -> String + '_ {
    move |error| format!("{label}: {error:?}")
}

fn v2_error(
    label: &str,
) -> impl FnOnce(tau_state_proof_risc0_shared_v2::RecursiveNodeErrorV2) -> String + '_ {
    move |error| format!("{label}: {error:?}")
}

#[cfg(test)]
fn decode_exact_postcard<T>(bytes: &[u8], label: &str) -> Result<T, String>
where
    T: serde::de::DeserializeOwned + serde::Serialize,
{
    decode_exact_postcard_v2(bytes).map_err(v2_error(label))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn production_leaf_surface_policy_rejects_summary_and_unknown_profiles() {
        assert_eq!(
            leaf_surface(PROOF_TYPE_RECURSIVE_SPOT_LEAF)
                .unwrap()
                .profile,
            RECURSIVE_SPOT_LEAF_PROFILE_V1
        );
        assert!(leaf_surface("risc0.zenodex_recursive_summary_leaf.v1").is_err());
        assert!(leaf_surface("risc0.unknown.v1").is_err());
    }

    #[test]
    fn option_parser_accepts_bounded_fanout_and_explicit_outputs() {
        let options = parse_options(
            [
                "leaf.json",
                "--dry-run",
                "--inner-out",
                "inner.json",
                "--root-out",
                "root.json",
            ]
            .into_iter()
            .map(str::to_string),
        )
        .unwrap();
        assert!(options.dry_run);
        assert!(!options.expect_missing_assumption_reject);
        assert_eq!(options.leaf_proofs, vec![PathBuf::from("leaf.json")]);
        assert_eq!(options.inner_output, PathBuf::from("inner.json"));
        assert_eq!(options.root_output, PathBuf::from("root.json"));
        let pair =
            parse_options(["left.json", "right.json"].into_iter().map(str::to_string)).unwrap();
        assert_eq!(pair.leaf_proofs.len(), 2);
        let over_limit = (0..=RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN)
            .map(|index| format!("leaf-{index}.json"));
        assert!(parse_options(over_limit).is_err());
        assert!(parse_options(
            [
                "leaf.json",
                "--dry-run",
                "--expect-missing-assumption-reject",
            ]
            .into_iter()
            .map(str::to_string),
        )
        .is_err());
    }

    #[test]
    fn exact_postcard_decoder_rejects_trailing_bytes() {
        let value = vec![1u32, 2, 3];
        let mut bytes = canonical_postcard(&value, "test vector").unwrap();
        let decoded: Vec<u32> = decode_exact_postcard(&bytes, "test vector").unwrap();
        assert_eq!(decoded, value);
        bytes.push(0);
        assert!(decode_exact_postcard::<Vec<u32>>(&bytes, "test vector").is_err());
    }
}
