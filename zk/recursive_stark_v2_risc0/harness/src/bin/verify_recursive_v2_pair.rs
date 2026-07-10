use std::{env, fs, path::Path};

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use risc0_zkvm::{Digest, InnerReceipt, Receipt};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use tau_state_proof_risc0_recursive_v2_methods::TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID;
use tau_state_proof_risc0_shared_v2::{
    decode_exact_postcard_v2, recursive_immediate_verifier_set_root_v2,
    recursive_node_journal_bytes_hash_v2, recursive_node_verification_claim_hash_v2,
    recursive_node_verifier_id_v2, RecursiveNodeJournalV2, RecursiveNodeLevelV2,
    RecursiveNodeProfileV2, PROOF_TYPE_RECURSIVE_NODE_V2, RECURSIVE_NODE_DOMAIN_SEPARATOR_V2,
    RECURSIVE_NODE_JOURNAL_VERSION_V2,
};

#[path = "../evidence_policy.rs"]
mod evidence_policy;

use evidence_policy::has_exact_recursive_v2_local_nonclaims;

const ARTIFACT_SCHEMA: &str = "tau_recursive_node_v2_receipt_artifact";
const ARTIFACT_SCHEMA_VERSION: u32 = 2;
const RECEIPT_CODEC: &str = "risc0_receipt_canonical_serde_json_depth128_v1";
const MAX_ARTIFACT_BYTES: usize = 16 * 1024 * 1024;
const IMMEDIATE_CLAIMS_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.immediate_child_claims_root.v2";
const IMMEDIATE_JOURNALS_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.immediate_child_journals_root.v2";

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ReceiptArtifact {
    schema: String,
    schema_version: u32,
    proof_type: String,
    receipt_codec: String,
    receipt_kind: String,
    risc0_image_id: String,
    receipt_sha256: String,
    journal_sha256: String,
    protocol_journal_hash: String,
    journal: RecursiveNodeJournalV2,
    proof: String,
    nonclaims: Vec<String>,
}

struct VerifiedArtifact {
    journal: RecursiveNodeJournalV2,
    journal_bytes: Vec<u8>,
    receipt_sha256: String,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let mut args = env::args().skip(1);
    let inner_path = args.next().ok_or_else(|| {
        "usage: verify_recursive_v2_pair <inner-artifact> <root-artifact>".to_string()
    })?;
    let root_path = args.next().ok_or_else(|| {
        "usage: verify_recursive_v2_pair <inner-artifact> <root-artifact>".to_string()
    })?;
    if args.next().is_some() {
        return Err("verify_recursive_v2_pair accepts exactly two artifacts".to_string());
    }

    let inner = verify_artifact(Path::new(&inner_path))?;
    let root = verify_artifact(Path::new(&root_path))?;
    verify_pair_binding(&inner, &root)?;
    println!(
        "{}",
        json!({
            "aggregate_v2_image_id": image_id_hex(),
            "inner_receipt_sha256": inner.receipt_sha256,
            "ok": true,
            "root_receipt_sha256": root.receipt_sha256,
            "status": "recursive_v2_pair_verified",
        })
    );
    Ok(())
}

fn verify_artifact(path: &Path) -> Result<VerifiedArtifact, String> {
    let metadata =
        fs::metadata(path).map_err(|error| format!("{} metadata: {error}", path.display()))?;
    if !metadata.is_file() || metadata.len() > MAX_ARTIFACT_BYTES as u64 {
        return Err(format!("{} is not a bounded regular file", path.display()));
    }
    let bytes = fs::read(path).map_err(|error| format!("{} read: {error}", path.display()))?;
    if bytes.len() > MAX_ARTIFACT_BYTES {
        return Err(format!(
            "{} exceeds the artifact byte limit",
            path.display()
        ));
    }
    let canonical_value: Value = serde_json::from_slice(&bytes)
        .map_err(|error| format!("{} JSON: {error}", path.display()))?;
    let canonical_bytes = serde_json::to_vec(&canonical_value)
        .map_err(|error| format!("{} canonical JSON: {error}", path.display()))?;
    if canonical_bytes != bytes {
        return Err(format!("{} is not canonical JSON", path.display()));
    }
    let artifact: ReceiptArtifact = serde_json::from_slice(&bytes)
        .map_err(|error| format!("{} artifact schema: {error}", path.display()))?;
    validate_artifact_header(&artifact)?;

    if artifact.proof.len() > MAX_ARTIFACT_BYTES.div_ceil(3) * 4 {
        return Err("receipt base64 exceeds the byte limit".to_string());
    }
    let receipt_bytes = BASE64_STANDARD
        .decode(&artifact.proof)
        .map_err(|error| format!("receipt base64: {error}"))?;
    if receipt_bytes.len() > MAX_ARTIFACT_BYTES
        || BASE64_STANDARD.encode(&receipt_bytes) != artifact.proof
    {
        return Err("receipt base64 is not canonical and bounded".to_string());
    }
    let receipt: Receipt =
        serde_json::from_slice(&receipt_bytes).map_err(|error| format!("receipt JSON: {error}"))?;
    let canonical_receipt =
        serde_json::to_vec(&receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if canonical_receipt != receipt_bytes {
        return Err("receipt JSON is not canonical".to_string());
    }
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err("receipt is not succinct".to_string());
    }
    receipt
        .verify(TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID)
        .map_err(|error| format!("receipt verification failed: {error}"))?;

    let receipt_sha256 = sha256_hex(&receipt_bytes);
    if receipt_sha256 != artifact.receipt_sha256 {
        return Err("receipt SHA-256 mismatch".to_string());
    }
    let journal: RecursiveNodeJournalV2 = decode_exact_postcard_v2(&receipt.journal.bytes)
        .map_err(|error| format!("authenticated journal decode: {error:?}"))?;
    let canonical_journal =
        postcard::to_allocvec(&journal).map_err(|error| format!("journal encode: {error}"))?;
    let artifact_journal = postcard::to_allocvec(&artifact.journal)
        .map_err(|error| format!("artifact journal encode: {error}"))?;
    if canonical_journal != receipt.journal.bytes || canonical_journal != artifact_journal {
        return Err("artifact journal does not match the authenticated journal".to_string());
    }
    if sha256_hex(&canonical_journal) != artifact.journal_sha256 {
        return Err("journal SHA-256 mismatch".to_string());
    }
    let protocol_hash = recursive_node_journal_bytes_hash_v2(&canonical_journal)
        .map_err(|error| format!("protocol journal hash: {error:?}"))?;
    if hex32(&protocol_hash) != artifact.protocol_journal_hash {
        return Err("protocol journal hash mismatch".to_string());
    }
    validate_authenticated_journal(&journal)?;
    Ok(VerifiedArtifact {
        journal,
        journal_bytes: canonical_journal,
        receipt_sha256,
    })
}

fn validate_artifact_header(artifact: &ReceiptArtifact) -> Result<(), String> {
    if artifact.schema != ARTIFACT_SCHEMA
        || artifact.schema_version != ARTIFACT_SCHEMA_VERSION
        || artifact.proof_type != PROOF_TYPE_RECURSIVE_NODE_V2
        || artifact.receipt_codec != RECEIPT_CODEC
        || artifact.receipt_kind != "succinct"
        || artifact.risc0_image_id != image_id_hex()
        || !has_exact_recursive_v2_local_nonclaims(&artifact.nonclaims)
    {
        return Err("receipt artifact header mismatch".to_string());
    }
    Ok(())
}

fn validate_authenticated_journal(journal: &RecursiveNodeJournalV2) -> Result<(), String> {
    if journal.journal_version != RECURSIVE_NODE_JOURNAL_VERSION_V2
        || journal.proof_type != PROOF_TYPE_RECURSIVE_NODE_V2
        || journal.domain_separator != RECURSIVE_NODE_DOMAIN_SEPARATOR_V2
        || journal.self_image_id != TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID
        || journal.immediate_child_count != 1
        || journal.flat_leaf_count != 1
    {
        return Err("authenticated journal surface mismatch".to_string());
    }
    Ok(())
}

fn verify_pair_binding(inner: &VerifiedArtifact, root: &VerifiedArtifact) -> Result<(), String> {
    if inner.journal.level != RecursiveNodeLevelV2::ClosedSubtreeOverLeaves
        || inner.journal.profile != RecursiveNodeProfileV2::ClosedSubtree
        || inner.journal.tree_height != 1
        || root.journal.level != RecursiveNodeLevelV2::EpochRootOverSubtrees
        || root.journal.profile != RecursiveNodeProfileV2::EpochRoot
        || root.journal.tree_height != 2
    {
        return Err("recursive pair level/profile mismatch".to_string());
    }
    if root.journal.subtree_node_count
        != inner
            .journal
            .subtree_node_count
            .checked_add(1)
            .ok_or_else(|| "subtree node count overflow".to_string())?
        || root.journal.aggregation_scope_hash != inner.journal.aggregation_scope_hash
        || root.journal.flat_v1_projection != inner.journal.flat_v1_projection
        || root.journal.flat_leaf_count != inner.journal.flat_leaf_count
        || root.journal.leaf_disclosures_root != inner.journal.leaf_disclosures_root
        || root.journal.assigned_leaf_ids_root != inner.journal.assigned_leaf_ids_root
        || root.journal.descendant_claims_root != inner.journal.descendant_claims_root
        || root.journal.descendant_sources_root != inner.journal.descendant_sources_root
    {
        return Err("recursive pair flat projection or leaf-set binding mismatch".to_string());
    }

    let inner_claim = recursive_node_verification_claim_hash_v2(
        &TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID,
        &inner.journal_bytes,
    )
    .map_err(|error| format!("inner claim hash: {error:?}"))?;
    let inner_journal = recursive_node_journal_bytes_hash_v2(&inner.journal_bytes)
        .map_err(|error| format!("inner journal hash: {error:?}"))?;
    if root.journal.immediate_child_claims_root
        != singleton_root(IMMEDIATE_CLAIMS_ROOT_DOMAIN, &inner_claim)
        || root.journal.immediate_child_journals_root
            != singleton_root(IMMEDIATE_JOURNALS_ROOT_DOMAIN, &inner_journal)
    {
        return Err("epoch root does not bind the supplied inner receipt journal".to_string());
    }
    let node_verifier_id = recursive_node_verifier_id_v2(
        &TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID,
        RecursiveNodeProfileV2::ClosedSubtree,
    )
    .map_err(|error| format!("inner verifier ID: {error:?}"))?;
    let verifier_root = recursive_immediate_verifier_set_root_v2(&[node_verifier_id])
        .map_err(|error| format!("inner verifier set root: {error:?}"))?;
    if root.journal.immediate_verifier_set_root != verifier_root {
        return Err("epoch root immediate verifier set mismatch".to_string());
    }
    Ok(())
}

fn singleton_root(domain: &[u8], value: &[u8; 32]) -> [u8; 32] {
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(1u32.to_be_bytes());
    hasher.update(value);
    hasher.finalize().into()
}

fn image_id_hex() -> String {
    Digest::from(TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID).to_string()
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn hex32(value: &[u8; 32]) -> String {
    hex::encode(value)
}
