use std::{env, fs, path::Path};

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use risc0_zkvm::{Digest, InnerReceipt, Receipt};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use tau_state_proof_risc0_recursive_v2_methods::TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID;
use tau_state_proof_risc0_shared::{
    recursive_child_journal_hash_v1, recursive_child_verification_claim_hash_v1,
    recursive_child_verifier_id_v1, validate_recursive_effect_summary_shape_v1,
    RecursiveEffectSummaryV1, PROOF_TYPE_RECURSIVE_SPOT_LEAF, PROOF_TYPE_RECURSIVE_ZUSD_LEAF,
    RECURSIVE_SPOT_LEAF_PROFILE_V1, RECURSIVE_ZUSD_LEAF_PROFILE_V1,
};
use tau_state_proof_risc0_shared_v2::{
    decode_exact_postcard_v2, recursive_assigned_leaf_id_v2, recursive_assigned_leaf_ids_root_v2,
    recursive_descendant_claims_root_v2, recursive_descendant_sources_root_v2,
    recursive_immediate_verifier_set_root_v2, recursive_leaf_source_id_v2,
    recursive_node_journal_bytes_hash_v2, recursive_node_verification_claim_hash_v2,
    recursive_node_verifier_id_v2, RecursiveNodeJournalV2, RecursiveNodeLevelV2,
    RecursiveNodeProfileV2, PROOF_TYPE_RECURSIVE_NODE_V2, RECURSIVE_NODE_DOMAIN_SEPARATOR_V2,
    RECURSIVE_NODE_JOURNAL_VERSION_V2,
};

#[path = "../evidence_policy.rs"]
mod evidence_policy;

use evidence_policy::has_exact_recursive_v2_local_nonclaims;
const ARTIFACT_SCHEMA: &str = "tau_recursive_node_v2_receipt_artifact";
const RECEIPT_CODEC: &str = "risc0_receipt_canonical_serde_json_depth128_v1";
const MAX_ARTIFACT_BYTES: usize = 16 * 1024 * 1024;
const MAX_ARTIFACT_BYTES_U64: u64 = 16 * 1024 * 1024;
const IMMEDIATE_CLAIMS_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.immediate_child_claims_root.v2";
const IMMEDIATE_JOURNALS_ROOT_DOMAIN: &[u8] =
    b"zenodex.risc0.recursive.immediate_child_journals_root.v2";

const SPOT_LEAF_ID: [u32; 8] = [
    1_106_212_114,
    3_876_807_999,
    30_284_647,
    3_707_445_917,
    3_791_588_337,
    1_758_404_023,
    1_845_828_211,
    57_936_497,
];
const ZUSD_LEAF_ID: [u32; 8] = [
    19_873_599,
    252_308_233,
    1_468_752_926,
    1_474_425_934,
    3_641_025_494,
    2_887_030_159,
    2_180_993_514,
    1_290_180_508,
];

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LeafKind {
    Spot,
    Zusd,
}

#[derive(Clone, Copy)]
struct LeafSurface {
    kind: LeafKind,
    proof_type: &'static str,
    profile: &'static str,
    lane_kind: &'static str,
    image_id: [u32; 8],
}

struct VerifiedLeaf {
    kind: LeafKind,
    profile: String,
    image_id: [u32; 8],
    lane_kind: String,
    lane_id: String,
    statement_hash: [u8; 32],
    journal_bytes: Vec<u8>,
    receipt_sha256: String,
}

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
    let first_leaf_path = args.next().ok_or_else(|| usage().to_string())?;
    let second_leaf_path = args.next().ok_or_else(|| usage().to_string())?;
    let inner_path = args.next().ok_or_else(|| usage().to_string())?;
    let root_path = args.next().ok_or_else(|| usage().to_string())?;
    if args.next().is_some() {
        return Err(usage().to_string());
    }

    let mut leaves = vec![
        verify_leaf(Path::new(&first_leaf_path))?,
        verify_leaf(Path::new(&second_leaf_path))?,
    ];
    leaves.sort_by(|left, right| left.lane_id.cmp(&right.lane_id));
    validate_two_leaf_policy(&leaves)?;
    let inner = verify_artifact(Path::new(&inner_path))?;
    let root = verify_artifact(Path::new(&root_path))?;
    verify_pair(&leaves, &inner, &root)?;
    println!(
        "{}",
        json!({
            "aggregate_v2_image_id": image_id_hex(),
            "leaf_receipt_sha256s": leaves.iter().map(|leaf| leaf.receipt_sha256.as_str()).collect::<Vec<_>>(),
            "inner_receipt_sha256": inner.receipt_sha256,
            "ok": true,
            "root_receipt_sha256": root.receipt_sha256,
            "status": "recursive_v2_two_leaf_pair_verified",
        })
    );
    Ok(())
}

fn usage() -> &'static str {
    "usage: verify_recursive_v2_two_leaf_pair <spot-or-zusd-leaf> <other-leaf> <inner> <root>"
}

fn leaf_surface(proof_type: &str) -> Result<LeafSurface, String> {
    match proof_type {
        PROOF_TYPE_RECURSIVE_SPOT_LEAF => Ok(LeafSurface {
            kind: LeafKind::Spot,
            proof_type: PROOF_TYPE_RECURSIVE_SPOT_LEAF,
            profile: RECURSIVE_SPOT_LEAF_PROFILE_V1,
            lane_kind: "spot",
            image_id: SPOT_LEAF_ID,
        }),
        PROOF_TYPE_RECURSIVE_ZUSD_LEAF => Ok(LeafSurface {
            kind: LeafKind::Zusd,
            proof_type: PROOF_TYPE_RECURSIVE_ZUSD_LEAF,
            profile: RECURSIVE_ZUSD_LEAF_PROFILE_V1,
            lane_kind: "zusd",
            image_id: ZUSD_LEAF_ID,
        }),
        _ => Err("leaf proof type is not current spot or zUSD".to_string()),
    }
}

fn verify_leaf(path: &Path) -> Result<VerifiedLeaf, String> {
    let metadata = fs::metadata(path).map_err(|error| format!("leaf metadata: {error}"))?;
    if !metadata.is_file() || metadata.len() > MAX_ARTIFACT_BYTES_U64 {
        return Err("leaf artifact is not a bounded regular file".to_string());
    }
    let bytes = fs::read(path).map_err(|error| format!("read leaf artifact: {error}"))?;
    if bytes.len() > MAX_ARTIFACT_BYTES {
        return Err("leaf artifact exceeds byte limit".to_string());
    }
    let proof: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("leaf JSON: {error}"))?;
    let proof_type = required_str(&proof, "proof_type")?;
    let surface = leaf_surface(proof_type)?;
    let meta = proof
        .get("meta")
        .and_then(Value::as_object)
        .ok_or_else(|| "leaf meta must be an object".to_string())?;
    expect_meta(meta, "proof_type", surface.proof_type)?;
    expect_meta(meta, "proof_profile", surface.profile)?;
    expect_meta(
        meta,
        "risc0_image_id",
        &Digest::from(surface.image_id).to_string(),
    )?;
    expect_meta(meta, "receipt_codec", RECEIPT_CODEC)?;
    expect_meta(meta, "receipt_kind", "succinct")?;

    let proof_b64 = required_str(&proof, "proof")?;
    if proof_b64.len() > MAX_ARTIFACT_BYTES.div_ceil(3) * 4 {
        return Err("leaf receipt base64 exceeds limit".to_string());
    }
    let receipt_bytes = BASE64_STANDARD
        .decode(proof_b64)
        .map_err(|error| format!("leaf receipt base64: {error}"))?;
    if receipt_bytes.len() > MAX_ARTIFACT_BYTES
        || BASE64_STANDARD.encode(&receipt_bytes) != proof_b64
    {
        return Err("leaf receipt base64 is not canonical and bounded".to_string());
    }
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)
        .map_err(|error| format!("leaf receipt JSON: {error}"))?;
    if serde_json::to_vec(&receipt).map_err(|error| format!("leaf receipt encode: {error}"))?
        != receipt_bytes
    {
        return Err("leaf receipt JSON is not canonical".to_string());
    }
    let InnerReceipt::Succinct(inner) = &receipt.inner else {
        return Err("leaf receipt is not succinct".to_string());
    };
    receipt
        .verify(surface.image_id)
        .map_err(|error| format!("leaf receipt verification failed: {error}"))?;
    expect_meta(
        meta,
        "receipt_verifier_parameters",
        &receipt.metadata.verifier_parameters.to_string(),
    )?;
    expect_meta(meta, "receipt_hashfn", &inner.hashfn)?;
    expect_meta(meta, "receipt_control_id", &inner.control_id.to_string())?;

    let summary: RecursiveEffectSummaryV1 = decode_exact_postcard_v2(&receipt.journal.bytes)
        .map_err(|error| format!("leaf journal decode: {error:?}"))?;
    validate_recursive_effect_summary_shape_v1(&summary)
        .map_err(|error| format!("leaf summary rejected: {error:?}"))?;
    if summary.proof_profile != surface.profile
        || summary.risc0_image_id != surface.image_id
        || summary.lane_kind != surface.lane_kind
    {
        return Err("authenticated leaf surface mismatch".to_string());
    }
    expect_meta(meta, "chain_id", &summary.chain_id)?;
    expect_meta(meta, "lane_id", &summary.lane_id)?;
    expect_meta(meta, "statement_hash", &hex32(&summary.statement_hash))?;
    expect_meta(meta, "post_state_root", &hex32(&summary.post_state_root))?;
    if required_str(&proof, "state_hash")? != hex32(&summary.post_state_root) {
        return Err("leaf state hash does not match authenticated post-state root".to_string());
    }
    Ok(VerifiedLeaf {
        kind: surface.kind,
        profile: surface.profile.to_string(),
        image_id: surface.image_id,
        lane_kind: summary.lane_kind,
        lane_id: summary.lane_id,
        statement_hash: summary.statement_hash,
        journal_bytes: receipt.journal.bytes,
        receipt_sha256: sha256_hex(&receipt_bytes),
    })
}

fn semantic_source_id(leaf: &VerifiedLeaf) -> Result<[u8; 32], String> {
    recursive_leaf_source_id_v2(&leaf.lane_kind, &leaf.statement_hash)
        .map_err(|error| format!("leaf semantic source ID: {error:?}"))
}

fn validate_two_leaf_policy(leaves: &[VerifiedLeaf]) -> Result<(), String> {
    if leaves.len() != 2 {
        return Err("two-leaf policy requires exactly two authenticated leaves".to_string());
    }
    if leaves[0].lane_id == leaves[1].lane_id {
        return Err("duplicate authenticated leaf lane ID".to_string());
    }
    if semantic_source_id(&leaves[0])? == semantic_source_id(&leaves[1])? {
        return Err("duplicate authenticated leaf semantic source ID".to_string());
    }
    match (leaves[0].kind, leaves[1].kind) {
        (LeafKind::Spot, LeafKind::Spot)
        | (LeafKind::Spot, LeafKind::Zusd)
        | (LeafKind::Zusd, LeafKind::Spot) => Ok(()),
        (LeafKind::Zusd, LeafKind::Zusd) => {
            Err("expected current spot+zUSD or distinct spot+spot leaf pair".to_string())
        }
    }
}

fn verify_artifact(path: &Path) -> Result<VerifiedArtifact, String> {
    let metadata = fs::metadata(path).map_err(|error| format!("metadata: {error}"))?;
    if !metadata.is_file() || metadata.len() > MAX_ARTIFACT_BYTES_U64 {
        return Err("artifact is not a bounded regular file".to_string());
    }
    let bytes = fs::read(path).map_err(|error| format!("read artifact: {error}"))?;
    if bytes.len() > MAX_ARTIFACT_BYTES {
        return Err("artifact exceeds byte limit".to_string());
    }
    let value: Value =
        serde_json::from_slice(&bytes).map_err(|error| format!("artifact JSON: {error}"))?;
    if serde_json::to_vec(&value).map_err(|error| format!("canonical JSON: {error}"))? != bytes {
        return Err("artifact is not canonical JSON".to_string());
    }
    let artifact: ReceiptArtifact =
        serde_json::from_slice(&bytes).map_err(|error| format!("artifact schema: {error}"))?;
    if artifact.schema != ARTIFACT_SCHEMA
        || artifact.schema_version != 2
        || artifact.proof_type != PROOF_TYPE_RECURSIVE_NODE_V2
        || artifact.receipt_codec != RECEIPT_CODEC
        || artifact.receipt_kind != "succinct"
        || artifact.risc0_image_id != image_id_hex()
        || !has_exact_recursive_v2_local_nonclaims(&artifact.nonclaims)
    {
        return Err("artifact header mismatch".to_string());
    }

    if artifact.proof.len() > MAX_ARTIFACT_BYTES.div_ceil(3) * 4 {
        return Err("receipt base64 exceeds limit".to_string());
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
    if serde_json::to_vec(&receipt).map_err(|error| format!("receipt encode: {error}"))?
        != receipt_bytes
        || !matches!(&receipt.inner, InnerReceipt::Succinct(_))
    {
        return Err("receipt codec or kind mismatch".to_string());
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
    let journal_bytes =
        postcard::to_allocvec(&journal).map_err(|error| format!("journal encode: {error}"))?;
    let artifact_journal = postcard::to_allocvec(&artifact.journal)
        .map_err(|error| format!("artifact journal encode: {error}"))?;
    if journal_bytes != receipt.journal.bytes || journal_bytes != artifact_journal {
        return Err("artifact journal is not the authenticated journal".to_string());
    }
    if sha256_hex(&journal_bytes) != artifact.journal_sha256 {
        return Err("journal SHA-256 mismatch".to_string());
    }
    let protocol_hash = recursive_node_journal_bytes_hash_v2(&journal_bytes)
        .map_err(|error| format!("protocol journal hash: {error:?}"))?;
    if hex32(&protocol_hash) != artifact.protocol_journal_hash {
        return Err("protocol journal hash mismatch".to_string());
    }
    if journal.journal_version != RECURSIVE_NODE_JOURNAL_VERSION_V2
        || journal.proof_type != PROOF_TYPE_RECURSIVE_NODE_V2
        || journal.domain_separator != RECURSIVE_NODE_DOMAIN_SEPARATOR_V2
        || journal.self_image_id != TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID
        || journal.flat_leaf_count != 2
    {
        return Err("authenticated journal surface mismatch".to_string());
    }
    Ok(VerifiedArtifact {
        journal,
        journal_bytes,
        receipt_sha256,
    })
}

fn verify_pair(
    leaves: &[VerifiedLeaf],
    inner: &VerifiedArtifact,
    root: &VerifiedArtifact,
) -> Result<(), String> {
    if inner.journal.level != RecursiveNodeLevelV2::ClosedSubtreeOverLeaves
        || inner.journal.profile != RecursiveNodeProfileV2::ClosedSubtree
        || inner.journal.tree_height != 1
        || inner.journal.immediate_child_count != 2
        || inner.journal.subtree_node_count != 3
        || root.journal.level != RecursiveNodeLevelV2::EpochRootOverSubtrees
        || root.journal.profile != RecursiveNodeProfileV2::EpochRoot
        || root.journal.tree_height != 2
        || root.journal.immediate_child_count != 1
        || root.journal.subtree_node_count != 4
    {
        return Err("two-leaf pair shape mismatch".to_string());
    }
    let mut claims = Vec::with_capacity(leaves.len());
    let mut journals = Vec::with_capacity(leaves.len());
    let mut verifier_ids = Vec::with_capacity(leaves.len());
    let mut source_ids = Vec::with_capacity(leaves.len());
    let mut assigned_leaf_ids = Vec::with_capacity(leaves.len());
    for leaf in leaves {
        claims.push(
            recursive_child_verification_claim_hash_v1(&leaf.image_id, &leaf.journal_bytes)
                .map_err(|error| format!("leaf claim hash: {error:?}"))?,
        );
        journals.push(
            recursive_child_journal_hash_v1(&leaf.journal_bytes)
                .map_err(|error| format!("leaf journal hash: {error:?}"))?,
        );
        verifier_ids.push(
            recursive_child_verifier_id_v1(&leaf.image_id, &leaf.profile)
                .map_err(|error| format!("leaf verifier ID: {error:?}"))?,
        );
        let source_id = semantic_source_id(leaf)?;
        assigned_leaf_ids.push(
            recursive_assigned_leaf_id_v2(
                &inner.journal.aggregation_scope_hash,
                &leaf.lane_id,
                &source_id,
            )
            .map_err(|error| format!("assigned leaf ID: {error:?}"))?,
        );
        source_ids.push(source_id);
    }
    let mut canonical_claims = claims.clone();
    canonical_claims.sort_unstable();
    verifier_ids.sort_unstable();
    verifier_ids.dedup();
    source_ids.sort_unstable();
    assigned_leaf_ids.sort_unstable();
    let immediate_claims_root = root_list(IMMEDIATE_CLAIMS_ROOT_DOMAIN, &claims)?;
    let immediate_journals_root = root_list(IMMEDIATE_JOURNALS_ROOT_DOMAIN, &journals)?;
    if inner.journal.immediate_child_claims_root != immediate_claims_root
        || inner.journal.immediate_child_journals_root != immediate_journals_root
        || inner.journal.immediate_verifier_set_root
            != recursive_immediate_verifier_set_root_v2(&verifier_ids)
                .map_err(|error| format!("leaf verifier set root: {error:?}"))?
        || inner.journal.descendant_claims_root
            != recursive_descendant_claims_root_v2(&canonical_claims)
                .map_err(|error| format!("descendant claims root: {error:?}"))?
        || inner.journal.descendant_sources_root
            != recursive_descendant_sources_root_v2(&source_ids)
                .map_err(|error| format!("descendant sources root: {error:?}"))?
        || inner.journal.assigned_leaf_ids_root
            != recursive_assigned_leaf_ids_root_v2(&assigned_leaf_ids)
                .map_err(|error| format!("assigned leaf IDs root: {error:?}"))?
    {
        return Err("inner node does not bind the supplied current leaves".to_string());
    }
    if root.journal.aggregation_scope_hash != inner.journal.aggregation_scope_hash
        || root.journal.flat_v1_projection != inner.journal.flat_v1_projection
        || root.journal.leaf_disclosures_root != inner.journal.leaf_disclosures_root
        || root.journal.assigned_leaf_ids_root != inner.journal.assigned_leaf_ids_root
        || root.journal.descendant_claims_root != inner.journal.descendant_claims_root
        || root.journal.descendant_sources_root != inner.journal.descendant_sources_root
    {
        return Err("two-leaf flat projection binding mismatch".to_string());
    }

    let inner_claim = recursive_node_verification_claim_hash_v2(
        &TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID,
        &inner.journal_bytes,
    )
    .map_err(|error| format!("inner claim hash: {error:?}"))?;
    let inner_journal = recursive_node_journal_bytes_hash_v2(&inner.journal_bytes)
        .map_err(|error| format!("inner journal hash: {error:?}"))?;
    let inner_claims_root = singleton_root(IMMEDIATE_CLAIMS_ROOT_DOMAIN, &inner_claim)?;
    let inner_journals_root = singleton_root(IMMEDIATE_JOURNALS_ROOT_DOMAIN, &inner_journal)?;
    if root.journal.immediate_child_claims_root != inner_claims_root
        || root.journal.immediate_child_journals_root != inner_journals_root
    {
        return Err("root does not bind the supplied inner receipt".to_string());
    }
    let node_verifier_id = recursive_node_verifier_id_v2(
        &TAU_STATE_PROOF_RISC0_AGGREGATE_V2_ID,
        RecursiveNodeProfileV2::ClosedSubtree,
    )
    .map_err(|error| format!("inner verifier ID: {error:?}"))?;
    let verifier_root = recursive_immediate_verifier_set_root_v2(&[node_verifier_id])
        .map_err(|error| format!("verifier set root: {error:?}"))?;
    if root.journal.immediate_verifier_set_root != verifier_root {
        return Err("root immediate verifier set mismatch".to_string());
    }
    Ok(())
}

fn singleton_root(domain: &[u8], value: &[u8; 32]) -> Result<[u8; 32], String> {
    root_list(domain, core::slice::from_ref(value))
}

fn root_list(domain: &[u8], values: &[[u8; 32]]) -> Result<[u8; 32], String> {
    let count = u32::try_from(values.len())
        .map_err(|_| "verifier root length exceeds u32 bound".to_string())?;
    let mut hasher = Sha256::new();
    hasher.update(domain);
    hasher.update(count.to_be_bytes());
    for value in values {
        hasher.update(value);
    }
    Ok(hasher.finalize().into())
}

fn required_str<'a>(value: &'a Value, field: &str) -> Result<&'a str, String> {
    value
        .get(field)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("{field} missing or not a string"))
}

fn expect_meta(
    meta: &serde_json::Map<String, Value>,
    field: &str,
    expected: &str,
) -> Result<(), String> {
    if meta.get(field).and_then(Value::as_str) != Some(expected) {
        return Err(format!("leaf meta.{field} mismatch"));
    }
    Ok(())
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

#[cfg(test)]
mod tests {
    use super::*;

    fn statement(byte: u8) -> [u8; 32] {
        [byte; 32]
    }

    fn leaf(kind: LeafKind, lane_id: &str, statement_hash: [u8; 32]) -> VerifiedLeaf {
        let (profile, image_id, lane_kind) = match kind {
            LeafKind::Spot => (RECURSIVE_SPOT_LEAF_PROFILE_V1, SPOT_LEAF_ID, "spot"),
            LeafKind::Zusd => (RECURSIVE_ZUSD_LEAF_PROFILE_V1, ZUSD_LEAF_ID, "zusd"),
        };
        VerifiedLeaf {
            kind,
            profile: profile.to_string(),
            image_id,
            lane_kind: lane_kind.to_string(),
            lane_id: lane_id.to_string(),
            statement_hash,
            journal_bytes: vec![1],
            receipt_sha256: "00".repeat(32),
        }
    }

    #[test]
    fn spot_and_zusd_pair_is_allowed() {
        let leaves = [
            leaf(LeafKind::Spot, "spot-a", statement(1)),
            leaf(LeafKind::Zusd, "zusd-a", statement(2)),
        ];
        assert_eq!(validate_two_leaf_policy(&leaves), Ok(()));
    }

    #[test]
    fn distinct_spot_pair_is_allowed() {
        let leaves = [
            leaf(LeafKind::Spot, "spot-a", statement(1)),
            leaf(LeafKind::Spot, "spot-b", statement(2)),
        ];
        assert_eq!(validate_two_leaf_policy(&leaves), Ok(()));
    }

    #[test]
    fn duplicate_lane_precedes_duplicate_source_reject() {
        let leaves = [
            leaf(LeafKind::Spot, "spot-a", statement(1)),
            leaf(LeafKind::Spot, "spot-a", statement(1)),
        ];
        assert_eq!(
            validate_two_leaf_policy(&leaves),
            Err("duplicate authenticated leaf lane ID".to_string())
        );
    }

    #[test]
    fn lane_alias_cannot_duplicate_semantic_source() {
        let leaves = [
            leaf(LeafKind::Spot, "spot-a", statement(1)),
            leaf(LeafKind::Spot, "spot-b", statement(1)),
        ];
        assert_eq!(
            validate_two_leaf_policy(&leaves),
            Err("duplicate authenticated leaf semantic source ID".to_string())
        );
    }

    #[test]
    fn two_zusd_leaves_are_outside_bounded_policy() {
        let leaves = [
            leaf(LeafKind::Zusd, "zusd-a", statement(1)),
            leaf(LeafKind::Zusd, "zusd-b", statement(2)),
        ];
        assert_eq!(
            validate_two_leaf_policy(&leaves),
            Err("expected current spot+zUSD or distinct spot+spot leaf pair".to_string())
        );
    }

    #[test]
    fn policy_requires_exactly_two_leaves() {
        let leaves = [leaf(LeafKind::Spot, "spot-a", statement(1))];
        assert_eq!(
            validate_two_leaf_policy(&leaves),
            Err("two-leaf policy requires exactly two authenticated leaves".to_string())
        );
    }
}
