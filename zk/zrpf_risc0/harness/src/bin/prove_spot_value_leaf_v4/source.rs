use std::path::Path;

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use risc0_zkvm::{Digest, InnerReceipt, Receipt};
use serde::{Deserialize, Serialize};
use tau_state_proof_risc0_shared::{
    recursive_asset_delta_root_v1, RecursiveAssetDeltaRowV1, RecursiveEffectSummaryV1,
    PROOF_TYPE_RECURSIVE_SPOT_LEAF,
};
use zenodex_zrpf_risc0_shared::{source_policy_v1, SourceKindV1};

use super::artifact_io::{
    canonical_receipt_bytes, read_bounded_regular_file, require_succinct, sha256_hex,
    MAX_ARTIFACT_BYTES,
};

const RECEIPT_CODEC: &str = "risc0_receipt_canonical_serde_json_depth128_v1";
const RETAINED_SOURCE_WRAPPER_BYTES: usize = 784_225;
const RETAINED_SOURCE_WRAPPER_SHA256: &str =
    "4ce7db31e6ae5e5af53b4ef67fb0cd6ebb1dcae9cf05ee9f73b4511c10db20b9";
const RETAINED_SOURCE_RECEIPT_SHA256: &str =
    "c6f365df966c98ef28f05e59c3e36533d0c16ca06475348a7bbb2863e41d58f6";

pub(super) struct VerifiedSource {
    pub(super) receipt: Receipt,
    pub(super) summary: RecursiveEffectSummaryV1,
    pub(super) asset_rows: Vec<RecursiveAssetDeltaRowV1>,
    pub(super) receipt_sha256: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceProofArtifact {
    meta: SpotProofMeta,
    proof: String,
    proof_type: String,
    schema: String,
    schema_version: u32,
    state_hash: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SpotProofMeta {
    accepted_receipts_root: String,
    asset_delta_root: String,
    asset_delta_rows: Vec<RecursiveAssetDeltaRowV1>,
    chain_id: String,
    child_image_id: String,
    cross_shard_inbox_root: String,
    cross_shard_outbox_root: String,
    dependency_lock_hash: String,
    epoch_id: u64,
    evidence_root: String,
    feature_suite_hash: String,
    lane_id: String,
    lane_kind: String,
    post_state_root: String,
    pre_state_root: String,
    proof_profile: String,
    proof_type: String,
    public_policy_hash: String,
    receipt_codec: String,
    receipt_control_id: String,
    receipt_hashfn: String,
    receipt_kind: String,
    receipt_root: String,
    receipt_verifier_parameters: String,
    rejected_receipts_root: String,
    risc0_image_id: String,
    statement_hash: String,
    summary_version: u32,
    toolchain_lock_hash: String,
    tx_root: String,
    write_set_root: String,
}

pub(super) fn load_verified_source(path: &Path) -> Result<VerifiedSource, String> {
    let artifact_bytes = read_bounded_regular_file(path, "source proof")?;
    require_exact_wrapper(&artifact_bytes)?;
    let artifact: SourceProofArtifact = serde_json::from_slice(&artifact_bytes)
        .map_err(|error| format!("source proof JSON: {error}"))?;
    require_canonical_artifact(&artifact, &artifact_bytes)?;
    validate_source_artifact_envelope(&artifact)?;

    let receipt_bytes = decode_canonical_source_receipt(&artifact.proof)?;
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)
        .map_err(|error| format!("source receipt JSON: {error}"))?;
    if canonical_receipt_bytes(&receipt)? != receipt_bytes {
        return Err("source receipt JSON is not canonical".to_owned());
    }
    require_succinct(&receipt, "source")?;
    let policy = source_policy_v1(SourceKindV1::Spot);
    receipt
        .verify(policy.image_id)
        .map_err(|error| format!("source receipt verification failed: {error}"))?;
    let summary = decode_exact_source_summary(&receipt)?;
    verify_source_artifact_bindings(&artifact, &receipt, &summary)?;
    if !artifact.meta.asset_delta_rows.is_empty()
        || summary.pre_state_root != summary.post_state_root
    {
        return Err("retained source is not the scoped zero-row unchanged-state leaf".to_owned());
    }
    Ok(VerifiedSource {
        receipt,
        summary,
        asset_rows: artifact.meta.asset_delta_rows,
        receipt_sha256: sha256_hex(&receipt_bytes),
    })
}

fn require_exact_wrapper(bytes: &[u8]) -> Result<(), String> {
    if bytes.len() != RETAINED_SOURCE_WRAPPER_BYTES
        || sha256_hex(bytes) != RETAINED_SOURCE_WRAPPER_SHA256
    {
        return Err("source proof differs from retained ordinal-zero wrapper".to_owned());
    }
    Ok(())
}

fn require_canonical_artifact(artifact: &SourceProofArtifact, bytes: &[u8]) -> Result<(), String> {
    let canonical = serde_json::to_vec(artifact)
        .map_err(|error| format!("source proof canonical encode: {error}"))?;
    if canonical != bytes {
        return Err("source proof JSON is not canonical".to_owned());
    }
    Ok(())
}

fn decode_canonical_source_receipt(proof_b64: &str) -> Result<Vec<u8>, String> {
    if proof_b64.len() > MAX_ARTIFACT_BYTES.div_ceil(3) * 4 {
        return Err("source receipt base64 exceeds bound".to_owned());
    }
    let bytes = BASE64_STANDARD
        .decode(proof_b64)
        .map_err(|error| format!("source receipt base64: {error}"))?;
    if bytes.is_empty()
        || bytes.len() > MAX_ARTIFACT_BYTES
        || BASE64_STANDARD.encode(&bytes) != proof_b64
        || sha256_hex(&bytes) != RETAINED_SOURCE_RECEIPT_SHA256
    {
        return Err("source receipt base64 is noncanonical or oversized".to_owned());
    }
    Ok(bytes)
}

fn validate_source_artifact_envelope(artifact: &SourceProofArtifact) -> Result<(), String> {
    let policy = source_policy_v1(SourceKindV1::Spot);
    if artifact.schema != "tau_state_proof"
        || artifact.schema_version != 1
        || artifact.proof_type != PROOF_TYPE_RECURSIVE_SPOT_LEAF
        || artifact.meta.proof_type != policy.proof_type
        || artifact.meta.proof_profile != policy.proof_profile
        || artifact.meta.risc0_image_id != Digest::from(policy.image_id).to_string()
        || artifact.meta.receipt_codec != RECEIPT_CODEC
        || artifact.meta.receipt_kind != "succinct"
    {
        return Err("source proof governed envelope mismatch".to_owned());
    }
    Ok(())
}

fn decode_exact_source_summary(receipt: &Receipt) -> Result<RecursiveEffectSummaryV1, String> {
    let (summary, remainder) =
        postcard::take_from_bytes::<RecursiveEffectSummaryV1>(&receipt.journal.bytes)
            .map_err(|error| format!("source journal decode: {error}"))?;
    if !remainder.is_empty()
        || postcard::to_allocvec(&summary)
            .map_err(|error| format!("source journal encode: {error}"))?
            != receipt.journal.bytes
    {
        return Err("source journal encoding is not exact canonical Postcard".to_owned());
    }
    Ok(summary)
}

fn verify_source_artifact_bindings(
    artifact: &SourceProofArtifact,
    receipt: &Receipt,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), String> {
    verify_hash_bindings(artifact, summary)?;
    verify_scalar_bindings(&artifact.meta, summary)?;
    verify_asset_rows(&artifact.meta, summary)?;
    verify_receipt_security(&artifact.meta, receipt)
}

fn verify_hash_bindings(
    artifact: &SourceProofArtifact,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), String> {
    verify_transition_hashes(artifact, summary)?;
    verify_policy_hashes(&artifact.meta, summary)
}

fn verify_transition_hashes(
    artifact: &SourceProofArtifact,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), String> {
    let meta = &artifact.meta;
    require_hash_bindings(&[
        (
            "state_hash",
            artifact.state_hash.as_str(),
            summary.post_state_root,
        ),
        (
            "statement_hash",
            meta.statement_hash.as_str(),
            summary.statement_hash,
        ),
        (
            "pre_state_root",
            meta.pre_state_root.as_str(),
            summary.pre_state_root,
        ),
        (
            "post_state_root",
            meta.post_state_root.as_str(),
            summary.post_state_root,
        ),
        ("tx_root", meta.tx_root.as_str(), summary.tx_root),
        (
            "evidence_root",
            meta.evidence_root.as_str(),
            summary.evidence_root,
        ),
        (
            "receipt_root",
            meta.receipt_root.as_str(),
            summary.receipt_root,
        ),
        (
            "accepted_receipts_root",
            meta.accepted_receipts_root.as_str(),
            summary.accepted_receipts_root,
        ),
        (
            "rejected_receipts_root",
            meta.rejected_receipts_root.as_str(),
            summary.rejected_receipts_root,
        ),
    ])
}

fn verify_policy_hashes(
    meta: &SpotProofMeta,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), String> {
    require_hash_bindings(&[
        (
            "asset_delta_root",
            meta.asset_delta_root.as_str(),
            summary.asset_delta_root,
        ),
        (
            "cross_shard_outbox_root",
            meta.cross_shard_outbox_root.as_str(),
            summary.cross_shard_outbox_root,
        ),
        (
            "cross_shard_inbox_root",
            meta.cross_shard_inbox_root.as_str(),
            summary.cross_shard_inbox_root,
        ),
        (
            "write_set_root",
            meta.write_set_root.as_str(),
            summary.write_set_root,
        ),
        (
            "public_policy_hash",
            meta.public_policy_hash.as_str(),
            summary.public_policy_hash,
        ),
        (
            "feature_suite_hash",
            meta.feature_suite_hash.as_str(),
            summary.feature_suite_hash,
        ),
        (
            "dependency_lock_hash",
            meta.dependency_lock_hash.as_str(),
            summary.dependency_lock_hash,
        ),
        (
            "toolchain_lock_hash",
            meta.toolchain_lock_hash.as_str(),
            summary.toolchain_lock_hash,
        ),
    ])
}

fn require_hash_bindings(bindings: &[(&str, &str, [u8; 32])]) -> Result<(), String> {
    for (field, declared, expected) in bindings {
        if *declared != hex::encode(expected) {
            return Err(format!("source metadata mismatch: {field}"));
        }
    }
    Ok(())
}

fn verify_scalar_bindings(
    meta: &SpotProofMeta,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), String> {
    let image_id = Digest::from(summary.risc0_image_id).to_string();
    if meta.summary_version != summary.summary_version
        || meta.lane_id != summary.lane_id
        || meta.lane_kind != summary.lane_kind
        || meta.chain_id != summary.chain_id
        || meta.epoch_id != summary.epoch_id
        || meta.proof_profile != summary.proof_profile
        || meta.risc0_image_id != image_id
        || meta.child_image_id != image_id
    {
        return Err("source metadata differs from authenticated journal".to_owned());
    }
    Ok(())
}

fn verify_asset_rows(
    meta: &SpotProofMeta,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), String> {
    let root = recursive_asset_delta_root_v1(&meta.asset_delta_rows)
        .map_err(|_| "source asset rows rejected".to_owned())?;
    if root != summary.asset_delta_root {
        return Err("source asset rows do not open the authenticated root".to_owned());
    }
    Ok(())
}

fn verify_receipt_security(meta: &SpotProofMeta, receipt: &Receipt) -> Result<(), String> {
    let InnerReceipt::Succinct(inner) = &receipt.inner else {
        return Err("source receipt is not Succinct".to_owned());
    };
    if meta.receipt_verifier_parameters != receipt.metadata.verifier_parameters.to_string()
        || meta.receipt_hashfn != inner.hashfn
        || meta.receipt_control_id != inner.control_id.to_string()
    {
        return Err("source receipt security metadata mismatch".to_owned());
    }
    Ok(())
}
