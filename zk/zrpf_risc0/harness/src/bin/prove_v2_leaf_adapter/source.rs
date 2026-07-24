use std::path::Path;

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use risc0_zkvm::{Digest, InnerReceipt, Receipt};
use serde::{Deserialize, Serialize};
use tau_state_proof_risc0_shared::{
    recursive_asset_delta_root_v1, RecursiveAssetDeltaRowV1, RecursiveEffectSummaryV1,
    PROOF_TYPE_RECURSIVE_SPOT_LEAF,
};
use zenodex_zrpf_risc0_shared::{source_policy_v2, SourceKindV2};

use super::artifact_io::{
    canonical_receipt_bytes, read_bounded_regular_file, require_succinct, sha256_hex,
    MAX_ARTIFACT_BYTES,
};

const RECEIPT_CODEC: &str = "risc0_receipt_canonical_serde_json_depth128_v1";

pub(super) struct VerifiedSourceReceipt {
    pub(super) receipt: Receipt,
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
    asset_delta_rows: Vec<RecursiveAssetDeltaRowWire>,
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

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct RecursiveAssetDeltaRowWire {
    asset_id: String,
    authority_root: String,
    authorized_burn_atoms: String,
    authorized_mint_atoms: String,
    credit_atoms: String,
    debit_atoms: String,
}

impl RecursiveAssetDeltaRowWire {
    fn to_typed(&self) -> Result<RecursiveAssetDeltaRowV1, String> {
        Ok(RecursiveAssetDeltaRowV1 {
            asset_id: self.asset_id.clone(),
            debit_atoms: parse_canonical_u128(&self.debit_atoms, "debit_atoms")?,
            credit_atoms: parse_canonical_u128(&self.credit_atoms, "credit_atoms")?,
            authorized_mint_atoms: parse_canonical_u128(
                &self.authorized_mint_atoms,
                "authorized_mint_atoms",
            )?,
            authorized_burn_atoms: parse_canonical_u128(
                &self.authorized_burn_atoms,
                "authorized_burn_atoms",
            )?,
            authority_root: parse_canonical_hash(&self.authority_root, "authority_root")?,
        })
    }
}

pub(super) fn load_verified_source(path: &Path) -> Result<VerifiedSourceReceipt, String> {
    let artifact_bytes = read_bounded_regular_file(path, "current source proof")?;
    let artifact: SourceProofArtifact = serde_json::from_slice(&artifact_bytes)
        .map_err(|error| format!("current source proof JSON: {error}"))?;
    require_exact_json_encoding(&artifact, &artifact_bytes, "current source proof")?;
    validate_source_envelope(&artifact)?;

    let receipt_bytes = decode_canonical_receipt(&artifact.proof)?;
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)
        .map_err(|error| format!("current source receipt JSON: {error}"))?;
    if canonical_receipt_bytes(&receipt)? != receipt_bytes {
        return Err("current source receipt JSON is not canonical".to_owned());
    }
    require_succinct(&receipt, "current source")?;
    let policy = source_policy_v2(SourceKindV2::Spot)
        .map_err(|error| format!("current source policy rejected: {error}"))?;
    receipt
        .verify(policy.image_id)
        .map_err(|error| format!("current source receipt verification failed: {error}"))?;
    let summary = decode_exact_source_summary(&receipt)?;
    verify_source_bindings(&artifact, &receipt, &summary)?;
    Ok(VerifiedSourceReceipt {
        receipt,
        receipt_sha256: sha256_hex(&receipt_bytes),
    })
}

pub(super) fn require_exact_json_encoding<T: Serialize>(
    value: &T,
    bytes: &[u8],
    label: &str,
) -> Result<(), String> {
    let canonical =
        serde_json::to_vec(value).map_err(|error| format!("{label} canonical encode: {error}"))?;
    if canonical != bytes {
        return Err(format!("{label} JSON is not exact canonical bytes"));
    }
    Ok(())
}

fn validate_source_envelope(artifact: &SourceProofArtifact) -> Result<(), String> {
    let policy = source_policy_v2(SourceKindV2::Spot)
        .map_err(|error| format!("current source policy rejected: {error}"))?;
    if artifact.schema != "tau_state_proof"
        || artifact.schema_version != 1
        || artifact.proof_type != PROOF_TYPE_RECURSIVE_SPOT_LEAF
        || artifact.meta.proof_type != policy.proof_type
        || artifact.meta.proof_profile != policy.proof_profile
        || artifact.meta.risc0_image_id != Digest::from(policy.image_id).to_string()
        || artifact.meta.receipt_codec != RECEIPT_CODEC
        || artifact.meta.receipt_kind != "succinct"
    {
        return Err("current source proof governed envelope mismatch".to_owned());
    }
    Ok(())
}

fn decode_canonical_receipt(proof_b64: &str) -> Result<Vec<u8>, String> {
    if proof_b64.len() > MAX_ARTIFACT_BYTES.div_ceil(3) * 4 {
        return Err("current source receipt base64 exceeds bound".to_owned());
    }
    let bytes = BASE64_STANDARD
        .decode(proof_b64)
        .map_err(|error| format!("current source receipt base64: {error}"))?;
    if bytes.is_empty()
        || bytes.len() > MAX_ARTIFACT_BYTES
        || BASE64_STANDARD.encode(&bytes) != proof_b64
    {
        return Err("current source receipt base64 is noncanonical or oversized".to_owned());
    }
    Ok(bytes)
}

fn decode_exact_source_summary(receipt: &Receipt) -> Result<RecursiveEffectSummaryV1, String> {
    let (summary, remainder) =
        postcard::take_from_bytes::<RecursiveEffectSummaryV1>(&receipt.journal.bytes)
            .map_err(|error| format!("current source journal decode: {error}"))?;
    if !remainder.is_empty()
        || postcard::to_allocvec(&summary)
            .map_err(|error| format!("current source journal encode: {error}"))?
            != receipt.journal.bytes
    {
        return Err("current source journal encoding is not exact canonical Postcard".to_owned());
    }
    Ok(summary)
}

fn verify_source_bindings(
    artifact: &SourceProofArtifact,
    receipt: &Receipt,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), String> {
    verify_transition_hashes(artifact, summary)?;
    verify_policy_hashes(&artifact.meta, summary)?;
    verify_scalar_bindings(&artifact.meta, summary)?;
    verify_asset_rows(&artifact.meta, summary)?;
    verify_receipt_security(&artifact.meta, receipt)
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

fn require_hash_bindings(rows: &[(&str, &str, [u8; 32])]) -> Result<(), String> {
    for (field, declared, expected) in rows {
        if *declared != hex::encode(expected) {
            return Err(format!("current source metadata mismatch: {field}"));
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
        return Err("current source metadata differs from authenticated journal".to_owned());
    }
    Ok(())
}

fn verify_asset_rows(
    meta: &SpotProofMeta,
    summary: &RecursiveEffectSummaryV1,
) -> Result<(), String> {
    let rows = meta
        .asset_delta_rows
        .iter()
        .map(RecursiveAssetDeltaRowWire::to_typed)
        .collect::<Result<Vec<_>, _>>()?;
    let root = recursive_asset_delta_root_v1(&rows)
        .map_err(|_| "current source asset rows rejected".to_owned())?;
    if root != summary.asset_delta_root {
        return Err("current source asset rows do not open the authenticated root".to_owned());
    }
    Ok(())
}

fn parse_canonical_u128(value: &str, field: &str) -> Result<u128, String> {
    let parsed = value
        .parse::<u128>()
        .map_err(|error| format!("current source {field} is not a u128: {error}"))?;
    if parsed.to_string() != value {
        return Err(format!("current source {field} is not canonical decimal"));
    }
    Ok(parsed)
}

fn parse_canonical_hash(value: &str, field: &str) -> Result<[u8; 32], String> {
    if value.len() != 64
        || !value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
    {
        return Err(format!(
            "current source {field} is not exact lowercase hex32"
        ));
    }
    let mut decoded = [0_u8; 32];
    hex::decode_to_slice(value, &mut decoded)
        .map_err(|error| format!("current source {field} hex decode: {error}"))?;
    Ok(decoded)
}

fn verify_receipt_security(meta: &SpotProofMeta, receipt: &Receipt) -> Result<(), String> {
    let InnerReceipt::Succinct(inner) = &receipt.inner else {
        return Err("current source receipt is not Succinct".to_owned());
    };
    if meta.receipt_verifier_parameters != receipt.metadata.verifier_parameters.to_string()
        || meta.receipt_hashfn != inner.hashfn
        || meta.receipt_control_id != inner.control_id.to_string()
    {
        return Err("current source receipt security metadata mismatch".to_owned());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{parse_canonical_hash, RecursiveAssetDeltaRowWire};

    fn row() -> RecursiveAssetDeltaRowWire {
        RecursiveAssetDeltaRowWire {
            asset_id: "asset-a".to_owned(),
            authority_root: "ab".repeat(32),
            authorized_burn_atoms: "0".to_owned(),
            authorized_mint_atoms: "18446744073709551616".to_owned(),
            credit_atoms: "12".to_owned(),
            debit_atoms: "12".to_owned(),
        }
    }

    #[test]
    fn asset_row_wire_accepts_canonical_nonempty_values() {
        let row = row();
        assert!(matches!(
            row.to_typed(),
            Ok(typed)
                if typed.asset_id == "asset-a"
                    && typed.authorized_mint_atoms == 18_446_744_073_709_551_616
                    && typed.authority_root == [0xab; 32]
        ));
        let expected = format!(
            "{{\"asset_id\":\"asset-a\",\"authority_root\":\"{}\",\"authorized_burn_atoms\":\"0\",\"authorized_mint_atoms\":\"18446744073709551616\",\"credit_atoms\":\"12\",\"debit_atoms\":\"12\"}}",
            "ab".repeat(32)
        );
        assert!(matches!(
            serde_json::to_string(&row),
            Ok(serialized) if serialized == expected
        ));
    }

    #[test]
    fn asset_row_wire_rejects_noncanonical_or_out_of_range_values() {
        let mut leading_zero = row();
        leading_zero.debit_atoms = "012".to_owned();
        assert!(leading_zero.to_typed().is_err());

        let mut overflow = row();
        overflow.credit_atoms = "340282366920938463463374607431768211456".to_owned();
        assert!(overflow.to_typed().is_err());

        assert!(parse_canonical_hash(&"AB".repeat(32), "authority_root").is_err());
        assert!(parse_canonical_hash(&"ab".repeat(31), "authority_root").is_err());
    }
}
