mod bundle;
mod error;
pub mod firecracker_protocol;
mod profile;

use risc0_zkvm::{Digest, InnerReceipt, Receipt};
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use zenodex_zrpf_risc0_aggregate_shared::{
    compose_structural_aggregate_after_receipt_verification_v1, StructuralAggregateInputV1,
    StructuralAggregatePolicyV1,
};
use zenodex_zrpf_risc0_verifier::{
    VerifiedNodeReceiptErrorV3, VerifiedNodeReceiptV3, MAX_CANONICAL_RECEIPT_BYTES_V3,
    ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
};

use bundle::{
    parse_bundle_directory, read_bounded_regular_file, require_retained_artifact_binding,
    BundlePaths,
};
pub use error::ReplayError;
use profile::{
    ADAPTER_ID, EXPECTED_ROOT_JOURNAL_HASH, LEAF_NAMES, LEVEL_ONE_ID, LEVEL_ONE_NAMES,
    LEVEL_TWO_ID, MUTATION_NAME, REPLAY_PROFILE_ID, REPORT_SCHEMA, ROOT_NAME,
    ROOT_SEAL_MUTATION_WORD_INDEX,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SealWordMutation {
    word_count: usize,
    word_index: usize,
    original_word: u32,
    mutated_word: u32,
}

struct VerifiedTree {
    leaves: Vec<VerifiedNodeReceiptV3>,
    level_one: Vec<VerifiedNodeReceiptV3>,
    root: VerifiedNodeReceiptV3,
}

/// Canonical replay report produced only after the complete retained tree verifies.
pub struct VerifiedReplayReport {
    json: String,
}

impl VerifiedReplayReport {
    pub fn as_json(&self) -> &str {
        &self.json
    }

    pub fn canonical_cli_bytes(&self) -> Vec<u8> {
        let mut output = Vec::with_capacity(self.json.len() + 1);
        output.extend_from_slice(self.json.as_bytes());
        output.push(b'\n');
        output
    }

    fn from_verified_json(json: String) -> Self {
        Self { json }
    }
}

pub fn run_cli(
    args: impl IntoIterator<Item = String>,
) -> Result<VerifiedReplayReport, ReplayError> {
    let paths = parse_bundle_directory(args)?;
    let tree = verify_tree(&paths)?;
    verify_expected_root(&tree)?;
    let mutation = verify_root_seal_mutation(&paths, &tree)?;
    let receipt_profile = tree.root.receipt_profile();
    let report = json!({
        "authority": {
            "guest_binaries_required_by_replay": false,
            "guest_source_to_image_attested": false,
            "ledger_admission_authority": false,
            "production_authority": false,
            "proof_generation_source_attested": false,
            "release_authority": false,
            "settlement_authority": false
        },
        "expected_images": {
            "adapter": Digest::from(ADAPTER_ID).to_string(),
            "structural_l1": Digest::from(LEVEL_ONE_ID).to_string(),
            "structural_l2": Digest::from(LEVEL_TWO_ID).to_string()
        },
        "leaf_receipts": tree.leaves.iter().map(receipt_report).collect::<Result<Vec<_>, _>>()?,
        "level_one_receipts": tree.level_one.iter().map(receipt_report).collect::<Result<Vec<_>, _>>()?,
        "mutation_control": mutation,
        "nonclaims": [
            "no new proof generation or proof-generation provenance claim",
            "no guest source-to-image, cross-host reproducibility, or release-build claim",
            "no authenticated compiler, dependency cache, runtime rootfs, or executing-binary identity claim",
            "no semantic aggregation, conservation, data-availability, carry, or schedule claim",
            "no ledger admission, settlement, release, or production authority",
            "no witness-privacy or zero-knowledge claim",
            "no receipt-byte determinism claim",
            "operation counts denote source-transition receipts; no transaction-count, TPS, or throughput claim"
        ],
        "ok": true,
        "receipt_security_profile": {
            "control_id": receipt_profile.control_id(),
            "hashfn": receipt_profile.hashfn(),
            "profile_id": ZRPF_RISC0_SUCCINCT_RECEIPT_PROFILE_ID_V1,
            "receipt_kind": receipt_profile.receipt_kind(),
            "verifier_parameters": receipt_profile.verifier_parameters()
        },
        "replay_profile": REPLAY_PROFILE_ID,
        "root": receipt_report(&tree.root)?,
        "schema": REPORT_SCHEMA,
        "status": "retained_exact_four_leaf_two_level_receipts_verified"
    });
    serde_json::to_string(&report)
        .map(VerifiedReplayReport::from_verified_json)
        .map_err(|_| ReplayError::ReportEncoding)
}

pub fn rejection_report(error: ReplayError) -> String {
    json!({
        "context": error.context(),
        "error_code": error.code(),
        "ok": false,
        "schema": REPORT_SCHEMA,
        "status": "rejected",
        "verifier_code": error.verifier_code()
    })
    .to_string()
}

fn verify_tree(paths: &BundlePaths) -> Result<VerifiedTree, ReplayError> {
    let leaves: Vec<VerifiedNodeReceiptV3> = LEAF_NAMES
        .iter()
        .map(|name| verify_receipt(paths, name, ADAPTER_ID))
        .collect::<Result<_, _>>()?;
    let level_one_policy = StructuralAggregatePolicyV1::level_one_adapter_children(ADAPTER_ID);
    let left = verify_exact_node(
        paths,
        LEVEL_ONE_NAMES[0],
        node_input(LEVEL_ONE_ID, &leaves[0..2]),
        level_one_policy,
    )?;
    let right = verify_exact_node(
        paths,
        LEVEL_ONE_NAMES[1],
        node_input(LEVEL_ONE_ID, &leaves[2..4]),
        level_one_policy,
    )?;
    let level_one = vec![left, right];
    let root = verify_exact_node(
        paths,
        ROOT_NAME,
        node_input(LEVEL_TWO_ID, &level_one),
        StructuralAggregatePolicyV1::level_two_level_one_children(LEVEL_ONE_ID),
    )?;
    Ok(VerifiedTree {
        leaves,
        level_one,
        root,
    })
}

fn verify_receipt(
    paths: &BundlePaths,
    name: &'static str,
    image_id: [u32; 8],
) -> Result<VerifiedNodeReceiptV3, ReplayError> {
    let bytes = read_bounded_regular_file(paths, name)?;
    require_retained_artifact_binding(name, &bytes)?;
    VerifiedNodeReceiptV3::verify_canonical_succinct_bytes(&bytes, image_id)
        .map_err(|error| ReplayError::ReceiptVerification(name, error.code()))
}

fn verify_exact_node(
    paths: &BundlePaths,
    name: &'static str,
    input: StructuralAggregateInputV1,
    policy: StructuralAggregatePolicyV1,
) -> Result<VerifiedNodeReceiptV3, ReplayError> {
    let expected = compose_structural_aggregate_after_receipt_verification_v1(&input, policy)
        .map_err(|_| ReplayError::StructuralComposition(name))?;
    let bytes = read_bounded_regular_file(paths, name)?;
    require_retained_artifact_binding(name, &bytes)?;
    VerifiedNodeReceiptV3::verify_exact_succinct_bytes(
        &bytes,
        input.expected_self_image_id,
        &expected.journal,
    )
    .map_err(|error| ReplayError::ReceiptVerification(name, error.code()))
}

fn node_input(
    expected_self_image_id: [u32; 8],
    children: &[VerifiedNodeReceiptV3],
) -> StructuralAggregateInputV1 {
    StructuralAggregateInputV1 {
        expected_self_image_id,
        child_journal_bytes: children
            .iter()
            .map(|child| child.receipt().journal.bytes.clone())
            .collect(),
    }
}

fn verify_expected_root(tree: &VerifiedTree) -> Result<(), ReplayError> {
    let journal = tree.root.journal();
    let journal_hash = hex::encode(
        journal
            .canonical_hash()
            .map_err(|_| ReplayError::RootBinding)?
            .as_bytes(),
    );
    if journal_hash != EXPECTED_ROOT_JOURNAL_HASH
        || journal.node_level().get() != 2
        || journal.leaf_count() != 4
        || journal.operation_count() != 4
        || journal.subtree_node_count() != 7
        || journal.immediate_child_count() != 2
        || journal.partition().start() != 0
        || journal.partition().end_exclusive() != 4
    {
        return Err(ReplayError::RootBinding);
    }
    Ok(())
}

fn verify_root_seal_mutation(
    paths: &BundlePaths,
    tree: &VerifiedTree,
) -> Result<Value, ReplayError> {
    let candidate_bytes = read_bounded_regular_file(paths, MUTATION_NAME)?;
    require_retained_artifact_binding(MUTATION_NAME, &candidate_bytes)?;
    let candidate = decode_canonical_candidate(&candidate_bytes, MUTATION_NAME)?;
    let mutation = require_exact_root_seal_mutation(tree.root.receipt(), &candidate)?;
    let reject = VerifiedNodeReceiptV3::verify_exact_succinct_bytes(
        &candidate_bytes,
        LEVEL_TWO_ID,
        tree.root.journal(),
    )
    .err()
    .ok_or(ReplayError::MutationAccepted)?;
    if reject != VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed {
        return Err(ReplayError::MutationRejectClass(
            MUTATION_NAME,
            reject.code(),
        ));
    }
    let source_bytes = canonical_receipt_bytes(tree.root.receipt(), ROOT_NAME)?;
    Ok(json!({
        "candidate_accepted": false,
        "mutated_receipt_sha256": sha256_hex(&candidate_bytes),
        "mutation": {
            "kind": "succinct_seal_word_xor_lsb_v1",
            "seal_word_count": mutation.word_count,
            "seal_word_index": mutation.word_index,
            "seal_word_mutated": mutation.mutated_word,
            "seal_word_original": mutation.original_word,
            "xor_mask": 1
        },
        "reject_code": reject.code(),
        "source_receipt_sha256": sha256_hex(&source_bytes)
    }))
}

fn decode_canonical_candidate(bytes: &[u8], name: &'static str) -> Result<Receipt, ReplayError> {
    let receipt: Receipt =
        serde_json::from_slice(bytes).map_err(|_| ReplayError::ReceiptDecode(name))?;
    if canonical_receipt_bytes(&receipt, name)? != bytes {
        return Err(ReplayError::ReceiptNonCanonical(name));
    }
    Ok(receipt)
}

fn require_exact_root_seal_mutation(
    source: &Receipt,
    candidate: &Receipt,
) -> Result<SealWordMutation, ReplayError> {
    let InnerReceipt::Succinct(source_inner) = &source.inner else {
        return Err(ReplayError::MutationShape);
    };
    let InnerReceipt::Succinct(candidate_inner) = &candidate.inner else {
        return Err(ReplayError::MutationShape);
    };
    let mutation = require_exact_seal_word_mutation(&source_inner.seal, &candidate_inner.seal)?;
    let mut restored = candidate.clone();
    let InnerReceipt::Succinct(restored_inner) = &mut restored.inner else {
        return Err(ReplayError::MutationShape);
    };
    restored_inner.seal[mutation.word_index] = mutation.original_word;
    if canonical_receipt_bytes(&restored, MUTATION_NAME)?
        != canonical_receipt_bytes(source, ROOT_NAME)?
    {
        return Err(ReplayError::MutationShape);
    }
    Ok(mutation)
}

fn require_exact_seal_word_mutation(
    source: &[u32],
    candidate: &[u32],
) -> Result<SealWordMutation, ReplayError> {
    if source.is_empty() || source.len() != candidate.len() {
        return Err(ReplayError::MutationShape);
    }
    let mut difference = None;
    for (index, (original, mutated)) in source
        .iter()
        .copied()
        .zip(candidate.iter().copied())
        .enumerate()
    {
        if original == mutated {
            continue;
        }
        if difference.is_some() {
            return Err(ReplayError::MutationShape);
        }
        difference = Some((index, original, mutated));
    }
    let Some((word_index, original_word, mutated_word)) = difference else {
        return Err(ReplayError::MutationShape);
    };
    if word_index != ROOT_SEAL_MUTATION_WORD_INDEX || original_word ^ mutated_word != 1 {
        return Err(ReplayError::MutationShape);
    }
    Ok(SealWordMutation {
        word_count: source.len(),
        word_index,
        original_word,
        mutated_word,
    })
}

fn canonical_receipt_bytes(receipt: &Receipt, name: &'static str) -> Result<Vec<u8>, ReplayError> {
    let bytes = serde_json::to_vec(receipt).map_err(|_| ReplayError::ReceiptDecode(name))?;
    if bytes.is_empty() || bytes.len() > MAX_CANONICAL_RECEIPT_BYTES_V3 {
        return Err(ReplayError::ReceiptArtifact(name));
    }
    Ok(bytes)
}

fn receipt_report(node: &VerifiedNodeReceiptV3) -> Result<Value, ReplayError> {
    let receipt_bytes =
        canonical_receipt_bytes(node.receipt(), "verified_receipt_internal_encoding")?;
    let journal_hash = node
        .journal()
        .canonical_hash()
        .map_err(|_| ReplayError::ReportEncoding)?;
    Ok(json!({
        "count_unit": {
            "id": hex::encode(node.journal().count_unit_id().as_bytes()),
            "label": "source_transition_receipt_v3"
        },
        "immediate_child_count": node.journal().immediate_child_count(),
        "journal_hash": hex::encode(journal_hash.as_bytes()),
        "journal_sha256": sha256_hex(&node.receipt().journal.bytes),
        "leaf_count": node.journal().leaf_count(),
        "node_level": node.journal().node_level().get(),
        "operation_count": node.journal().operation_count(),
        "partition_end_exclusive": node.journal().partition().end_exclusive(),
        "partition_start": node.journal().partition().start(),
        "receipt_bytes": receipt_bytes.len(),
        "receipt_sha256": sha256_hex(&receipt_bytes),
        "subtree_node_count": node.journal().subtree_node_count()
    }))
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

#[cfg(test)]
mod tests;
