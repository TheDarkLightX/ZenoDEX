use std::{
    env, fs,
    io::Read,
    path::{Path, PathBuf},
};

use risc0_zkvm::{compute_image_id, Digest, InnerReceipt, Receipt};
use serde::Serialize;
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use zenodex_zrpf_risc0_aggregate_shared::{
    compose_structural_aggregate_after_receipt_verification_v1, StructuralAggregateInputV1,
    StructuralAggregatePolicyV1,
};
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF, ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
    ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ELF, ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
    ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF, ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
};
use zenodex_zrpf_risc0_verifier::{VerifiedNodeReceiptErrorV3, VerifiedNodeReceiptV3};

const MAX_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_RECEIPT_BYTES_U64: u64 = 16 * 1_024 * 1_024;
const MAX_RECEIPT_READ_BYTES_U64: u64 = MAX_RECEIPT_BYTES_U64 + 1;
const ROOT_SEAL_MUTATION_WORD_INDEX: usize = 1;

struct Options {
    leaf_paths: [PathBuf; 4],
    level_one_paths: [PathBuf; 2],
    root_path: PathBuf,
    mode: VerificationMode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum VerificationMode {
    VerifyTree,
    ExpectRootSealReject { candidate_path: PathBuf },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SealWordMutation {
    word_count: usize,
    word_index: usize,
    original_word: u32,
    mutated_word: u32,
}

#[derive(Serialize)]
struct SealMutationRejectReport<'a> {
    baseline_tree_verified: bool,
    candidate_accepted: bool,
    control_passed: bool,
    expected_image_id: String,
    journal_protocol_hash: String,
    journal_sha256: String,
    mutated_receipt_sha256: String,
    mutation: SealMutationReport<'a>,
    reject: TypedRejectReport<'a>,
    schema: &'a str,
    source_receipt_sha256: String,
    status: &'a str,
}

#[derive(Serialize)]
struct SealMutationReport<'a> {
    kind: &'a str,
    seal_word_count: usize,
    seal_word_index: usize,
    seal_word_mutated: u32,
    seal_word_original: u32,
    xor_mask: u32,
}

#[derive(Serialize)]
struct TypedRejectReport<'a> {
    boundary: &'a str,
    code: &'a str,
}

struct VerifiedStructuralTree {
    leaves: Vec<VerifiedNodeReceiptV3>,
    level_one_nodes: Vec<VerifiedNodeReceiptV3>,
    root: VerifiedNodeReceiptV3,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let options = parse_options(env::args().skip(1))?;
    validate_methods()?;
    let tree = verify_tree(&options)?;
    let report = match &options.mode {
        VerificationMode::VerifyTree => tree_report(&tree)?.to_string(),
        VerificationMode::ExpectRootSealReject { candidate_path } => {
            root_seal_mutation_report(&tree, candidate_path)?
        }
    };
    println!("{report}");
    Ok(())
}

fn tree_report(tree: &VerifiedStructuralTree) -> Result<Value, String> {
    Ok(json!({
        "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
        "leaf_receipts": tree.leaves.iter().map(receipt_report).collect::<Result<Vec<_>, _>>()?,
        "level_one_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID).to_string(),
        "level_one_nodes": tree.level_one_nodes.iter().map(receipt_report).collect::<Result<Vec<_>, _>>()?,
        "level_two_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID).to_string(),
        "nonclaims": [
            "structural roots bind child commitments without proving their application semantics",
            "temporary compiler-visible paths are not release identities",
            "no settlement, ledger admission, data availability, conservation, or production authority"
        ],
        "ok": true,
        "root": receipt_report(&tree.root)?,
        "status": "persisted_four_leaf_two_level_structural_tree_verified",
    }))
}

fn root_seal_mutation_report(
    tree: &VerifiedStructuralTree,
    candidate_path: &Path,
) -> Result<String, String> {
    let source_receipt_bytes = canonical_receipt_bytes(tree.root.receipt())?;
    let mutated_receipt = load_canonical_receipt(candidate_path)
        .map_err(|error| format!("mutated root candidate: {error}"))?;
    let mutated_receipt_bytes = canonical_receipt_bytes(&mutated_receipt)?;
    let mutation = require_exact_root_seal_mutation(tree.root.receipt(), &mutated_receipt)?;
    let reject = match VerifiedNodeReceiptV3::verify_exact_succinct(
        mutated_receipt,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
        tree.root.journal(),
    ) {
        Ok(_) => return Err("mutated root Succinct seal was accepted".to_owned()),
        Err(error) => error,
    };
    if reject != VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed {
        return Err(format!(
            "mutated root rejected at unexpected boundary: {}",
            reject.code()
        ));
    }
    serde_json::to_string(&SealMutationRejectReport {
        baseline_tree_verified: true,
        candidate_accepted: false,
        control_passed: true,
        expected_image_id: Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID).to_string(),
        journal_protocol_hash: hex::encode(
            tree.root
                .journal()
                .canonical_hash()
                .map_err(|error| format!("journal hash: {error}"))?
                .as_bytes(),
        ),
        journal_sha256: sha256_hex(&tree.root.receipt().journal.bytes),
        mutated_receipt_sha256: sha256_hex(&mutated_receipt_bytes),
        mutation: SealMutationReport {
            kind: "succinct_seal_word_xor_lsb_v1",
            seal_word_count: mutation.word_count,
            seal_word_index: mutation.word_index,
            seal_word_mutated: mutation.mutated_word,
            seal_word_original: mutation.original_word,
            xor_mask: 1,
        },
        reject: TypedRejectReport {
            boundary: "VerifiedNodeReceiptV3::verify_exact_succinct",
            code: reject.code(),
        },
        schema: "zenodex/zrpf_v3_structural_root_seal_mutation_reject/v1",
        source_receipt_sha256: sha256_hex(&source_receipt_bytes),
        status: "structural_l2_root_succinct_seal_mutation_rejected",
    })
    .map_err(|error| format!("seal mutation report encode: {error}"))
}

fn require_exact_root_seal_mutation(
    source: &Receipt,
    candidate: &Receipt,
) -> Result<SealWordMutation, String> {
    let InnerReceipt::Succinct(source_inner) = &source.inner else {
        return Err("source root receipt is not Succinct".to_owned());
    };
    let InnerReceipt::Succinct(candidate_inner) = &candidate.inner else {
        return Err("mutated root candidate is not Succinct".to_owned());
    };
    let mutation = require_exact_seal_word_mutation(&source_inner.seal, &candidate_inner.seal)?;

    let mut restored = candidate.clone();
    let InnerReceipt::Succinct(restored_inner) = &mut restored.inner else {
        return Err("mutated root candidate restoration failed".to_owned());
    };
    restored_inner.seal[mutation.word_index] = mutation.original_word;
    if canonical_receipt_bytes(&restored)? != canonical_receipt_bytes(source)? {
        return Err("mutated root candidate changes non-seal receipt fields".to_owned());
    }
    Ok(mutation)
}

fn require_exact_seal_word_mutation(
    source: &[u32],
    candidate: &[u32],
) -> Result<SealWordMutation, String> {
    if source.is_empty() || source.len() != candidate.len() {
        return Err("Succinct seal mutation changes the seal length".to_owned());
    }
    let differences: Vec<(usize, u32, u32)> = source
        .iter()
        .copied()
        .zip(candidate.iter().copied())
        .enumerate()
        .filter_map(|(index, (original, mutated))| {
            (original != mutated).then_some((index, original, mutated))
        })
        .collect();
    let [(word_index, original_word, mutated_word)] = differences.as_slice() else {
        return Err("Succinct seal candidate must change exactly one word".to_owned());
    };
    if *word_index != ROOT_SEAL_MUTATION_WORD_INDEX || original_word ^ mutated_word != 1 {
        return Err("Succinct seal candidate must XOR the pinned word low bit".to_owned());
    }
    Ok(SealWordMutation {
        word_count: source.len(),
        word_index: *word_index,
        original_word: *original_word,
        mutated_word: *mutated_word,
    })
}

fn verify_tree(options: &Options) -> Result<VerifiedStructuralTree, String> {
    // Only this sealed boundary turns receipt bytes into usable child nodes.
    let leaves: Vec<VerifiedNodeReceiptV3> = options
        .leaf_paths
        .iter()
        .enumerate()
        .map(|(index, path)| {
            let receipt =
                load_canonical_receipt(path).map_err(|error| format!("leaf {index}: {error}"))?;
            VerifiedNodeReceiptV3::verify_canonical_succinct(
                receipt,
                ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
            )
            .map_err(|error| format!("leaf {index} sealed verification: {error}"))
        })
        .collect::<Result<_, _>>()?;

    let level_one_policy = StructuralAggregatePolicyV1::level_one_adapter_children(
        ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
    );
    let left = verify_exact_node(
        &options.level_one_paths[0],
        node_input(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID, &leaves[0..2]),
        level_one_policy,
        "level-one left",
    )?;
    let right = verify_exact_node(
        &options.level_one_paths[1],
        node_input(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID, &leaves[2..4]),
        level_one_policy,
        "level-one right",
    )?;

    let level_one_nodes = vec![left, right];
    let root = verify_exact_node(
        &options.root_path,
        node_input(
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
            &level_one_nodes,
        ),
        StructuralAggregatePolicyV1::level_two_level_one_children(
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
        ),
        "level-two root",
    )?;
    Ok(VerifiedStructuralTree {
        leaves,
        level_one_nodes,
        root,
    })
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args: Vec<String> = args.into_iter().collect();
    if !matches!(args.len(), 7 | 9) || args.iter().any(String::is_empty) {
        return Err(usage().to_owned());
    }
    let mode = if args.len() == 7 {
        VerificationMode::VerifyTree
    } else {
        if args[7] != "--expect-root-seal-reject" {
            return Err(usage().to_owned());
        }
        VerificationMode::ExpectRootSealReject {
            candidate_path: PathBuf::from(&args[8]),
        }
    };
    let leaf_paths: [PathBuf; 4] = args[..4]
        .iter()
        .map(PathBuf::from)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| usage().to_owned())?;
    let level_one_paths = [PathBuf::from(&args[4]), PathBuf::from(&args[5])];
    Ok(Options {
        leaf_paths,
        level_one_paths,
        root_path: PathBuf::from(&args[6]),
        mode,
    })
}

fn usage() -> &'static str {
    "usage: verify_structural_tree <leaf0.receipt.json> <leaf1.receipt.json> <leaf2.receipt.json> <leaf3.receipt.json> <l1-left.receipt.json> <l1-right.receipt.json> <l2-root.receipt.json> [--expect-root-seal-reject <mutated-root.receipt.json>]"
}

fn validate_methods() -> Result<(), String> {
    for (name, elf, image_id) in [
        (
            "adapter",
            ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF,
            ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
        ),
        (
            "aggregate L1",
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF,
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
        ),
        (
            "aggregate L2",
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ELF,
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
        ),
    ] {
        if elf.is_empty() || image_id.iter().all(|word| *word == 0) {
            return Err(format!("{name} method is a placeholder"));
        }
        if compute_image_id(elf).map_err(|error| format!("compute {name} image: {error}"))?
            != Digest::from(image_id)
        {
            return Err(format!("{name} image ID mismatch"));
        }
    }
    Ok(())
}

fn verify_exact_node(
    path: &Path,
    input: StructuralAggregateInputV1,
    policy: StructuralAggregatePolicyV1,
    label: &str,
) -> Result<VerifiedNodeReceiptV3, String> {
    let expected_image_id = input.expected_self_image_id;
    let expected = compose_structural_aggregate_after_receipt_verification_v1(&input, policy)
        .map_err(|error| format!("{label} host structural composition rejected: {error}"))?;
    let receipt = load_canonical_receipt(path).map_err(|error| format!("{label}: {error}"))?;
    VerifiedNodeReceiptV3::verify_exact_succinct(receipt, expected_image_id, &expected.journal)
        .map_err(|error| format!("{label} exact sealed verification: {error}"))
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

fn load_canonical_receipt(path: &Path) -> Result<Receipt, String> {
    let bytes = read_bounded_regular_file(path)?;
    let receipt: Receipt =
        serde_json::from_slice(&bytes).map_err(|error| format!("receipt JSON: {error}"))?;
    if canonical_receipt_bytes(&receipt)? != bytes {
        return Err("receipt JSON is not canonical".to_owned());
    }
    Ok(receipt)
}

fn read_bounded_regular_file(path: &Path) -> Result<Vec<u8>, String> {
    let metadata =
        fs::symlink_metadata(path).map_err(|error| format!("receipt metadata: {error}"))?;
    if !metadata.is_file()
        || metadata.file_type().is_symlink()
        || metadata.len() > MAX_RECEIPT_BYTES_U64
    {
        return Err("receipt must be a bounded non-symlink regular file".to_owned());
    }
    let input = fs::File::open(path).map_err(|error| format!("open receipt: {error}"))?;
    let mut bytes = Vec::new();
    input
        .take(MAX_RECEIPT_READ_BYTES_U64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read receipt: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_RECEIPT_BYTES {
        return Err("receipt byte length unsupported".to_owned());
    }
    Ok(bytes)
}

fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, String> {
    let bytes = serde_json::to_vec(receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_RECEIPT_BYTES {
        return Err("canonical receipt bytes exceed evidence bound".to_owned());
    }
    Ok(bytes)
}

fn receipt_report(node: &VerifiedNodeReceiptV3) -> Result<Value, String> {
    let receipt_bytes = canonical_receipt_bytes(node.receipt())?;
    Ok(json!({
        "immediate_child_count": node.journal().immediate_child_count(),
        "journal_hash": hex::encode(node.journal().canonical_hash().map_err(|error| format!("journal hash: {error}"))?.as_bytes()),
        "journal_sha256": sha256_hex(&node.receipt().journal.bytes),
        "leaf_count": node.journal().leaf_count(),
        "node_level": node.journal().node_level().get(),
        "operation_count": node.journal().operation_count(),
        "partition_end_exclusive": node.journal().partition().end_exclusive(),
        "partition_start": node.journal().partition().start(),
        "receipt_bytes": receipt_bytes.len(),
        "receipt_sha256": sha256_hex(&receipt_bytes),
        "subtree_node_count": node.journal().subtree_node_count(),
    }))
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use std::{error::Error, fs, path::PathBuf};

    use super::{
        parse_options, read_bounded_regular_file, require_exact_seal_word_mutation,
        VerificationMode, MAX_RECEIPT_READ_BYTES_U64,
    };

    fn values() -> Vec<String> {
        ["leaf0", "leaf1", "leaf2", "leaf3", "left", "right", "root"]
            .into_iter()
            .map(str::to_owned)
            .collect()
    }

    #[test]
    fn exact_cli_shape_maps_all_receipt_roles() -> Result<(), String> {
        let parsed = parse_options(values())?;
        assert_eq!(parsed.leaf_paths[0].to_string_lossy(), "leaf0");
        assert_eq!(parsed.leaf_paths[3].to_string_lossy(), "leaf3");
        assert_eq!(parsed.level_one_paths[0].to_string_lossy(), "left");
        assert_eq!(parsed.level_one_paths[1].to_string_lossy(), "right");
        assert_eq!(parsed.root_path.to_string_lossy(), "root");
        assert_eq!(parsed.mode, VerificationMode::VerifyTree);
        Ok(())
    }

    #[test]
    fn exact_cli_shape_accepts_seal_mutation_candidate() -> Result<(), String> {
        let mut args = values();
        args.extend([
            "--expect-root-seal-reject".to_owned(),
            "mutated-root.json".to_owned(),
        ]);
        let parsed = parse_options(args)?;
        assert_eq!(
            parsed.mode,
            VerificationMode::ExpectRootSealReject {
                candidate_path: PathBuf::from("mutated-root.json")
            }
        );
        Ok(())
    }

    #[test]
    fn seal_mutation_mode_rejects_unknown_option_or_empty_candidate() {
        let mut unknown = values();
        unknown.extend(["--unknown".to_owned(), "mutated.json".to_owned()]);
        assert!(parse_options(unknown).is_err());

        let mut empty = values();
        empty.extend(["--expect-root-seal-reject".to_owned(), String::new()]);
        assert!(parse_options(empty).is_err());
    }

    #[test]
    fn exact_seal_mutation_accepts_only_pinned_single_low_bit_change() -> Result<(), String> {
        let source = [10, 20, 30];
        let accepted = require_exact_seal_word_mutation(&source, &[10, 21, 30])?;
        assert_eq!(accepted.word_index, 1);
        assert_eq!(accepted.original_word, 20);
        assert_eq!(accepted.mutated_word, 21);

        for candidate in [
            vec![10, 20, 30],
            vec![11, 20, 30],
            vec![10, 22, 30],
            vec![10, 21, 31],
            vec![10, 21],
            Vec::new(),
        ] {
            assert!(require_exact_seal_word_mutation(&source, &candidate).is_err());
        }
        Ok(())
    }

    #[test]
    fn wrong_arity_or_empty_path_rejects() {
        assert!(parse_options(values().into_iter().take(6)).is_err());
        let mut empty = values();
        empty[4].clear();
        assert!(parse_options(empty).is_err());
        let mut extra = values();
        extra.push("extra".to_owned());
        assert!(parse_options(extra).is_err());
    }

    #[test]
    fn oversized_receipt_file_rejects_before_decode() -> Result<(), Box<dyn Error>> {
        let directory = isolated_test_directory("oversized");
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir(&directory)?;
        let receipt_path = directory.join("receipt.json");
        fs::File::create(&receipt_path)?.set_len(MAX_RECEIPT_READ_BYTES_U64)?;

        let result = read_bounded_regular_file(&receipt_path);
        fs::remove_dir_all(&directory)?;
        assert_eq!(
            result,
            Err("receipt must be a bounded non-symlink regular file".to_owned())
        );
        Ok(())
    }

    #[cfg(unix)]
    #[test]
    fn symlink_receipt_path_rejects_before_decode() -> Result<(), Box<dyn Error>> {
        use std::os::unix::fs::symlink;

        let directory = isolated_test_directory("symlink");
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir(&directory)?;
        let target_path = directory.join("target.json");
        let link_path = directory.join("receipt.json");
        fs::write(&target_path, b"{}")?;
        symlink(&target_path, &link_path)?;

        let result = read_bounded_regular_file(&link_path);
        fs::remove_dir_all(&directory)?;
        assert_eq!(
            result,
            Err("receipt must be a bounded non-symlink regular file".to_owned())
        );
        Ok(())
    }

    fn isolated_test_directory(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "zenodex-zrpf-verify-structural-tree-{label}-{}",
            std::process::id()
        ))
    }
}
