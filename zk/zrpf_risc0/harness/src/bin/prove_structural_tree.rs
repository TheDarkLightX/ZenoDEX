use std::{
    env, fs,
    io::{Read, Write},
    path::{Path, PathBuf},
};

use risc0_zkvm::{
    compute_image_id, default_executor, default_prover, sha::Digestible, Digest, ExecutorEnv,
    InnerReceipt, MaybePruned, ProverOpts, Receipt, ReceiptClaim,
};
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use zenodex_zrpf_risc0_aggregate_shared::{
    compose_structural_aggregate_after_receipt_verification_v1,
    encode_structural_aggregate_input_v1, StructuralAggregateInputV1, StructuralAggregatePolicyV1,
};
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF, ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
    ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ELF, ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
    ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF, ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
};
use zenodex_zrpf_risc0_verifier::VerifiedNodeReceiptV3;

const MAX_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;

struct Options {
    leaf_paths: [PathBuf; 4],
    output_dir: PathBuf,
    missing_assumption: bool,
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
    let leaves: Vec<VerifiedNodeReceiptV3> = options
        .leaf_paths
        .iter()
        .enumerate()
        .map(|(index, path)| {
            load_verified_receipt(path, ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID)
                .map_err(|error| format!("leaf {index}: {error}"))
        })
        .collect::<Result<_, _>>()?;
    let l1_policy = StructuralAggregatePolicyV1::level_one_adapter_children(
        ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
    );
    let left_input = node_input(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID, &leaves[0..2]);
    if options.missing_assumption {
        return execute_missing_assumption_reject(&left_input, &leaves[0]);
    }
    prepare_output_dir(&options.output_dir)?;
    let left_path = options.output_dir.join("structural-l1-left.receipt.json");
    let right_path = options.output_dir.join("structural-l1-right.receipt.json");
    let root_path = options.output_dir.join("structural-l2-root.receipt.json");
    for path in [&left_path, &right_path, &root_path] {
        if path.exists() {
            return Err("structural tree output already exists".to_owned());
        }
    }

    let left = prove_node(
        &left_input,
        l1_policy,
        &leaves[0..2],
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
    )?;
    persist_receipt(&left_path, left.receipt())?;
    let right_input = node_input(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID, &leaves[2..4]);
    let right = prove_node(
        &right_input,
        l1_policy,
        &leaves[2..4],
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
    )?;
    persist_receipt(&right_path, right.receipt())?;

    let level_one_nodes = vec![left, right];
    let root_input = node_input(
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
        &level_one_nodes,
    );
    let root = prove_node(
        &root_input,
        StructuralAggregatePolicyV1::level_two_level_one_children(
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
        ),
        &level_one_nodes,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ELF,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
    )?;
    persist_receipt(&root_path, root.receipt())?;
    println!(
        "{}",
        json!({
            "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
            "leaf_receipts": leaves.iter().map(receipt_report).collect::<Result<Vec<_>, _>>()?,
            "level_one_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID).to_string(),
            "level_one_nodes": level_one_nodes.iter().map(receipt_report).collect::<Result<Vec<_>, _>>()?,
            "level_two_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID).to_string(),
            "nonclaims": [
                "structural roots bind child commitments without proving their application semantics",
                "temporary compiler-visible paths are not release identities",
                "no settlement, ledger admission, data availability, conservation, or production authority"
            ],
            "ok": true,
            "root": receipt_report(&root)?,
            "status": "temporary_path_four_leaf_two_level_structural_tree_verified",
        })
    );
    Ok(())
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args: Vec<String> = args.into_iter().collect();
    if args.len() != 5 && args.len() != 6 {
        return Err(usage().to_owned());
    }
    let missing_assumption = args
        .get(5)
        .is_some_and(|value| value == "--missing-assumption");
    if args.len() == 6 && !missing_assumption {
        return Err(usage().to_owned());
    }
    let leaf_paths: [PathBuf; 4] = args[..4]
        .iter()
        .map(PathBuf::from)
        .collect::<Vec<_>>()
        .try_into()
        .map_err(|_| usage().to_owned())?;
    Ok(Options {
        leaf_paths,
        output_dir: PathBuf::from(&args[4]),
        missing_assumption,
    })
}

fn usage() -> &'static str {
    "usage: prove_structural_tree <leaf0.receipt.json> <leaf1.receipt.json> <leaf2.receipt.json> <leaf3.receipt.json> <output-dir> [--missing-assumption]"
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

fn load_verified_receipt(
    path: &Path,
    expected_image_id: [u32; 8],
) -> Result<VerifiedNodeReceiptV3, String> {
    let bytes = read_bounded_file(path)?;
    let receipt: Receipt =
        serde_json::from_slice(&bytes).map_err(|error| format!("receipt JSON: {error}"))?;
    let canonical = canonical_receipt_bytes(&receipt)?;
    if canonical != bytes {
        return Err("receipt JSON is not canonical".to_owned());
    }
    VerifiedNodeReceiptV3::verify_canonical_succinct(receipt, expected_image_id)
        .map_err(|error| format!("verified node boundary: {error}"))
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

fn prove_node(
    input: &StructuralAggregateInputV1,
    policy: StructuralAggregatePolicyV1,
    children: &[VerifiedNodeReceiptV3],
    elf: &[u8],
    image_id: [u32; 8],
) -> Result<VerifiedNodeReceiptV3, String> {
    let expected = compose_structural_aggregate_after_receipt_verification_v1(input, policy)
        .map_err(|error| format!("host structural composition rejected: {error}"))?;
    let input_bytes = encode_structural_aggregate_input_v1(input)
        .map_err(|error| format!("structural input encode: {error}"))?;
    let input_length =
        u32::try_from(input_bytes.len()).map_err(|_| "structural input length exceeds u32")?;
    let mut builder = ExecutorEnv::builder();
    builder
        .write_slice(&[input_length])
        .write_slice(&input_bytes);
    for child in children {
        builder.add_assumption(child.receipt().clone());
    }
    let executor_env = builder
        .build()
        .map_err(|error| format!("structural executor environment: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(executor_env, elf, &ProverOpts::succinct())
        .map_err(|error| format!("structural proving failed: {error}"))?
        .receipt;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err("structural prover returned a non-Succinct receipt".to_owned());
    }
    VerifiedNodeReceiptV3::verify_exact_succinct(receipt, image_id, &expected.journal)
        .map_err(|error| format!("structural receipt verification failed: {error}"))
}

fn execute_missing_assumption_reject(
    input: &StructuralAggregateInputV1,
    missing_child: &VerifiedNodeReceiptV3,
) -> Result<(), String> {
    let input_bytes = encode_structural_aggregate_input_v1(input)
        .map_err(|error| format!("structural input encode: {error}"))?;
    let input_length =
        u32::try_from(input_bytes.len()).map_err(|_| "structural input length exceeds u32")?;
    let executor_env = ExecutorEnv::builder()
        .write_slice(&[input_length])
        .write_slice(&input_bytes)
        .build()
        .map_err(|error| format!("missing-assumption environment: {error}"))?;
    let journal_digest = missing_child.receipt().journal.bytes.as_slice().digest();
    let claim_digest = ReceiptClaim::ok(
        ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
        MaybePruned::<Vec<u8>>::Pruned(journal_digest),
    )
    .digest();
    let expected_reason = format!(
        "sys_verify_integrity: no receipt found to resolve assumption: claim digest {claim_digest}, control root {}",
        Digest::ZERO
    );
    match default_executor().execute(executor_env, ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF) {
        Ok(_) => Err("structural aggregate accepted a missing child assumption".to_owned()),
        Err(error)
            if error
                .chain()
                .any(|cause| cause.to_string() == expected_reason) =>
        {
            println!(
                "{}",
                json!({
                    "aggregate_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID).to_string(),
                    "ok": true,
                    "status": "structural_l1_missing_child_assumption_rejected",
                })
            );
            Ok(())
        }
        Err(error) => Err(format!(
            "structural aggregate failed at the wrong missing-assumption boundary: {error:#}"
        )),
    }
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

fn prepare_output_dir(path: &Path) -> Result<(), String> {
    fs::create_dir_all(path).map_err(|error| format!("create output directory: {error}"))?;
    let metadata = fs::symlink_metadata(path)
        .map_err(|error| format!("output directory metadata: {error}"))?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        return Err("output path must be a non-symlink directory".to_owned());
    }
    Ok(())
}

fn persist_receipt(path: &Path, receipt: &Receipt) -> Result<(), String> {
    let bytes = canonical_receipt_bytes(receipt)?;
    let mut output = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("create structural receipt: {error}"))?;
    output
        .write_all(&bytes)
        .map_err(|error| format!("write structural receipt: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync structural receipt: {error}"))
}

fn read_bounded_file(path: &Path) -> Result<Vec<u8>, String> {
    let input = fs::File::open(path).map_err(|error| format!("open receipt: {error}"))?;
    let metadata = input
        .metadata()
        .map_err(|error| format!("receipt metadata: {error}"))?;
    if !metadata.is_file() || metadata.len() > MAX_RECEIPT_BYTES as u64 {
        return Err("receipt must be a bounded regular file".to_owned());
    }
    let mut bytes = Vec::new();
    input
        .take((MAX_RECEIPT_BYTES + 1) as u64)
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

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use super::parse_options;

    fn values(extra: &[&str]) -> Vec<String> {
        ["a", "b", "c", "d", "out"]
            .into_iter()
            .chain(extra.iter().copied())
            .map(str::to_owned)
            .collect()
    }

    #[test]
    fn exact_cli_shape_accepts_positive_and_negative_modes() {
        assert!(!parse_options(values(&[])).unwrap().missing_assumption);
        assert!(
            parse_options(values(&["--missing-assumption"]))
                .unwrap()
                .missing_assumption
        );
    }

    #[test]
    fn unknown_or_extra_cli_arguments_reject() {
        assert!(parse_options(values(&["--unknown"])).is_err());
        assert!(parse_options(values(&["--missing-assumption", "extra"])).is_err());
    }
}
