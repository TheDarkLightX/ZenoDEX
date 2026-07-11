use std::{
    env, fs,
    io::{Read, Write},
    path::{Path, PathBuf},
};

#[cfg(unix)]
use std::os::unix::fs::MetadataExt;

use risc0_zkvm::{
    compute_image_id, default_prover, Digest, ExecutorEnv, InnerReceipt, ProverOpts, Receipt,
};
use serde_json::json;
use sha2::{Digest as ShaDigest, Sha256};
use zenodex_zrpf_risc0_aggregate_shared::{
    compose_structural_aggregate_after_receipt_verification_v1,
    encode_structural_aggregate_input_v1, StructuralAggregateInputV1, StructuralAggregatePolicyV1,
};
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF, ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
    ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF, ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
};
use zenodex_zrpf_risc0_verifier::VerifiedNodeReceiptV3;

const MAX_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_RECEIPT_BYTES_U64: u64 = 16 * 1_024 * 1_024;
const MAX_RECEIPT_READ_BYTES_U64: u64 = MAX_RECEIPT_BYTES_U64 + 1;
const MAX_ADAPTER_RECEIPTS: usize = 8;

struct Options {
    receipt_out: PathBuf,
    adapter_receipt_paths: Vec<PathBuf>,
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

    // This sealed boundary authenticates every child before any child journal is
    // interpreted or used to derive the aggregate statement.
    let children = options
        .adapter_receipt_paths
        .iter()
        .enumerate()
        .map(|(index, path)| {
            load_verified_adapter_receipt(path)
                .map_err(|error| format!("adapter receipt {index}: {error}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    let input = structural_input(&children);
    let expected = compose_structural_aggregate_after_receipt_verification_v1(
        &input,
        StructuralAggregatePolicyV1::level_one_adapter_children(
            ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
        ),
    )
    .map_err(|error| format!("host structural composition rejected: {error}"))?;
    let node = prove_level_one(&input, &children, &expected.journal)?;
    let receipt_bytes = canonical_receipt_bytes(node.receipt())?;
    persist_receipt(&options.receipt_out, &receipt_bytes)?;

    println!(
        "{}",
        json!({
            "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
            "child_count": children.len(),
            "journal_hash": hex::encode(node.journal().canonical_hash().map_err(|error| format!("journal hash: {error}"))?.as_bytes()),
            "journal_sha256": sha256_hex(&node.receipt().journal.bytes),
            "level_one_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID).to_string(),
            "nonclaims": [
                "the structural L1 receipt does not prove application-level semantic composition",
                "proof generation does not grant ledger, settlement, release, or production authority"
            ],
            "ok": true,
            "receipt_bytes": receipt_bytes.len(),
            "receipt_sha256": sha256_hex(&receipt_bytes),
            "receipt_written": true,
            "status": "bounded_structural_l1_succinct_receipt_verified",
        })
    );
    Ok(())
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args: Vec<String> = args.into_iter().collect();
    if !(3..=MAX_ADAPTER_RECEIPTS + 2).contains(&args.len())
        || args[0] != "--receipt-out"
        || args[1].is_empty()
        || args[1].starts_with("--")
        || args[2..]
            .iter()
            .any(|value| value.is_empty() || value.starts_with("--"))
    {
        return Err(usage().to_owned());
    }
    Ok(Options {
        receipt_out: PathBuf::from(&args[1]),
        adapter_receipt_paths: args[2..].iter().map(PathBuf::from).collect(),
    })
}

fn usage() -> &'static str {
    "usage: prove_structural_l1 --receipt-out <l1.receipt.json> <adapter0.receipt.json> [adapter1.receipt.json ... adapter7.receipt.json]"
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
    ] {
        if elf.is_empty() || image_id.iter().all(|word| *word == 0) {
            return Err(format!("{name} method is a placeholder"));
        }
        let computed =
            compute_image_id(elf).map_err(|error| format!("compute {name} image ID: {error}"))?;
        if computed != Digest::from(image_id) {
            return Err(format!("{name} image ID mismatch"));
        }
    }
    Ok(())
}

fn load_verified_adapter_receipt(path: &Path) -> Result<VerifiedNodeReceiptV3, String> {
    let receipt_bytes = read_bounded_regular_file(path)?;
    VerifiedNodeReceiptV3::verify_canonical_succinct_bytes(
        &receipt_bytes,
        ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
    )
    .map_err(|error| format!("sealed adapter verification: {error}"))
}

fn structural_input(children: &[VerifiedNodeReceiptV3]) -> StructuralAggregateInputV1 {
    StructuralAggregateInputV1 {
        expected_self_image_id: ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
        child_journal_bytes: children
            .iter()
            .map(|child| child.receipt().journal.bytes.clone())
            .collect(),
    }
}

fn prove_level_one(
    input: &StructuralAggregateInputV1,
    children: &[VerifiedNodeReceiptV3],
    expected_journal: &zenodex_zrpf_protocol_v3::NodeJournalV3,
) -> Result<VerifiedNodeReceiptV3, String> {
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
        .map_err(|error| format!("structural L1 executor environment: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("structural L1 proving failed: {error}"))?
        .receipt;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err("structural L1 prover returned a non-Succinct receipt".to_owned());
    }
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    VerifiedNodeReceiptV3::verify_exact_succinct_bytes(
        &receipt_bytes,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
        expected_journal,
    )
    .map_err(|error| format!("structural L1 receipt verification failed: {error}"))
}

fn read_bounded_regular_file(path: &Path) -> Result<Vec<u8>, String> {
    let path_metadata =
        fs::symlink_metadata(path).map_err(|error| format!("receipt metadata: {error}"))?;
    if !path_metadata.is_file()
        || path_metadata.file_type().is_symlink()
        || path_metadata.len() > MAX_RECEIPT_BYTES_U64
    {
        return Err("receipt must be a bounded non-symlink regular file".to_owned());
    }
    let mut input = fs::File::open(path).map_err(|error| format!("open receipt: {error}"))?;
    let opened_metadata = input
        .metadata()
        .map_err(|error| format!("opened receipt metadata: {error}"))?;
    if !same_file_version(&path_metadata, &opened_metadata) {
        return Err("receipt path changed while it was opened".to_owned());
    }
    let mut bytes = Vec::new();
    (&mut input)
        .take(MAX_RECEIPT_READ_BYTES_U64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read receipt: {error}"))?;
    let final_metadata = input
        .metadata()
        .map_err(|error| format!("final receipt metadata: {error}"))?;
    if !same_file_version(&opened_metadata, &final_metadata) {
        return Err("receipt changed while it was read".to_owned());
    }
    if bytes.is_empty() || bytes.len() > MAX_RECEIPT_BYTES {
        return Err("receipt byte length unsupported".to_owned());
    }
    Ok(bytes)
}

#[cfg(unix)]
fn same_file_version(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.dev() == right.dev()
        && left.ino() == right.ino()
        && left.mode() == right.mode()
        && left.size() == right.size()
        && left.mtime() == right.mtime()
        && left.mtime_nsec() == right.mtime_nsec()
        && left.ctime() == right.ctime()
        && left.ctime_nsec() == right.ctime_nsec()
}

#[cfg(not(unix))]
fn same_file_version(left: &fs::Metadata, right: &fs::Metadata) -> bool {
    left.is_file() == right.is_file()
        && left.len() == right.len()
        && left.modified().ok() == right.modified().ok()
}

fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, String> {
    let bytes = serde_json::to_vec(receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_RECEIPT_BYTES {
        return Err("canonical receipt bytes exceed evidence bound".to_owned());
    }
    Ok(bytes)
}

fn persist_receipt(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut output = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("create structural L1 receipt: {error}"))?;
    output
        .write_all(bytes)
        .map_err(|error| format!("write structural L1 receipt: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync structural L1 receipt: {error}"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use std::{fs, path::PathBuf};

    use super::{
        parse_options, read_bounded_regular_file, same_file_version, MAX_ADAPTER_RECEIPTS,
        MAX_RECEIPT_BYTES_U64,
    };

    fn args(receipt_count: usize) -> Vec<String> {
        let mut values = vec!["--receipt-out".to_owned(), "l1.json".to_owned()];
        values.extend((0..receipt_count).map(|index| format!("adapter-{index}.json")));
        values
    }

    fn scratch(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "zenodex-zrpf-prove-l1-{}-{name}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir(&path).expect("create isolated scratch directory");
        path
    }

    #[test]
    fn exact_cli_accepts_one_and_eight_adapter_receipts() -> Result<(), String> {
        let one = parse_options(args(1))?;
        assert_eq!(one.receipt_out.to_string_lossy(), "l1.json");
        assert_eq!(one.adapter_receipt_paths.len(), 1);

        let eight = parse_options(args(MAX_ADAPTER_RECEIPTS))?;
        assert_eq!(eight.adapter_receipt_paths.len(), MAX_ADAPTER_RECEIPTS);
        Ok(())
    }

    #[test]
    fn cli_rejects_zero_or_nine_adapter_receipts() {
        assert!(parse_options(args(0)).is_err());
        assert!(parse_options(args(MAX_ADAPTER_RECEIPTS + 1)).is_err());
    }

    #[test]
    fn cli_rejects_unknown_or_misordered_options() {
        assert!(parse_options([
            "--unknown".to_owned(),
            "l1.json".to_owned(),
            "adapter.json".to_owned(),
        ])
        .is_err());
        assert!(parse_options([
            "adapter.json".to_owned(),
            "--receipt-out".to_owned(),
            "l1.json".to_owned(),
        ])
        .is_err());
        assert!(parse_options([
            "--receipt-out".to_owned(),
            "l1.json".to_owned(),
            "--unknown".to_owned(),
        ])
        .is_err());
    }

    #[test]
    fn cli_rejects_empty_output_or_adapter_paths() {
        assert!(parse_options([
            "--receipt-out".to_owned(),
            String::new(),
            "adapter.json".to_owned(),
        ])
        .is_err());
        assert!(parse_options([
            "--receipt-out".to_owned(),
            "l1.json".to_owned(),
            String::new(),
        ])
        .is_err());
    }

    #[test]
    fn bounded_receipt_reader_rejects_empty_oversize_and_symlink_inputs() {
        let directory = scratch("bounded-reader");
        let empty = directory.join("empty.json");
        fs::write(&empty, []).expect("write empty input");
        assert!(read_bounded_regular_file(&empty).is_err());

        let oversized = directory.join("oversized.json");
        let file = fs::File::create(&oversized).expect("create sparse oversized input");
        file.set_len(MAX_RECEIPT_BYTES_U64 + 1)
            .expect("set oversized length");
        assert!(read_bounded_regular_file(&oversized).is_err());

        #[cfg(unix)]
        {
            let target = directory.join("target.json");
            fs::write(&target, b"{}").expect("write symlink target");
            let link = directory.join("link.json");
            std::os::unix::fs::symlink(&target, &link).expect("create symlink input");
            assert!(read_bounded_regular_file(&link).is_err());
        }
        fs::remove_dir_all(directory).expect("remove isolated scratch directory");
    }

    #[test]
    fn file_version_comparison_detects_in_place_mutation() {
        let directory = scratch("file-version");
        let path = directory.join("receipt.json");
        fs::write(&path, b"{}").expect("write initial input");
        let before = fs::metadata(&path).expect("initial metadata");
        let stable = fs::metadata(&path).expect("stable metadata");
        assert!(same_file_version(&before, &stable));

        fs::write(&path, b"{\"changed\":true}").expect("mutate input");
        let after = fs::metadata(&path).expect("mutated metadata");
        assert!(!same_file_version(&before, &after));
        fs::remove_dir_all(directory).expect("remove isolated scratch directory");
    }
}
