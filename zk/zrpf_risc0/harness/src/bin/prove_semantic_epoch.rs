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
use zenodex_zrpf_protocol_v3::{
    SemanticEpochDependencyProgramsInputV1, SemanticEpochDependencyProgramsV1,
};
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ELF, ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID,
    ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF, ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
    ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ELF, ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
    ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF, ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
};
use zenodex_zrpf_risc0_semantic_shared::{
    bind_semantic_guest_input_after_level_one_verification_v1,
    compose_semantic_epoch_after_level_one_verification_v1, encode_semantic_guest_input_v1,
    SemanticEpochCompositionPolicyV1, SemanticEpochCompositionProjectionV1, SemanticGuestInputV1,
    SemanticGuestLeafDisclosureV1, SemanticGuestLevelOneDisclosureV1,
};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_verifier::{VerifiedNodeReceiptV3, VerifiedSemanticEpochReceiptV1};

const MAX_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_RECEIPT_BYTES_U64: u64 = 16 * 1_024 * 1_024;
const MAX_RECEIPT_READ_BYTES_U64: u64 = MAX_RECEIPT_BYTES_U64 + 1;
const MAX_LEVEL_ONE_GROUPS: usize = 8;
const MAX_LEAVES_PER_GROUP: usize = 8;
const MAX_TOTAL_LEAVES: usize = 64;

struct Options {
    receipt_out: PathBuf,
    groups: Vec<GroupOptions>,
}

struct GroupOptions {
    level_one_receipt_path: PathBuf,
    leaves: Vec<LeafOptions>,
}

struct LeafOptions {
    adapter_receipt_path: PathBuf,
    semantic_opening: [u8; 32],
}

struct VerifiedGroup {
    level_one: VerifiedNodeReceiptV3,
    leaves: Vec<VerifiedLeaf>,
}

struct VerifiedLeaf {
    adapter: VerifiedNodeReceiptV3,
    semantic_opening: [u8; 32],
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let options = parse_options(process_args()?)?;
    validate_methods()?;

    // Receipt journals are interpreted only through sealed verified types.
    let groups = load_verified_groups(&options.groups)?;
    let raw_input = semantic_guest_input(&groups)?;
    let policy = semantic_policy()?;
    let semantic_input = bind_semantic_guest_input_after_level_one_verification_v1(&raw_input)
        .map_err(|error| format!("host semantic disclosure binding rejected: {error}"))?;
    let expected = compose_semantic_epoch_after_level_one_verification_v1(&semantic_input, policy)
        .map_err(|error| format!("host semantic composition rejected: {error}"))?;
    let dependencies = governed_dependency_programs()?;
    let verified = prove_semantic_epoch(&raw_input, &groups, &expected, &dependencies)?;
    let receipt_bytes = canonical_receipt_bytes(verified.receipt())?;
    persist_receipt(&options.receipt_out, &receipt_bytes)?;
    print_report(&verified, groups.len(), &receipt_bytes)
}

fn process_args() -> Result<Vec<String>, String> {
    env::args_os()
        .skip(1)
        .map(|value| value.into_string().map_err(|_| usage().to_owned()))
        .collect()
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args: Vec<String> = args.into_iter().collect();
    if args.len() < 7 || args.first().is_none_or(|value| value != "--receipt-out") {
        return Err(usage().to_owned());
    }
    let receipt_out = args
        .get(1)
        .filter(|value| valid_path_token(value))
        .ok_or_else(|| usage().to_owned())?;
    let mut cursor = 2usize;
    let mut groups = Vec::new();
    let mut total_leaves = 0usize;
    while cursor < args.len() {
        if groups.len() == MAX_LEVEL_ONE_GROUPS
            || args.get(cursor).map(String::as_str) != Some("--l1")
        {
            return Err(usage().to_owned());
        }
        let level_one_path = args
            .get(cursor + 1)
            .filter(|value| valid_path_token(value))
            .ok_or_else(|| usage().to_owned())?;
        cursor = cursor.checked_add(2).ok_or_else(|| usage().to_owned())?;
        let (leaves, next_cursor) = parse_group_leaves(&args, cursor)?;
        cursor = next_cursor;
        total_leaves = total_leaves
            .checked_add(leaves.len())
            .ok_or_else(|| usage().to_owned())?;
        if total_leaves > MAX_TOTAL_LEAVES {
            return Err(usage().to_owned());
        }
        groups.push(GroupOptions {
            level_one_receipt_path: PathBuf::from(level_one_path),
            leaves,
        });
    }
    if groups.is_empty() {
        return Err(usage().to_owned());
    }
    Ok(Options {
        receipt_out: PathBuf::from(receipt_out),
        groups,
    })
}

fn parse_group_leaves(
    args: &[String],
    mut cursor: usize,
) -> Result<(Vec<LeafOptions>, usize), String> {
    let mut leaves = Vec::new();
    while args.get(cursor).map(String::as_str) == Some("--leaf") {
        if leaves.len() == MAX_LEAVES_PER_GROUP {
            return Err(usage().to_owned());
        }
        let path = args
            .get(cursor + 1)
            .filter(|value| valid_path_token(value))
            .ok_or_else(|| usage().to_owned())?;
        let opening = args.get(cursor + 2).ok_or_else(|| usage().to_owned())?;
        leaves.push(LeafOptions {
            adapter_receipt_path: PathBuf::from(path),
            semantic_opening: parse_opening_hex(opening)?,
        });
        cursor = cursor.checked_add(3).ok_or_else(|| usage().to_owned())?;
    }
    if leaves.is_empty() {
        return Err(usage().to_owned());
    }
    Ok((leaves, cursor))
}

fn valid_path_token(value: &str) -> bool {
    !value.is_empty() && !value.starts_with("--")
}

fn parse_opening_hex(value: &str) -> Result<[u8; 32], String> {
    if value.len() != 64 {
        return Err(usage().to_owned());
    }
    let bytes = hex::decode(value).map_err(|_| usage().to_owned())?;
    let opening: [u8; 32] = bytes.try_into().map_err(|_| usage().to_owned())?;
    if opening.iter().all(|byte| *byte == 0) {
        return Err(usage().to_owned());
    }
    Ok(opening)
}

fn usage() -> &'static str {
    "usage: prove_semantic_epoch --receipt-out <semantic.receipt.json> --l1 <l1.receipt.json> --leaf <adapter.receipt.json> <opening-hex> [--leaf <adapter.receipt.json> <opening-hex> ...] [--l1 <l1.receipt.json> --leaf <adapter.receipt.json> <opening-hex> ...]"
}

fn validate_methods() -> Result<(), String> {
    for (name, elf, image_id) in [
        (
            "adapter A",
            ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF,
            ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
        ),
        (
            "structural L1 B",
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ELF,
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
        ),
        (
            "structural L2 C",
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ELF,
            ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
        ),
        (
            "semantic epoch D",
            ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ELF,
            ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID,
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

fn load_verified_groups(options: &[GroupOptions]) -> Result<Vec<VerifiedGroup>, String> {
    options
        .iter()
        .enumerate()
        .map(|(group_index, group)| load_verified_group(group, group_index))
        .collect()
}

fn load_verified_group(group: &GroupOptions, group_index: usize) -> Result<VerifiedGroup, String> {
    let level_one = load_verified_node(
        &group.level_one_receipt_path,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
    )
    .map_err(|error| format!("level-one receipt {group_index}: {error}"))?;
    let leaves = group
        .leaves
        .iter()
        .enumerate()
        .map(|(leaf_index, leaf)| {
            let adapter = load_verified_node(
                &leaf.adapter_receipt_path,
                ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
            )
            .map_err(|error| format!("adapter receipt {group_index}:{leaf_index}: {error}"))?;
            Ok(VerifiedLeaf {
                adapter,
                semantic_opening: leaf.semantic_opening,
            })
        })
        .collect::<Result<Vec<_>, String>>()?;
    Ok(VerifiedGroup { level_one, leaves })
}

fn load_verified_node(
    path: &Path,
    expected_image_id: [u32; 8],
) -> Result<VerifiedNodeReceiptV3, String> {
    let receipt_bytes = read_bounded_regular_file(path)?;
    VerifiedNodeReceiptV3::verify_canonical_succinct_bytes(&receipt_bytes, expected_image_id)
        .map_err(|error| format!("sealed node verification: {error}"))
}

fn semantic_guest_input(groups: &[VerifiedGroup]) -> Result<SemanticGuestInputV1, String> {
    let disclosures = groups
        .iter()
        .enumerate()
        .map(|(group_index, group)| {
            let leaves = group
                .leaves
                .iter()
                .enumerate()
                .map(|(leaf_index, leaf)| {
                    SemanticGuestLeafDisclosureV1::new(
                        leaf.adapter.receipt().journal.bytes.clone(),
                        leaf.semantic_opening,
                    )
                    .map_err(|error| {
                        format!("semantic leaf disclosure {group_index}:{leaf_index}: {error}")
                    })
                })
                .collect::<Result<Vec<_>, _>>()?;
            SemanticGuestLevelOneDisclosureV1::new(
                group.level_one.receipt().journal.bytes.clone(),
                leaves,
            )
            .map_err(|error| format!("semantic level-one disclosure {group_index}: {error}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    SemanticGuestInputV1::new(ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID, disclosures)
        .map_err(|error| format!("semantic guest input rejected: {error}"))
}

fn semantic_policy() -> Result<SemanticEpochCompositionPolicyV1, String> {
    SemanticEpochCompositionPolicyV1::new(
        ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID,
        ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID,
    )
    .map_err(|error| format!("semantic epoch policy rejected: {error}"))
}

fn governed_dependency_programs() -> Result<SemanticEpochDependencyProgramsV1, String> {
    let adapter_program_id = program_id_from_risc0_words_v3(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID)
        .map_err(|error| format!("adapter dependency program ID: {error}"))?;
    let level_one_program_id =
        program_id_from_risc0_words_v3(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID)
            .map_err(|error| format!("level-one dependency program ID: {error}"))?;
    let level_two_program_id =
        program_id_from_risc0_words_v3(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID)
            .map_err(|error| format!("level-two dependency program ID: {error}"))?;
    Ok(SemanticEpochDependencyProgramsV1::new(
        SemanticEpochDependencyProgramsInputV1 {
            adapter_program_id,
            level_one_program_id,
            level_two_program_id,
        },
    ))
}

fn prove_semantic_epoch(
    raw_input: &SemanticGuestInputV1,
    groups: &[VerifiedGroup],
    expected: &SemanticEpochCompositionProjectionV1,
    dependencies: &SemanticEpochDependencyProgramsV1,
) -> Result<VerifiedSemanticEpochReceiptV1, String> {
    let input_bytes = encode_semantic_guest_input_v1(raw_input)
        .map_err(|error| format!("semantic guest input encode: {error}"))?;
    let input_length =
        u32::try_from(input_bytes.len()).map_err(|_| "semantic input length exceeds u32")?;
    let mut builder = ExecutorEnv::builder();
    builder
        .write_slice(&[input_length])
        .write_slice(&input_bytes);
    for group in groups {
        builder.add_assumption(group.level_one.receipt().clone());
    }
    let executor_env = builder
        .build()
        .map_err(|error| format!("semantic executor environment: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("semantic epoch proving failed: {error}"))?
        .receipt;
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err("semantic epoch prover returned a non-Succinct receipt".to_owned());
    }
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    VerifiedSemanticEpochReceiptV1::verify_exact_succinct_bytes(
        &receipt_bytes,
        ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID,
        dependencies,
        expected.proposal(),
    )
    .map_err(|error| format!("semantic epoch receipt verification failed: {error}"))
}

fn print_report(
    verified: &VerifiedSemanticEpochReceiptV1,
    group_count: usize,
    receipt_bytes: &[u8],
) -> Result<(), String> {
    let proposal = verified.proposal();
    let proposal_hash = proposal
        .proposal_hash()
        .map_err(|error| format!("semantic proposal hash: {error}"))?;
    let report = json!({
        "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
        "leaf_count": proposal.leaf_count(),
        "level_one_group_count": group_count,
        "level_one_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID).to_string(),
        "level_two_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID).to_string(),
        "nonclaims": [
            "this receipt does not prove complete ZenoDEX economic or value-flow semantics",
            "this receipt does not prove data availability or durable atomic ledger admission",
            "proof generation and local verification do not grant settlement, release, privacy, or production authority"
        ],
        "ok": true,
        "operation_count": proposal.operation_count(),
        "program_manifest_root": hex::encode(proposal.program_manifest_root().as_bytes()),
        "proof_tree_root": hex::encode(proposal.proof_tree_root().as_bytes()),
        "proposal_hash": hex::encode(proposal_hash.as_bytes()),
        "receipt_bytes": receipt_bytes.len(),
        "receipt_sha256": sha256_hex(receipt_bytes),
        "receipt_written": true,
        "semantic_epoch_image_id": Digest::from(ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID).to_string(),
        "semantic_epoch_root": hex::encode(proposal.semantic_epoch_root().as_bytes()),
        "status": "bounded_v1_adapter_semantic_epoch_succinct_receipt_verified",
        "structural_level_two_journal_hash": hex::encode(proposal.proof_tree_root().as_bytes()),
    });
    writeln!(std::io::stdout().lock(), "{report}")
        .map_err(|error| format!("write semantic epoch report: {error}"))
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
        .map_err(|error| format!("create semantic epoch receipt: {error}"))?;
    output
        .write_all(bytes)
        .map_err(|error| format!("write semantic epoch receipt: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync semantic epoch receipt: {error}"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

#[cfg(test)]
mod tests {
    use std::{fs, path::PathBuf};

    use super::{
        parse_opening_hex, parse_options, persist_receipt, read_bounded_regular_file,
        same_file_version, MAX_LEAVES_PER_GROUP, MAX_LEVEL_ONE_GROUPS, MAX_RECEIPT_BYTES_U64,
    };

    fn opening_hex(byte: u8) -> String {
        hex::encode([byte; 32])
    }

    fn args(group_count: usize, leaves_per_group: usize) -> Vec<String> {
        let mut values = vec!["--receipt-out".to_owned(), "semantic.json".to_owned()];
        for group in 0..group_count {
            values.push("--l1".to_owned());
            values.push(format!("l1-{group}.json"));
            for leaf in 0..leaves_per_group {
                values.push("--leaf".to_owned());
                values.push(format!("adapter-{group}-{leaf}.json"));
                values.push(opening_hex(1));
            }
        }
        values
    }

    fn scratch(name: &str) -> PathBuf {
        let path = std::env::temp_dir().join(format!(
            "zenodex-zrpf-prove-semantic-{}-{name}",
            std::process::id()
        ));
        let _ = fs::remove_dir_all(&path);
        fs::create_dir(&path).expect("create isolated scratch directory");
        path
    }

    #[test]
    fn exact_cli_accepts_one_leaf_and_bounded_eight_by_eight() -> Result<(), String> {
        let one = parse_options(args(1, 1))?;
        assert_eq!(one.groups.len(), 1);
        assert_eq!(one.groups[0].leaves.len(), 1);

        let maximum = parse_options(args(MAX_LEVEL_ONE_GROUPS, MAX_LEAVES_PER_GROUP))?;
        assert_eq!(maximum.groups.len(), MAX_LEVEL_ONE_GROUPS);
        assert!(maximum
            .groups
            .iter()
            .all(|group| group.leaves.len() == MAX_LEAVES_PER_GROUP));
        Ok(())
    }

    #[test]
    fn cli_rejects_missing_or_misordered_group_tokens() {
        assert!(parse_options(Vec::<String>::new()).is_err());
        assert!(parse_options([
            "--receipt-out".to_owned(),
            "semantic.json".to_owned(),
            "--leaf".to_owned(),
            "adapter.json".to_owned(),
            opening_hex(1),
        ])
        .is_err());

        let mut trailing = args(1, 1);
        trailing.push("trailing-token".to_owned());
        assert!(parse_options(trailing).is_err());
        assert!(parse_options([
            "--receipt-out".to_owned(),
            "semantic.json".to_owned(),
            "--l1".to_owned(),
            "l1.json".to_owned(),
        ])
        .is_err());
        assert!(parse_options([
            "--receipt-out".to_owned(),
            "semantic.json".to_owned(),
            "--l1".to_owned(),
            "l1.json".to_owned(),
            "--unknown".to_owned(),
        ])
        .is_err());
    }

    #[test]
    fn cli_rejects_counts_above_eight() {
        assert!(parse_options(args(MAX_LEVEL_ONE_GROUPS + 1, 1)).is_err());
        assert!(parse_options(args(1, MAX_LEAVES_PER_GROUP + 1)).is_err());
    }

    #[test]
    fn cli_rejects_empty_paths_and_malformed_openings() {
        let mut empty_output = args(1, 1);
        empty_output[1].clear();
        assert!(parse_options(empty_output).is_err());

        let mut empty_leaf = args(1, 1);
        empty_leaf[5].clear();
        assert!(parse_options(empty_leaf).is_err());

        assert!(parse_opening_hex("00").is_err());
        assert!(parse_opening_hex(&opening_hex(0)).is_err());
        assert!(parse_opening_hex(&"zz".repeat(32)).is_err());
        assert_eq!(parse_opening_hex(&opening_hex(7)), Ok([7; 32]));
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

    #[test]
    fn receipt_persistence_never_overwrites_an_existing_artifact() {
        let directory = scratch("exclusive-output");
        let path = directory.join("semantic.receipt.json");
        fs::write(&path, b"existing").expect("write existing output");

        assert!(persist_receipt(&path, b"replacement").is_err());
        assert_eq!(fs::read(&path).expect("read existing output"), b"existing");
        fs::remove_dir_all(directory).expect("remove isolated scratch directory");
    }
}
