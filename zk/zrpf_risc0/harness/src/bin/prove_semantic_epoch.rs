use std::{
    env, fs,
    io::{Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
};

#[cfg(unix)]
use std::os::unix::fs::MetadataExt;
#[cfg(target_os = "linux")]
use std::os::unix::io::AsRawFd;

use risc0_zkvm::{
    compute_image_id, default_prover, Digest, Executor, ExecutorEnv, ExternalProver, InnerReceipt,
    ProverOpts, Receipt,
};
#[cfg(target_os = "linux")]
use rustix::fs::{
    fchmod, fcntl_add_seals, fcntl_get_seals, memfd_create, MemfdFlags, Mode, SealFlags,
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
    SemanticEpochCompositionErrorV1, SemanticEpochCompositionPolicyV1,
    SemanticEpochCompositionProjectionV1, SemanticGuestInputV1, SemanticGuestLeafDisclosureV1,
    SemanticGuestLevelOneDisclosureV1, SemanticRecompositionErrorV1,
};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_verifier::{VerifiedNodeReceiptV3, VerifiedSemanticEpochReceiptV1};

const MAX_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_RECEIPT_BYTES_U64: u64 = 16 * 1_024 * 1_024;
const MAX_RECEIPT_READ_BYTES_U64: u64 = MAX_RECEIPT_BYTES_U64 + 1;
const MAX_LEVEL_ONE_GROUPS: usize = 8;
const MAX_LEAVES_PER_GROUP: usize = 8;
const MAX_TOTAL_LEAVES: usize = 64;
const MAX_NEGATIVE_REPORT_BYTES: usize = 4_096;
const NEGATIVE_DUPLICATE_SOURCE_COMMAND: &str = "negative-duplicate-source";
const EXPECTED_DUPLICATE_SOURCE_GUEST_REJECT: &str =
    "Guest panicked: ZRPF semantic epoch duplicate semantic source rejected";
const GOVERNED_R0VM_SHA256: &str =
    "36c016a5bb2ded5bd1f8f92cc487e6ffaeb1e95ec05850c983081a0f716b515b";
const GOVERNED_R0VM_SIZE_BYTES: u64 = 108_998_816;
const NEGATIVE_EXECUTOR_ENVIRONMENT_KEYS: [&str; 2] = ["RISC0_SERVER_PATH", "TMPDIR"];

struct Options {
    receipt_out: PathBuf,
    groups: Vec<GroupOptions>,
}

struct NegativeDuplicateSourceOptions {
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

struct GovernedR0vm {
    file: fs::File,
    initial_metadata: fs::Metadata,
    executable_path: PathBuf,
}

impl GovernedR0vm {
    #[cfg(target_os = "linux")]
    fn from_environment() -> Result<Self, String> {
        let (mut source, source_metadata) = open_governed_r0vm_source()?;
        let file = copy_to_sealed_r0vm_memfd(&mut source, &source_metadata)?;
        let initial_metadata = file
            .metadata()
            .map_err(|error| format!("governed r0vm memfd metadata: {error}"))?;
        let executable_path = opened_descriptor_executable_path(&file)?;
        let mut governed = Self {
            file,
            initial_metadata,
            executable_path,
        };
        governed.verify_opened_file()?;
        Ok(governed)
    }

    #[cfg(not(target_os = "linux"))]
    fn from_environment() -> Result<Self, String> {
        Err("governed r0vm memfd execution requires Linux".to_owned())
    }

    fn verify_opened_file(&mut self) -> Result<(), String> {
        #[cfg(target_os = "linux")]
        {
            let required_seals = required_r0vm_seals();
            let actual_seals = fcntl_get_seals(&self.file)
                .map_err(|error| format!("read governed r0vm execution seals: {error}"))?;
            if !actual_seals.contains(required_seals) {
                return Err("governed r0vm execution memfd lost a required seal".to_owned());
            }
        }
        verify_exact_r0vm_bytes(&mut self.file, &self.initial_metadata)
    }
}

#[cfg(target_os = "linux")]
fn open_governed_r0vm_source() -> Result<(fs::File, fs::Metadata), String> {
    let path = env::var_os("RISC0_SERVER_PATH")
        .map(PathBuf::from)
        .filter(|value| value.is_absolute())
        .ok_or_else(|| "RISC0_SERVER_PATH must name the governed absolute r0vm path".to_owned())?;
    let path_metadata =
        fs::symlink_metadata(&path).map_err(|error| format!("governed r0vm metadata: {error}"))?;
    if !path_metadata.is_file()
        || path_metadata.file_type().is_symlink()
        || path_metadata.len() != GOVERNED_R0VM_SIZE_BYTES
        || path_metadata.mode() & 0o111 == 0
    {
        return Err("governed r0vm must be the exact executable regular file".to_owned());
    }
    let mut file = fs::File::open(&path).map_err(|error| format!("open governed r0vm: {error}"))?;
    let metadata = file
        .metadata()
        .map_err(|error| format!("opened governed r0vm metadata: {error}"))?;
    if !same_file_version(&path_metadata, &metadata) {
        return Err("governed r0vm path changed while it was opened".to_owned());
    }
    verify_exact_r0vm_bytes(&mut file, &metadata)?;
    Ok((file, metadata))
}

#[cfg(target_os = "linux")]
fn copy_to_sealed_r0vm_memfd(
    source: &mut fs::File,
    source_metadata: &fs::Metadata,
) -> Result<fs::File, String> {
    source
        .seek(SeekFrom::Start(0))
        .map_err(|error| format!("rewind governed r0vm source: {error}"))?;
    let descriptor = memfd_create(
        "zenodex-zrpf-governed-r0vm",
        MemfdFlags::CLOEXEC | MemfdFlags::ALLOW_SEALING,
    )
    .map_err(|error| format!("create governed r0vm memfd: {error}"))?;
    let mut output = fs::File::from(descriptor);
    copy_exact_r0vm_bytes(source, &mut output)?;
    let source_after = source
        .metadata()
        .map_err(|error| format!("governed r0vm source final metadata: {error}"))?;
    if !same_file_version(source_metadata, &source_after) {
        return Err("governed r0vm source changed while copied".to_owned());
    }
    fchmod(&output, Mode::RUSR | Mode::XUSR)
        .map_err(|error| format!("mark governed r0vm memfd executable: {error}"))?;
    let required_seals = required_r0vm_seals();
    fcntl_add_seals(&output, required_seals)
        .map_err(|error| format!("seal governed r0vm memfd: {error}"))?;
    let actual_seals = fcntl_get_seals(&output)
        .map_err(|error| format!("read governed r0vm memfd seals: {error}"))?;
    if !actual_seals.contains(required_seals) {
        return Err("governed r0vm memfd is incompletely sealed".to_owned());
    }
    Ok(output)
}

#[cfg(target_os = "linux")]
fn copy_exact_r0vm_bytes(source: &mut fs::File, output: &mut fs::File) -> Result<(), String> {
    let mut copied = 0u64;
    let mut buffer = [0u8; 1024 * 1024];
    loop {
        let read = source
            .read(&mut buffer)
            .map_err(|error| format!("read governed r0vm source: {error}"))?;
        if read == 0 {
            break;
        }
        copied = copied
            .checked_add(u64::try_from(read).map_err(|_| "r0vm copy length exceeds u64")?)
            .ok_or_else(|| "r0vm copy byte count overflow".to_owned())?;
        if copied > GOVERNED_R0VM_SIZE_BYTES {
            return Err("governed r0vm source grew while copied".to_owned());
        }
        output
            .write_all(&buffer[..read])
            .map_err(|error| format!("write governed r0vm memfd: {error}"))?;
    }
    if copied != GOVERNED_R0VM_SIZE_BYTES {
        return Err("governed r0vm source truncated while copied".to_owned());
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn required_r0vm_seals() -> SealFlags {
    SealFlags::WRITE | SealFlags::GROW | SealFlags::SHRINK | SealFlags::SEAL
}

fn verify_exact_r0vm_bytes(
    file: &mut fs::File,
    initial_metadata: &fs::Metadata,
) -> Result<(), String> {
    let before = file
        .metadata()
        .map_err(|error| format!("governed r0vm pre-hash metadata: {error}"))?;
    if !same_file_version(initial_metadata, &before) {
        return Err("governed r0vm changed before hashing".to_owned());
    }
    file.seek(SeekFrom::Start(0))
        .map_err(|error| format!("rewind governed r0vm: {error}"))?;
    let mut hasher = Sha256::new();
    let mut total = 0u64;
    let mut buffer = [0u8; 1024 * 1024];
    loop {
        let read = file
            .read(&mut buffer)
            .map_err(|error| format!("hash governed r0vm: {error}"))?;
        if read == 0 {
            break;
        }
        total = total
            .checked_add(u64::try_from(read).map_err(|_| "r0vm read length exceeds u64")?)
            .ok_or_else(|| "r0vm byte count overflow".to_owned())?;
        if total > GOVERNED_R0VM_SIZE_BYTES {
            return Err("governed r0vm grew while it was hashed".to_owned());
        }
        hasher.update(&buffer[..read]);
    }
    let after = file
        .metadata()
        .map_err(|error| format!("governed r0vm post-hash metadata: {error}"))?;
    if total != GOVERNED_R0VM_SIZE_BYTES
        || !same_file_version(initial_metadata, &after)
        || hex::encode(hasher.finalize()) != GOVERNED_R0VM_SHA256
    {
        return Err("governed r0vm identity mismatch".to_owned());
    }
    Ok(())
}

#[cfg(target_os = "linux")]
fn opened_descriptor_executable_path(file: &fs::File) -> Result<PathBuf, String> {
    Ok(PathBuf::from(format!(
        "/proc/{}/fd/{}",
        std::process::id(),
        file.as_raw_fd()
    )))
}

#[cfg(not(target_os = "linux"))]
fn opened_descriptor_executable_path(_file: &fs::File) -> Result<PathBuf, String> {
    Err("governed descriptor execution requires Linux procfs".to_owned())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let args = process_args()?;
    if args.first().map(String::as_str) == Some(NEGATIVE_DUPLICATE_SOURCE_COMMAND) {
        let options = parse_negative_duplicate_source_options(args)?;
        return run_negative_duplicate_source(options);
    }
    let options = parse_options(args)?;
    run_positive(options)
}

fn run_positive(options: Options) -> Result<(), String> {
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

fn run_negative_duplicate_source(options: NegativeDuplicateSourceOptions) -> Result<(), String> {
    validate_methods()?;
    validate_negative_executor_environment()?;
    let mut governed_r0vm = GovernedR0vm::from_environment()?;

    // All persisted journals cross the sealed receipt verifier before any
    // disclosure bytes or semantic openings are used as commitments.
    let groups = load_verified_groups(&options.groups)?;
    if groups.len() < 2 {
        return Err("duplicate-source execution requires at least two level-one groups".to_owned());
    }
    let raw_input = semantic_guest_input(&groups)?;
    let semantic_input = bind_semantic_guest_input_after_level_one_verification_v1(&raw_input)
        .map_err(|error| format!("host duplicate-source disclosure binding rejected: {error}"))?;
    require_exact_duplicate_source_host_reject(
        compose_semantic_epoch_after_level_one_verification_v1(&semantic_input, semantic_policy()?),
    )?;
    execute_exact_duplicate_source_guest_reject(&raw_input, &groups, &mut governed_r0vm)?;
    print_negative_duplicate_source_report(&raw_input, &groups)
}

fn validate_negative_executor_environment() -> Result<(), String> {
    let mut keys = env::vars_os()
        .map(|(key, _)| {
            key.into_string()
                .map_err(|_| "negative executor environment key is not UTF-8".to_owned())
        })
        .collect::<Result<Vec<_>, _>>()?;
    keys.sort_unstable();
    if keys != NEGATIVE_EXECUTOR_ENVIRONMENT_KEYS {
        return Err(
            "negative executor requires the exact governed environment allowlist".to_owned(),
        );
    }
    let temporary_path = env::var_os("TMPDIR")
        .map(PathBuf::from)
        .filter(|value| value.is_absolute())
        .ok_or_else(|| "TMPDIR must name an absolute private directory".to_owned())?;
    let metadata = fs::symlink_metadata(&temporary_path)
        .map_err(|error| format!("negative executor TMPDIR metadata: {error}"))?;
    if !metadata.is_dir() || metadata.file_type().is_symlink() {
        return Err("negative executor TMPDIR must be a non-symlink directory".to_owned());
    }
    #[cfg(unix)]
    if metadata.mode() & 0o077 != 0 {
        return Err("negative executor TMPDIR must not grant group or other access".to_owned());
    }
    let canonical = fs::canonicalize(&temporary_path)
        .map_err(|error| format!("canonicalize negative executor TMPDIR: {error}"))?;
    if canonical != temporary_path {
        return Err("negative executor TMPDIR must already be canonical".to_owned());
    }
    Ok(())
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

fn parse_negative_duplicate_source_options(
    args: impl IntoIterator<Item = String>,
) -> Result<NegativeDuplicateSourceOptions, String> {
    let args: Vec<String> = args.into_iter().collect();
    if args.first().map(String::as_str) != Some(NEGATIVE_DUPLICATE_SOURCE_COMMAND) {
        return Err(negative_duplicate_source_usage().to_owned());
    }
    let mut cursor = 1usize;
    let mut groups = Vec::new();
    let mut total_leaves = 0usize;
    while cursor < args.len() {
        if groups.len() == MAX_LEVEL_ONE_GROUPS
            || args.get(cursor).map(String::as_str) != Some("--l1")
        {
            return Err(negative_duplicate_source_usage().to_owned());
        }
        let level_one_path = args
            .get(cursor + 1)
            .filter(|value| valid_path_token(value))
            .ok_or_else(|| negative_duplicate_source_usage().to_owned())?;
        cursor = cursor
            .checked_add(2)
            .ok_or_else(|| negative_duplicate_source_usage().to_owned())?;
        let (leaves, next_cursor) = parse_group_leaves(&args, cursor)
            .map_err(|_| negative_duplicate_source_usage().to_owned())?;
        cursor = next_cursor;
        total_leaves = total_leaves
            .checked_add(leaves.len())
            .ok_or_else(|| negative_duplicate_source_usage().to_owned())?;
        if total_leaves > MAX_TOTAL_LEAVES {
            return Err(negative_duplicate_source_usage().to_owned());
        }
        groups.push(GroupOptions {
            level_one_receipt_path: PathBuf::from(level_one_path),
            leaves,
        });
    }
    if groups.len() < 2 {
        return Err(negative_duplicate_source_usage().to_owned());
    }
    Ok(NegativeDuplicateSourceOptions { groups })
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

fn negative_duplicate_source_usage() -> &'static str {
    "usage: prove_semantic_epoch negative-duplicate-source --l1 <l1.receipt.json> --leaf <adapter.receipt.json> <opening-hex> [--leaf <adapter.receipt.json> <opening-hex> ...] --l1 <l1.receipt.json> --leaf <adapter.receipt.json> <opening-hex> [--leaf <adapter.receipt.json> <opening-hex> ...] [--l1 <l1.receipt.json> --leaf <adapter.receipt.json> <opening-hex> ...]"
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

fn require_exact_duplicate_source_host_reject(
    result: Result<SemanticEpochCompositionProjectionV1, SemanticEpochCompositionErrorV1>,
) -> Result<(), String> {
    match result {
        Err(SemanticEpochCompositionErrorV1::SemanticRecomposition(
            SemanticRecompositionErrorV1::DuplicateSemanticSource,
        )) => Ok(()),
        Ok(_) => Err("host semantic mirror accepted the duplicate semantic source".to_owned()),
        Err(error) => Err(format!(
            "host semantic mirror rejected at the wrong boundary: {error}"
        )),
    }
}

fn execute_exact_duplicate_source_guest_reject(
    raw_input: &SemanticGuestInputV1,
    groups: &[VerifiedGroup],
    governed_r0vm: &mut GovernedR0vm,
) -> Result<(), String> {
    let input_bytes = encode_semantic_guest_input_v1(raw_input)
        .map_err(|error| format!("duplicate-source semantic input encode: {error}"))?;
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
        .map_err(|error| format!("duplicate-source executor environment: {error}"))?;
    governed_r0vm.verify_opened_file()?;
    let execution = ExternalProver::new("governed-ipc-sealed", &governed_r0vm.executable_path)
        .execute(executor_env, ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ELF);
    governed_r0vm.verify_opened_file()?;
    match execution {
        Ok(_) => Err("semantic epoch guest accepted the duplicate semantic source".to_owned()),
        Err(error)
            if error
                .chain()
                .any(|cause| cause.to_string() == EXPECTED_DUPLICATE_SOURCE_GUEST_REJECT) =>
        {
            Ok(())
        }
        Err(error) => Err(format!(
            "semantic epoch guest rejected at the wrong boundary: {error:#}"
        )),
    }
}

fn negative_duplicate_source_report_bytes(
    raw_input: &SemanticGuestInputV1,
    group_count: usize,
    leaf_count: usize,
) -> Result<Vec<u8>, String> {
    if !(2..=MAX_LEVEL_ONE_GROUPS).contains(&group_count)
        || leaf_count < group_count
        || leaf_count > MAX_TOTAL_LEAVES
    {
        return Err("negative duplicate-source report counts are outside bounds".to_owned());
    }
    let semantic_input_bytes = encode_semantic_guest_input_v1(raw_input)
        .map_err(|error| format!("negative report semantic input encode: {error}"))?;
    let report = json!({
        "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
        "adapter_receipts_sealed_verified": leaf_count,
        "authoritative_negative_evidence": false,
        "candidate_accepted": false,
        "cryptographic_reject_receipt_exists": false,
        "dynamic_loader_closure_verified": false,
        "executor_binary_sealed_memfd": true,
        "guest_execution_attempted": true,
        "guest_execution_failed": true,
        "guest_execution_rejected": true,
        "guest_reject_boundary": "semantic_epoch_composition",
        "guest_reject_code": "duplicate_semantic_source",
        "host_mirror_reject": "duplicate_semantic_source",
        "level_one_assumptions_supplied": group_count,
        "level_one_group_count": group_count,
        "level_one_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID).to_string(),
        "level_one_receipts_sealed_verified": group_count,
        "level_two_image_id": Digest::from(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID).to_string(),
        "executor_backend": "governed_ipc_r0vm_sealed_memfd",
        "executor_binary_sha256": GOVERNED_R0VM_SHA256,
        "executor_environment_allowlist": NEGATIVE_EXECUTOR_ENVIRONMENT_KEYS,
        "executor_environment_exact": true,
        "methods_validated": true,
        "nonclaims": [
            "guest execution failure is not a cryptographic reject receipt",
            "the dynamic loader and shared-library closure are not verified by this report",
            "this negative control grants no semantic, settlement, release, privacy, or production authority"
        ],
        "ok": true,
        "receipt_written": false,
        "semantic_epoch_image_id": Digest::from(ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID).to_string(),
        "semantic_input_bytes": semantic_input_bytes.len(),
        "semantic_input_sha256": sha256_hex(&semantic_input_bytes),
        "semantic_receipt_created": false,
        "same_uid_source_mutation_resistance": true,
        "status": "bounded_v1_duplicate_semantic_source_guest_execution_rejected",
    });
    let bytes =
        serde_json::to_vec(&report).map_err(|error| format!("negative report encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_NEGATIVE_REPORT_BYTES {
        return Err("negative duplicate-source report exceeds canonical bound".to_owned());
    }
    Ok(bytes)
}

fn print_negative_duplicate_source_report(
    raw_input: &SemanticGuestInputV1,
    groups: &[VerifiedGroup],
) -> Result<(), String> {
    let leaf_count = groups.iter().try_fold(0usize, |count, group| {
        count
            .checked_add(group.leaves.len())
            .ok_or_else(|| "duplicate-source report leaf count overflow".to_owned())
    })?;
    let bytes = negative_duplicate_source_report_bytes(raw_input, groups.len(), leaf_count)?;
    let mut output = std::io::stdout().lock();
    output
        .write_all(&bytes)
        .and_then(|()| output.write_all(b"\n"))
        .map_err(|error| format!("write duplicate-source report: {error}"))
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

    use serde_json::Value;
    use zenodex_zrpf_risc0_semantic_shared::{
        encode_semantic_guest_input_v1, SemanticEpochCompositionErrorV1, SemanticGuestInputV1,
        SemanticGuestLeafDisclosureV1, SemanticGuestLevelOneDisclosureV1,
        SemanticRecompositionErrorV1,
    };

    use super::{
        negative_duplicate_source_report_bytes, parse_negative_duplicate_source_options,
        parse_opening_hex, parse_options, persist_receipt, read_bounded_regular_file,
        require_exact_duplicate_source_host_reject, same_file_version, sha256_hex,
        GOVERNED_R0VM_SHA256, MAX_LEAVES_PER_GROUP, MAX_LEVEL_ONE_GROUPS,
        MAX_NEGATIVE_REPORT_BYTES, MAX_RECEIPT_BYTES_U64, NEGATIVE_DUPLICATE_SOURCE_COMMAND,
    };

    fn opening_hex(byte: u8) -> String {
        hex::encode([byte; 32])
    }

    fn args(group_count: usize, leaves_per_group: usize) -> Vec<String> {
        let mut values = vec!["--receipt-out".to_owned(), "semantic.json".to_owned()];
        append_groups(&mut values, group_count, leaves_per_group);
        values
    }

    fn negative_args(group_count: usize, leaves_per_group: usize) -> Vec<String> {
        let mut values = vec![NEGATIVE_DUPLICATE_SOURCE_COMMAND.to_owned()];
        append_groups(&mut values, group_count, leaves_per_group);
        values
    }

    fn append_groups(values: &mut Vec<String>, group_count: usize, leaves_per_group: usize) {
        for group in 0..group_count {
            values.push("--l1".to_owned());
            values.push(format!("l1-{group}.json"));
            for leaf in 0..leaves_per_group {
                values.push("--leaf".to_owned());
                values.push(format!("adapter-{group}-{leaf}.json"));
                values.push(opening_hex(1));
            }
        }
    }

    fn report_input() -> Result<SemanticGuestInputV1, String> {
        let disclosures = (1..=2u8)
            .map(|value| {
                let leaf = SemanticGuestLeafDisclosureV1::new(vec![value], [value; 32])
                    .map_err(|error| format!("test leaf disclosure: {error}"))?;
                SemanticGuestLevelOneDisclosureV1::new(vec![value], vec![leaf])
                    .map_err(|error| format!("test level-one disclosure: {error}"))
            })
            .collect::<Result<Vec<_>, String>>()?;
        SemanticGuestInputV1::new([1; 8], disclosures)
            .map_err(|error| format!("test report input: {error}"))
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
    fn duplicate_source_cli_requires_two_groups_and_has_no_output_path() -> Result<(), String> {
        let minimum = parse_negative_duplicate_source_options(negative_args(2, 1))?;
        assert_eq!(minimum.groups.len(), 2);
        assert!(minimum.groups.iter().all(|group| group.leaves.len() == 1));

        let maximum = parse_negative_duplicate_source_options(negative_args(
            MAX_LEVEL_ONE_GROUPS,
            MAX_LEAVES_PER_GROUP,
        ))?;
        assert_eq!(maximum.groups.len(), MAX_LEVEL_ONE_GROUPS);
        assert!(maximum
            .groups
            .iter()
            .all(|group| group.leaves.len() == MAX_LEAVES_PER_GROUP));

        assert!(parse_negative_duplicate_source_options(negative_args(1, 1)).is_err());
        assert!(parse_negative_duplicate_source_options([
            NEGATIVE_DUPLICATE_SOURCE_COMMAND.to_owned(),
            "--receipt-out".to_owned(),
            "forbidden.json".to_owned(),
        ])
        .is_err());
        Ok(())
    }

    #[test]
    fn duplicate_source_cli_rejects_unknown_trailing_and_oversized_shapes() {
        assert!(parse_negative_duplicate_source_options(Vec::<String>::new()).is_err());
        assert!(parse_negative_duplicate_source_options(args(2, 1)).is_err());

        let mut trailing = negative_args(2, 1);
        trailing.push("trailing-token".to_owned());
        assert!(parse_negative_duplicate_source_options(trailing).is_err());
        assert!(parse_negative_duplicate_source_options(negative_args(
            MAX_LEVEL_ONE_GROUPS + 1,
            1,
        ))
        .is_err());
        assert!(parse_negative_duplicate_source_options(negative_args(
            2,
            MAX_LEAVES_PER_GROUP + 1,
        ))
        .is_err());
    }

    #[test]
    fn duplicate_source_host_reject_must_match_exact_typed_error() {
        let exact = Err(SemanticEpochCompositionErrorV1::SemanticRecomposition(
            SemanticRecompositionErrorV1::DuplicateSemanticSource,
        ));
        assert!(require_exact_duplicate_source_host_reject(exact).is_ok());

        let wrong = Err(SemanticEpochCompositionErrorV1::SemanticRecomposition(
            SemanticRecompositionErrorV1::DuplicateSourceClaim,
        ));
        assert!(require_exact_duplicate_source_host_reject(wrong)
            .expect_err("wrong typed error must reject")
            .contains("wrong boundary"));
    }

    #[test]
    fn duplicate_source_report_is_bounded_canonical_and_records_no_receipt() -> Result<(), String> {
        let raw_input = report_input()?;
        let input_bytes = encode_semantic_guest_input_v1(&raw_input)
            .map_err(|error| format!("encode test report input: {error}"))?;
        let bytes = negative_duplicate_source_report_bytes(&raw_input, 2, 2)?;
        assert!(bytes.len() <= MAX_NEGATIVE_REPORT_BYTES);
        let report: Value = serde_json::from_slice(&bytes)
            .map_err(|error| format!("decode duplicate-source report: {error}"))?;
        let canonical = serde_json::to_vec(&report)
            .map_err(|error| format!("re-encode duplicate-source report: {error}"))?;
        assert_eq!(bytes, canonical);
        assert_eq!(report["ok"], true);
        assert_eq!(report["candidate_accepted"], false);
        assert_eq!(report["guest_execution_attempted"], true);
        assert_eq!(report["guest_execution_failed"], true);
        assert_eq!(report["guest_execution_rejected"], true);
        assert_eq!(report["guest_reject_code"], "duplicate_semantic_source");
        assert_eq!(report["host_mirror_reject"], "duplicate_semantic_source");
        assert_eq!(report["level_one_assumptions_supplied"], 2);
        assert_eq!(report["executor_backend"], "governed_ipc_r0vm_sealed_memfd");
        assert_eq!(report["executor_binary_sha256"], GOVERNED_R0VM_SHA256);
        assert_eq!(report["executor_binary_sealed_memfd"], true);
        assert_eq!(report["executor_environment_exact"], true);
        assert_eq!(report["dynamic_loader_closure_verified"], false);
        assert_eq!(report["authoritative_negative_evidence"], false);
        assert_eq!(report["same_uid_source_mutation_resistance"], true);
        assert_eq!(report["semantic_input_bytes"], input_bytes.len());
        assert_eq!(report["semantic_input_sha256"], sha256_hex(&input_bytes));
        assert_eq!(report["semantic_receipt_created"], false);
        assert_eq!(report["receipt_written"], false);
        assert_eq!(report["cryptographic_reject_receipt_exists"], false);
        assert!(report.get("receipt_sha256").is_none());

        assert!(negative_duplicate_source_report_bytes(&raw_input, 1, 2).is_err());
        assert!(negative_duplicate_source_report_bytes(&raw_input, 2, 1).is_err());
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
