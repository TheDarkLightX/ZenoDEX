use std::{
    env, fs,
    io::{Read, Write},
    path::{Path, PathBuf},
};

#[cfg(unix)]
use std::os::unix::fs::MetadataExt;

use risc0_zkvm::{compute_image_id, Digest, InnerReceipt, Receipt};
use serde::Serialize;
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
    bind_semantic_guest_input_after_level_one_verification_v2,
    compose_semantic_epoch_after_level_one_verification_v2, SemanticEpochCompositionPolicyV2,
    SemanticEpochCompositionProjectionV2, SemanticGuestInputV2, SemanticGuestLeafDisclosureV1,
    SemanticGuestLevelOneDisclosureV1,
};
use zenodex_zrpf_risc0_shared::program_id_from_risc0_words_v3;
use zenodex_zrpf_risc0_verifier::{
    VerifiedNodeReceiptErrorV3, VerifiedNodeReceiptV3, VerifiedSemanticEpochReceiptErrorV2,
    VerifiedSemanticEpochReceiptV2,
};

const MAX_RECEIPT_BYTES: usize = 16 * 1_024 * 1_024;
const MAX_RECEIPT_BYTES_U64: u64 = MAX_RECEIPT_BYTES as u64;
const MAX_RECEIPT_READ_BYTES_U64: u64 = MAX_RECEIPT_BYTES_U64 + 1;
const MAX_REPORT_BYTES: usize = 32 * 1_024;
const MAX_LEVEL_ONE_GROUPS: usize = 8;
const MAX_LEAVES_PER_GROUP: usize = 8;
const MAX_TOTAL_LEAVES: usize = 64;
const SEMANTIC_SEAL_MUTATION_WORD_INDEX: usize = 1;

struct Options {
    semantic_receipt_path: PathBuf,
    groups: Vec<GroupOptions>,
    mode: VerificationMode,
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum VerificationMode {
    VerifyBaseline,
    ExpectSealReject { candidate_path: PathBuf },
    WriteAndExpectSealReject { candidate_path: PathBuf },
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

struct VerifiedBaseline {
    groups: Vec<VerifiedGroup>,
    projection: SemanticEpochCompositionProjectionV2,
    receipt_bytes: Vec<u8>,
    verified: VerifiedSemanticEpochReceiptV2,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct SealWordMutation {
    word_count: usize,
    word_index: usize,
    original_word: u32,
    mutated_word: u32,
}

#[derive(Serialize)]
struct ReceiptIdentity {
    journal_sha256: String,
    receipt_bytes: usize,
    receipt_sha256: String,
}

#[derive(Serialize)]
struct GroupIdentity {
    adapter_receipts: Vec<ReceiptIdentity>,
    level_one_receipt: ReceiptIdentity,
}

#[derive(Serialize)]
struct BaselineReport<'a> {
    adapter_image_id: String,
    adapter_receipts_sealed_verified: usize,
    claim_binding: String,
    dependency_programs_governed: bool,
    exact_expected_proposal_verified: bool,
    groups: Vec<GroupIdentity>,
    leaf_count: u64,
    level_one_group_count: usize,
    level_one_image_id: String,
    level_one_receipts_sealed_verified: usize,
    level_two_image_id: String,
    methods_validated: bool,
    nonclaims: [&'a str; 4],
    ok: bool,
    operation_count: u64,
    dependency_manifest_root: String,
    proof_tree_root: String,
    proposal_schema_version: u16,
    proposal_hash: String,
    receipt_profile_id: &'a str,
    schema: &'a str,
    semantic_epoch_image_id: String,
    semantic_epoch_root: String,
    semantic_statement_version: u16,
    semantic_receipt: ReceiptIdentity,
    status: &'a str,
    structural_level_two_journal_hash: String,
    verified_program_id: String,
    verified_program_manifest_root: String,
}

#[derive(Serialize)]
struct MutationRejectReport<'a> {
    adapter_receipts_sealed_verified: usize,
    baseline_exact_expected_proposal_verified: bool,
    baseline_semantic_receipt_verified: bool,
    candidate_accepted: bool,
    candidate_create_new: bool,
    candidate_origin: &'a str,
    candidate_reopened_with_created_file_identity: bool,
    control_passed: bool,
    expected_image_id: String,
    level_one_receipts_sealed_verified: usize,
    mutated_receipt_sha256: String,
    mutation: SealMutationReport<'a>,
    nonclaims: [&'a str; 4],
    ok: bool,
    reject: TypedRejectReport<'a>,
    schema: &'a str,
    semantic_epoch_root: String,
    source_receipt_sha256: String,
    status: &'a str,
}

#[derive(Serialize)]
struct SealMutationReport<'a> {
    journal_unchanged: bool,
    kind: &'a str,
    non_seal_receipt_bytes_unchanged: bool,
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
    outer_code: &'a str,
    variant: &'a str,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum CandidateOrigin {
    CallerPersisted,
    VerifierCreatedFromExactBaseline,
}

impl CandidateOrigin {
    const fn label(self) -> &'static str {
        match self {
            Self::CallerPersisted => "caller_persisted",
            Self::VerifierCreatedFromExactBaseline => "verifier_created_from_exact_baseline",
        }
    }

    const fn create_new(self) -> bool {
        matches!(self, Self::VerifierCreatedFromExactBaseline)
    }
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
    let baseline = verify_baseline(&options)?;
    let report_bytes = match &options.mode {
        VerificationMode::VerifyBaseline => baseline_report_bytes(&baseline)?,
        VerificationMode::ExpectSealReject { candidate_path } => {
            let candidate_bytes = read_bounded_regular_file(candidate_path)?;
            mutation_reject_report_bytes(
                &baseline,
                &candidate_bytes,
                CandidateOrigin::CallerPersisted,
            )?
        }
        VerificationMode::WriteAndExpectSealReject { candidate_path } => {
            let candidate_bytes = write_exact_seal_mutation_candidate(&baseline, candidate_path)?;
            mutation_reject_report_bytes(
                &baseline,
                &candidate_bytes,
                CandidateOrigin::VerifierCreatedFromExactBaseline,
            )?
        }
    };
    write_report(&report_bytes)
}

fn process_args() -> Result<Vec<String>, String> {
    env::args_os()
        .skip(1)
        .map(|value| value.into_string().map_err(|_| usage().to_owned()))
        .collect()
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args: Vec<String> = args.into_iter().collect();
    if args.len() < 7 || args.first().map(String::as_str) != Some("--semantic") {
        return Err(usage().to_owned());
    }
    let semantic_receipt_path = required_path(&args, 1)?;
    let mut cursor = 2usize;
    let mode = match args.get(cursor).map(String::as_str) {
        Some("--expect-seal-reject") => {
            let candidate_path = required_path(&args, cursor + 1)?;
            cursor = cursor.checked_add(2).ok_or_else(|| usage().to_owned())?;
            VerificationMode::ExpectSealReject { candidate_path }
        }
        Some("--write-and-expect-seal-reject") => {
            let candidate_path = required_path(&args, cursor + 1)?;
            cursor = cursor.checked_add(2).ok_or_else(|| usage().to_owned())?;
            VerificationMode::WriteAndExpectSealReject { candidate_path }
        }
        _ => VerificationMode::VerifyBaseline,
    };
    let (groups, final_cursor) = parse_groups(&args, cursor)?;
    if final_cursor != args.len() {
        return Err(usage().to_owned());
    }
    Ok(Options {
        semantic_receipt_path,
        groups,
        mode,
    })
}

fn parse_groups(args: &[String], mut cursor: usize) -> Result<(Vec<GroupOptions>, usize), String> {
    let mut groups = Vec::new();
    let mut total_leaves = 0usize;
    while cursor < args.len() {
        if groups.len() == MAX_LEVEL_ONE_GROUPS
            || args.get(cursor).map(String::as_str) != Some("--l1")
        {
            return Err(usage().to_owned());
        }
        let level_one_receipt_path = required_path(args, cursor + 1)?;
        cursor = cursor.checked_add(2).ok_or_else(|| usage().to_owned())?;
        let (leaves, next_cursor) = parse_group_leaves(args, cursor)?;
        cursor = next_cursor;
        total_leaves = total_leaves
            .checked_add(leaves.len())
            .ok_or_else(|| usage().to_owned())?;
        if total_leaves > MAX_TOTAL_LEAVES {
            return Err(usage().to_owned());
        }
        groups.push(GroupOptions {
            level_one_receipt_path,
            leaves,
        });
    }
    if groups.is_empty() {
        return Err(usage().to_owned());
    }
    Ok((groups, cursor))
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
        leaves.push(LeafOptions {
            adapter_receipt_path: required_path(args, cursor + 1)?,
            semantic_opening: parse_opening_hex(
                args.get(cursor + 2).ok_or_else(|| usage().to_owned())?,
            )?,
        });
        cursor = cursor.checked_add(3).ok_or_else(|| usage().to_owned())?;
    }
    if leaves.is_empty() {
        return Err(usage().to_owned());
    }
    Ok((leaves, cursor))
}

fn required_path(args: &[String], index: usize) -> Result<PathBuf, String> {
    args.get(index)
        .filter(|value| !value.is_empty() && !value.starts_with("--"))
        .map(PathBuf::from)
        .ok_or_else(|| usage().to_owned())
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
    "usage: verify_semantic_epoch --semantic <semantic.receipt.json> [--expect-seal-reject <mutated-semantic.receipt.json> | --write-and-expect-seal-reject <new-mutated-semantic.receipt.json>] --l1 <l1.receipt.json> --leaf <adapter.receipt.json> <opening-hex> [--leaf <adapter.receipt.json> <opening-hex> ...] [--l1 <l1.receipt.json> --leaf <adapter.receipt.json> <opening-hex> ...]"
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

fn verify_baseline(options: &Options) -> Result<VerifiedBaseline, String> {
    // A and B journal bytes become semantic inputs only after their exact
    // Succinct receipts cross the sealed verifier boundary.
    let groups = load_verified_groups(&options.groups)?;
    let raw_input = semantic_guest_input(&groups)?;
    let semantic_input = bind_semantic_guest_input_after_level_one_verification_v2(&raw_input)
        .map_err(|error| format!("host semantic disclosure binding rejected: {error}"))?;
    let projection =
        compose_semantic_epoch_after_level_one_verification_v2(&semantic_input, semantic_policy()?)
            .map_err(|error| format!("host semantic composition rejected: {error}"))?;
    let receipt_bytes = read_bounded_regular_file(&options.semantic_receipt_path)?;
    let verified = VerifiedSemanticEpochReceiptV2::verify_exact_succinct_bytes(
        &receipt_bytes,
        ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID,
        &governed_dependency_programs()?,
        projection.proposal(),
    )
    .map_err(|error| format!("semantic receipt exact sealed verification: {error}"))?;
    Ok(VerifiedBaseline {
        groups,
        projection,
        receipt_bytes,
        verified,
    })
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

fn semantic_guest_input(groups: &[VerifiedGroup]) -> Result<SemanticGuestInputV2, String> {
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
    SemanticGuestInputV2::new(disclosures)
        .map_err(|error| format!("semantic guest input rejected: {error}"))
}

fn semantic_policy() -> Result<SemanticEpochCompositionPolicyV2, String> {
    SemanticEpochCompositionPolicyV2::new(
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

fn baseline_report_bytes(baseline: &VerifiedBaseline) -> Result<Vec<u8>, String> {
    let proposal = baseline.verified.proposal();
    let proposal_hash = proposal
        .proposal_hash()
        .map_err(|error| format!("semantic proposal hash: {error}"))?;
    let groups = baseline
        .groups
        .iter()
        .map(group_identity)
        .collect::<Result<Vec<_>, _>>()?;
    let leaf_count = baseline
        .groups
        .iter()
        .try_fold(0usize, |sum, group| sum.checked_add(group.leaves.len()))
        .ok_or_else(|| "semantic report leaf count overflow".to_owned())?;
    let report = BaselineReport {
        adapter_image_id: image_id_string(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID),
        adapter_receipts_sealed_verified: leaf_count,
        claim_binding: commitment_hex(baseline.verified.claim_binding()),
        dependency_programs_governed: true,
        exact_expected_proposal_verified: true,
        groups,
        leaf_count: proposal.leaf_count(),
        level_one_group_count: baseline.groups.len(),
        level_one_image_id: image_id_string(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L1_ID),
        level_one_receipts_sealed_verified: baseline.groups.len(),
        level_two_image_id: image_id_string(ZENODEX_ZRPF_RISC0_STRUCTURAL_AGGREGATE_L2_ID),
        methods_validated: true,
        nonclaims: semantic_nonclaims(),
        ok: true,
        operation_count: proposal.operation_count(),
        dependency_manifest_root: commitment_hex(proposal.dependency_manifest_root()),
        proof_tree_root: commitment_hex(proposal.proof_tree_root()),
        proposal_schema_version: proposal.proposal_schema_version(),
        proposal_hash: commitment_hex(proposal_hash),
        receipt_profile_id: baseline.verified.receipt_profile().profile_id(),
        schema: "zenodex/zrpf_semantic_epoch_persisted_verification/v2",
        semantic_epoch_image_id: image_id_string(ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID),
        semantic_epoch_root: commitment_hex(proposal.semantic_epoch_root()),
        semantic_statement_version: proposal.semantic_statement_version(),
        semantic_receipt: receipt_identity(baseline.verified.receipt(), &baseline.receipt_bytes)?,
        status: "persisted_bounded_v2_semantic_epoch_exact_receipt_verified",
        structural_level_two_journal_hash: commitment_hex(
            baseline
                .projection
                .structural_level_two_journal()
                .canonical_hash()
                .map_err(|error| format!("structural level-two journal hash: {error}"))?,
        ),
        verified_program_id: hex::encode(baseline.verified.verified_program_id().as_bytes()),
        verified_program_manifest_root: commitment_hex(
            baseline.verified.verified_program_manifest_root(),
        ),
    };
    encode_bounded_report(&report)
}

fn mutation_reject_report_bytes(
    baseline: &VerifiedBaseline,
    candidate_bytes: &[u8],
    origin: CandidateOrigin,
) -> Result<Vec<u8>, String> {
    let candidate = decode_canonical_receipt(candidate_bytes)?;
    let mutation = require_exact_semantic_seal_mutation(baseline.verified.receipt(), &candidate)?;
    let dependencies = governed_dependency_programs()?;
    let reject = VerifiedSemanticEpochReceiptV2::verify_exact_succinct_bytes(
        candidate_bytes,
        ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID,
        &dependencies,
        baseline.verified.proposal(),
    );
    let reject = require_exact_receipt_verification_reject(reject)?;
    let leaf_count = baseline
        .groups
        .iter()
        .try_fold(0usize, |sum, group| sum.checked_add(group.leaves.len()))
        .ok_or_else(|| "mutation report leaf count overflow".to_owned())?;
    let report = MutationRejectReport {
        adapter_receipts_sealed_verified: leaf_count,
        baseline_exact_expected_proposal_verified: true,
        baseline_semantic_receipt_verified: true,
        candidate_accepted: false,
        candidate_create_new: origin.create_new(),
        candidate_origin: origin.label(),
        candidate_reopened_with_created_file_identity: origin.create_new(),
        control_passed: true,
        expected_image_id: image_id_string(ZENODEX_ZRPF_RISC0_SEMANTIC_EPOCH_ID),
        level_one_receipts_sealed_verified: baseline.groups.len(),
        mutated_receipt_sha256: sha256_hex(candidate_bytes),
        mutation: SealMutationReport {
            journal_unchanged: candidate.journal.bytes == baseline.verified.receipt().journal.bytes,
            kind: "succinct_seal_word_1_xor_1_v1",
            non_seal_receipt_bytes_unchanged: true,
            seal_word_count: mutation.word_count,
            seal_word_index: mutation.word_index,
            seal_word_mutated: mutation.mutated_word,
            seal_word_original: mutation.original_word,
            xor_mask: 1,
        },
        nonclaims: mutation_nonclaims(),
        ok: true,
        reject: TypedRejectReport {
            boundary: "VerifiedSemanticEpochReceiptV2::verify_exact_succinct_bytes",
            code: reject.code(),
            outer_code: VerifiedSemanticEpochReceiptErrorV2::ReceiptArtifact(reject).code(),
            variant: "ReceiptArtifact(ReceiptVerificationFailed)",
        },
        schema: "zenodex/zrpf_semantic_epoch_succinct_seal_mutation_reject/v2",
        semantic_epoch_root: commitment_hex(baseline.verified.proposal().semantic_epoch_root()),
        source_receipt_sha256: sha256_hex(&baseline.receipt_bytes),
        status: "persisted_semantic_epoch_v2_succinct_seal_mutation_rejected",
    };
    encode_bounded_report(&report)
}

fn write_exact_seal_mutation_candidate(
    baseline: &VerifiedBaseline,
    path: &Path,
) -> Result<Vec<u8>, String> {
    let candidate_bytes = exact_seal_mutation_candidate_bytes(baseline.verified.receipt())?;
    let reopened = persist_new_and_reopen_candidate(path, &candidate_bytes)?;
    let reopened_receipt = decode_canonical_receipt(&reopened)?;
    require_exact_semantic_seal_mutation(baseline.verified.receipt(), &reopened_receipt)?;
    Ok(reopened)
}

fn persist_new_and_reopen_candidate(
    path: &Path,
    candidate_bytes: &[u8],
) -> Result<Vec<u8>, String> {
    if candidate_bytes.is_empty() || candidate_bytes.len() > MAX_RECEIPT_BYTES {
        return Err("semantic mutation candidate bytes exceed persistence bound".to_owned());
    }
    let mut output = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("create semantic seal mutation candidate: {error}"))?;
    output
        .write_all(candidate_bytes)
        .map_err(|error| format!("write semantic seal mutation candidate: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync semantic seal mutation candidate: {error}"))?;
    let created_metadata = output
        .metadata()
        .map_err(|error| format!("created semantic mutation metadata: {error}"))?;
    let reopened = read_bounded_regular_file_with_version(path, Some(&created_metadata))?;
    if reopened != candidate_bytes {
        return Err("reopened semantic mutation candidate bytes differ from creation".to_owned());
    }
    Ok(reopened)
}

fn exact_seal_mutation_candidate_bytes(source: &Receipt) -> Result<Vec<u8>, String> {
    let mut candidate = source.clone();
    let InnerReceipt::Succinct(inner) = &mut candidate.inner else {
        return Err("exact-verified semantic receipt is not Succinct".to_owned());
    };
    if inner.seal.len() <= SEMANTIC_SEAL_MUTATION_WORD_INDEX {
        return Err("semantic Succinct seal has no word 1 to mutate".to_owned());
    }
    inner.seal[SEMANTIC_SEAL_MUTATION_WORD_INDEX] ^= 1;
    require_exact_semantic_seal_mutation(source, &candidate)?;
    canonical_receipt_bytes(&candidate)
}

fn require_exact_receipt_verification_reject(
    result: Result<VerifiedSemanticEpochReceiptV2, VerifiedSemanticEpochReceiptErrorV2>,
) -> Result<VerifiedNodeReceiptErrorV3, String> {
    match result {
        Err(VerifiedSemanticEpochReceiptErrorV2::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed,
        )) => Ok(VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed),
        Ok(_) => Err("mutated semantic Succinct seal was accepted".to_owned()),
        Err(error) => Err(format!(
            "mutated semantic receipt rejected at unexpected boundary: {}",
            error.code()
        )),
    }
}

fn require_exact_semantic_seal_mutation(
    source: &Receipt,
    candidate: &Receipt,
) -> Result<SealWordMutation, String> {
    let InnerReceipt::Succinct(source_inner) = &source.inner else {
        return Err("source semantic receipt is not Succinct".to_owned());
    };
    let InnerReceipt::Succinct(candidate_inner) = &candidate.inner else {
        return Err("mutated semantic candidate is not Succinct".to_owned());
    };
    let mutation = require_exact_seal_word_mutation(&source_inner.seal, &candidate_inner.seal)?;
    let mut restored = candidate.clone();
    let InnerReceipt::Succinct(restored_inner) = &mut restored.inner else {
        return Err("mutated semantic candidate restoration failed".to_owned());
    };
    restored_inner.seal[mutation.word_index] = mutation.original_word;
    if canonical_receipt_bytes(&restored)? != canonical_receipt_bytes(source)? {
        return Err("mutated semantic candidate changes non-seal receipt fields".to_owned());
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
    if *word_index != SEMANTIC_SEAL_MUTATION_WORD_INDEX || original_word ^ mutated_word != 1 {
        return Err("Succinct seal candidate must XOR word 1 by exactly 1".to_owned());
    }
    Ok(SealWordMutation {
        word_count: source.len(),
        word_index: *word_index,
        original_word: *original_word,
        mutated_word: *mutated_word,
    })
}

fn group_identity(group: &VerifiedGroup) -> Result<GroupIdentity, String> {
    Ok(GroupIdentity {
        adapter_receipts: group
            .leaves
            .iter()
            .map(|leaf| receipt_identity_from_verified_node(&leaf.adapter))
            .collect::<Result<Vec<_>, _>>()?,
        level_one_receipt: receipt_identity_from_verified_node(&group.level_one)?,
    })
}

fn receipt_identity_from_verified_node(
    node: &VerifiedNodeReceiptV3,
) -> Result<ReceiptIdentity, String> {
    let receipt_bytes = canonical_receipt_bytes(node.receipt())?;
    receipt_identity(node.receipt(), &receipt_bytes)
}

fn receipt_identity(receipt: &Receipt, receipt_bytes: &[u8]) -> Result<ReceiptIdentity, String> {
    if canonical_receipt_bytes(receipt)? != receipt_bytes {
        return Err("receipt identity input is not exact canonical bytes".to_owned());
    }
    Ok(ReceiptIdentity {
        journal_sha256: sha256_hex(&receipt.journal.bytes),
        receipt_bytes: receipt_bytes.len(),
        receipt_sha256: sha256_hex(receipt_bytes),
    })
}

fn read_bounded_regular_file(path: &Path) -> Result<Vec<u8>, String> {
    read_bounded_regular_file_with_version(path, None)
}

fn read_bounded_regular_file_with_version(
    path: &Path,
    expected_version: Option<&fs::Metadata>,
) -> Result<Vec<u8>, String> {
    let path_metadata =
        fs::symlink_metadata(path).map_err(|error| format!("receipt metadata: {error}"))?;
    if !path_metadata.is_file()
        || path_metadata.file_type().is_symlink()
        || path_metadata.len() > MAX_RECEIPT_BYTES_U64
    {
        return Err("receipt must be a bounded non-symlink regular file".to_owned());
    }
    if expected_version.is_some_and(|expected| !same_file_version(expected, &path_metadata)) {
        return Err("persisted semantic mutation path changed before reopen".to_owned());
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

fn decode_canonical_receipt(bytes: &[u8]) -> Result<Receipt, String> {
    let receipt: Receipt =
        serde_json::from_slice(bytes).map_err(|error| format!("receipt JSON: {error}"))?;
    if canonical_receipt_bytes(&receipt)? != bytes {
        return Err("receipt JSON is not canonical".to_owned());
    }
    Ok(receipt)
}

fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, String> {
    let bytes = serde_json::to_vec(receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_RECEIPT_BYTES {
        return Err("canonical receipt bytes exceed evidence bound".to_owned());
    }
    Ok(bytes)
}

fn encode_bounded_report<T: Serialize>(report: &T) -> Result<Vec<u8>, String> {
    let bytes =
        serde_json::to_vec(report).map_err(|error| format!("canonical report encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_REPORT_BYTES {
        return Err("canonical semantic verification report exceeds bound".to_owned());
    }
    Ok(bytes)
}

fn write_report(bytes: &[u8]) -> Result<(), String> {
    let mut output = std::io::stdout().lock();
    output
        .write_all(bytes)
        .and_then(|()| output.write_all(b"\n"))
        .map_err(|error| format!("write semantic verification report: {error}"))
}

fn image_id_string(words: [u32; 8]) -> String {
    Digest::from(words).to_string()
}

fn commitment_hex(commitment: zenodex_zrpf_protocol_v3::CommitmentV3) -> String {
    hex::encode(commitment.as_bytes())
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex::encode(Sha256::digest(bytes))
}

fn semantic_nonclaims() -> [&'static str; 4] {
    [
        "local persisted-receipt verification is not public replay or an independent verifier implementation",
        "the semantic profile does not prove complete ZenoDEX economic or value-flow semantics",
        "the receipt does not prove data availability or durable atomic ledger admission",
        "no settlement, release, zero-knowledge privacy, or production authority",
    ]
}

fn mutation_nonclaims() -> [&'static str; 4] {
    [
        "the mutation control does not regenerate the semantic proof",
        "the mutation control is not public replay or an independent verifier implementation",
        "the semantic profile does not prove complete ZenoDEX economic or value-flow semantics",
        "no settlement, release, zero-knowledge privacy, or production authority",
    ]
}

#[cfg(test)]
mod tests {
    use std::{error::Error, fs, path::PathBuf};

    use risc0_zkvm::{FakeReceipt, InnerReceipt, Receipt, ReceiptClaim};
    use serde_json::{json, Value};

    use super::{
        encode_bounded_report, exact_seal_mutation_candidate_bytes, parse_options,
        persist_new_and_reopen_candidate, read_bounded_regular_file,
        require_exact_receipt_verification_reject, require_exact_seal_word_mutation,
        require_exact_semantic_seal_mutation, VerificationMode, MAX_RECEIPT_READ_BYTES_U64,
        MAX_REPORT_BYTES,
    };
    use zenodex_zrpf_risc0_verifier::{
        VerifiedNodeReceiptErrorV3, VerifiedSemanticEpochReceiptErrorV2,
    };

    fn opening(byte: u8) -> String {
        hex::encode([byte; 32])
    }

    fn baseline_args() -> Vec<String> {
        vec![
            "--semantic".to_owned(),
            "semantic.json".to_owned(),
            "--l1".to_owned(),
            "left.json".to_owned(),
            "--leaf".to_owned(),
            "adapter-0.json".to_owned(),
            opening(1),
            "--leaf".to_owned(),
            "adapter-1.json".to_owned(),
            opening(2),
            "--l1".to_owned(),
            "right.json".to_owned(),
            "--leaf".to_owned(),
            "adapter-2.json".to_owned(),
            opening(3),
        ]
    }

    fn synthetic_succinct_receipt() -> Receipt {
        let fake = FakeReceipt::new(ReceiptClaim::ok([1_u32; 8], b"journal".to_vec()));
        let fake_receipt = Receipt::try_from(fake).expect("fake receipt conversion");
        let mut value = serde_json::to_value(fake_receipt).expect("fake receipt JSON");
        let inner = value
            .get_mut("inner")
            .and_then(Value::as_object_mut)
            .expect("inner object");
        let fake = inner.remove("Fake").expect("fake inner");
        let claim = fake.get("claim").expect("fake claim").clone();
        *inner = serde_json::from_value(json!({
            "Succinct": {
                "seal": [10, 20, 30],
                "control_id": [1, 1, 1, 1, 1, 1, 1, 1],
                "claim": claim,
                "hashfn": "poseidon2",
                "verifier_parameters": [2, 2, 2, 2, 2, 2, 2, 2],
                "control_inclusion_proof": {"index": 0, "digests": []}
            }
        }))
        .expect("succinct inner object");
        value["metadata"]["verifier_parameters"] = json!([2, 2, 2, 2, 2, 2, 2, 2]);
        serde_json::from_value(value).expect("synthetic Succinct receipt")
    }

    #[test]
    fn given_exact_receipt_roles_when_cli_parses_then_grouping_is_preserved() -> Result<(), String>
    {
        let parsed = parse_options(baseline_args())?;
        assert_eq!(parsed.semantic_receipt_path, PathBuf::from("semantic.json"));
        assert_eq!(parsed.groups.len(), 2);
        assert_eq!(parsed.groups[0].leaves.len(), 2);
        assert_eq!(parsed.groups[1].leaves.len(), 1);
        assert_eq!(parsed.mode, VerificationMode::VerifyBaseline);
        Ok(())
    }

    #[test]
    fn given_mutation_candidate_when_cli_parses_then_mode_is_explicit() -> Result<(), String> {
        let mut args = baseline_args();
        args.splice(
            2..2,
            ["--expect-seal-reject".to_owned(), "mutated.json".to_owned()],
        );
        let parsed = parse_options(args)?;
        assert_eq!(
            parsed.mode,
            VerificationMode::ExpectSealReject {
                candidate_path: PathBuf::from("mutated.json")
            }
        );
        Ok(())
    }

    #[test]
    fn given_write_mutation_mode_when_cli_parses_then_create_new_path_is_explicit(
    ) -> Result<(), String> {
        let mut args = baseline_args();
        args.splice(
            2..2,
            [
                "--write-and-expect-seal-reject".to_owned(),
                "new-mutated.json".to_owned(),
            ],
        );
        let parsed = parse_options(args)?;
        assert_eq!(
            parsed.mode,
            VerificationMode::WriteAndExpectSealReject {
                candidate_path: PathBuf::from("new-mutated.json")
            }
        );
        Ok(())
    }

    #[test]
    fn malformed_or_ambiguous_cli_shapes_reject() {
        let mut zero_opening = baseline_args();
        zero_opening[6] = "00".repeat(32);
        assert!(parse_options(zero_opening).is_err());

        let mut late_mode = baseline_args();
        late_mode.extend(["--expect-seal-reject".to_owned(), "mutated.json".to_owned()]);
        assert!(parse_options(late_mode).is_err());

        let mut empty_path = baseline_args();
        empty_path[1].clear();
        assert!(parse_options(empty_path).is_err());
    }

    #[test]
    fn exact_seal_mutation_accepts_only_word_one_xor_one() -> Result<(), String> {
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
    fn exact_receipt_mutation_rejects_all_non_seal_drift() -> Result<(), String> {
        let source = synthetic_succinct_receipt();
        let mut candidate = source.clone();
        let InnerReceipt::Succinct(inner) = &mut candidate.inner else {
            return Err("synthetic candidate is not Succinct".to_owned());
        };
        inner.seal[1] ^= 1;
        let mutation = require_exact_semantic_seal_mutation(&source, &candidate)?;
        assert_eq!(mutation.word_index, 1);

        candidate.journal.bytes.push(0);
        assert!(require_exact_semantic_seal_mutation(&source, &candidate).is_err());
        Ok(())
    }

    #[test]
    fn typed_candidate_creation_clones_baseline_and_changes_only_word_one() -> Result<(), String> {
        let source = synthetic_succinct_receipt();
        let source_before = serde_json::to_vec(&source).map_err(|error| error.to_string())?;
        let candidate_bytes = exact_seal_mutation_candidate_bytes(&source)?;
        let candidate: Receipt =
            serde_json::from_slice(&candidate_bytes).map_err(|error| error.to_string())?;
        let mutation = require_exact_semantic_seal_mutation(&source, &candidate)?;
        assert_eq!(mutation.word_index, 1);
        assert_eq!(mutation.original_word ^ mutation.mutated_word, 1);
        assert_eq!(
            serde_json::to_vec(&source).map_err(|error| error.to_string())?,
            source_before
        );
        Ok(())
    }

    #[test]
    fn typed_candidate_persistence_is_create_new_and_reopened_exact() -> Result<(), String> {
        let directory = isolated_test_directory("create-new");
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir(&directory).map_err(|error| error.to_string())?;
        let path = directory.join("candidate.json");
        let candidate_bytes = exact_seal_mutation_candidate_bytes(&synthetic_succinct_receipt())?;
        assert_eq!(
            persist_new_and_reopen_candidate(&path, &candidate_bytes)?,
            candidate_bytes
        );
        assert!(persist_new_and_reopen_candidate(&path, b"different").is_err());
        fs::remove_dir_all(&directory).map_err(|error| error.to_string())?;
        Ok(())
    }

    #[test]
    fn only_nested_receipt_verification_failed_is_the_expected_reject() -> Result<(), String> {
        let exact = require_exact_receipt_verification_reject(Err(
            VerifiedSemanticEpochReceiptErrorV2::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed,
            ),
        ))?;
        assert_eq!(exact, VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed);

        assert!(require_exact_receipt_verification_reject(Err(
            VerifiedSemanticEpochReceiptErrorV2::ReceiptArtifact(
                VerifiedNodeReceiptErrorV3::ReceiptProfileMismatch("hash function"),
            ),
        ))
        .is_err());
        assert!(require_exact_receipt_verification_reject(Err(
            VerifiedSemanticEpochReceiptErrorV2::ProposalBytesMismatch,
        ))
        .is_err());
        Ok(())
    }

    #[test]
    fn report_encoder_is_canonical_and_bounded() -> Result<(), String> {
        let report = serde_json::json!({"b": 2, "a": 1});
        assert_eq!(encode_bounded_report(&report)?, br#"{"a":1,"b":2}"#);
        let oversized = "x".repeat(MAX_REPORT_BYTES);
        assert!(encode_bounded_report(&oversized).is_err());
        Ok(())
    }

    #[test]
    fn oversized_receipt_rejects_before_decode() -> Result<(), Box<dyn Error>> {
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
    fn symlink_receipt_rejects_before_decode() -> Result<(), Box<dyn Error>> {
        use std::os::unix::fs::symlink;

        let directory = isolated_test_directory("symlink");
        let _ = fs::remove_dir_all(&directory);
        fs::create_dir(&directory)?;
        let target = directory.join("target.json");
        let link = directory.join("receipt.json");
        fs::write(&target, b"{}")?;
        symlink(&target, &link)?;
        let result = read_bounded_regular_file(&link);
        fs::remove_dir_all(&directory)?;
        assert_eq!(
            result,
            Err("receipt must be a bounded non-symlink regular file".to_owned())
        );
        Ok(())
    }

    fn isolated_test_directory(label: &str) -> PathBuf {
        std::env::temp_dir().join(format!(
            "zenodex-zrpf-verify-semantic-{label}-{}",
            std::process::id()
        ))
    }
}
