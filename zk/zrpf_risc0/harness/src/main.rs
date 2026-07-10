use std::{
    env, fs,
    io::{Read, Write},
    path::{Path, PathBuf},
};

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use risc0_zkvm::{
    compute_image_id, default_executor, default_prover, sha::Digestible, Digest, ExecutorEnv,
    InnerReceipt, MaybePruned, ProverOpts, Receipt, ReceiptClaim,
};
use serde::Deserialize;
use serde_json::{json, Value};
use sha2::{Digest as ShaDigest, Sha256};
use tau_state_proof_risc0_shared::{RecursiveEffectSummaryV1, PROOF_TYPE_RECURSIVE_SPOT_LEAF};
use zenodex_zrpf_protocol_v3::NodeJournalV3;
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF, ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
};
use zenodex_zrpf_risc0_shared::{
    project_policy_bound_v1_journal, risc0_image_words_to_bytes, source_policy_v1, SourceKindV1,
    V1LeafAdapterInputV1, V1_LEAF_ADAPTER_INPUT_SCHEMA_VERSION, V1_LEAF_ADAPTER_MAX_INPUT_BYTES,
};
use zenodex_zrpf_risc0_verifier::{VerifiedNodeReceiptErrorV3, VerifiedNodeReceiptV3};

const MAX_SOURCE_ARTIFACT_BYTES: usize = 16 * 1_024 * 1_024;
const RECEIPT_CODEC: &str = "risc0_receipt_canonical_serde_json_depth128_v1";

struct VerifiedSourceReceipt {
    receipt: Receipt,
    receipt_sha256: String,
}

#[derive(Deserialize, serde::Serialize)]
#[serde(deny_unknown_fields)]
struct SourceProofArtifact {
    meta: SpotProofMeta,
    proof: String,
    proof_type: String,
    schema: String,
    schema_version: u32,
    state_hash: String,
}

#[derive(Deserialize, serde::Serialize)]
#[serde(deny_unknown_fields)]
struct SpotProofMeta {
    accepted_receipts_root: String,
    asset_delta_root: String,
    asset_delta_rows: Vec<Value>,
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

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum HarnessMode {
    Prove,
    VerifyReceipt,
    MissingAssumption,
    SubstitutedSourceJournal,
    MislabeledAdapter,
}

struct HarnessOptions {
    source_path: PathBuf,
    assigned_leaf_ordinal: u64,
    receipt_out: Option<PathBuf>,
    adapter_receipt_in: Option<PathBuf>,
    mode: HarnessMode,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let options = parse_options(env::args().skip(1))?;
    validate_adapter_method()?;
    let source = load_verified_source(&options.source_path)?;

    if let Some(path) = &options.receipt_out {
        if path.exists() {
            return Err("receipt output already exists".to_owned());
        }
    }

    let input = adapter_input(
        &source.receipt,
        options.assigned_leaf_ordinal,
        ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
    )?;

    if options.mode == HarnessMode::VerifyReceipt {
        let expected = project_policy_bound_v1_journal(
            input.source_kind,
            &input.source_journal_bytes,
            input.assigned_leaf_ordinal,
            input.expected_adapter_image_id,
        )
        .map_err(|error| format!("host projection rejected: {error}"))?;
        let path = options
            .adapter_receipt_in
            .as_deref()
            .ok_or_else(|| "adapter receipt input missing".to_owned())?;
        let (receipt, receipt_bytes) = load_canonical_receipt(path, "adapter receipt")?;
        let journal = verify_adapter_receipt(&receipt, &expected.journal)?;
        println!(
            "{}",
            json!({
                "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
                "adapter_receipt_bytes": receipt_bytes.len(),
                "adapter_receipt_sha256": sha256_hex(&receipt_bytes),
                "assigned_leaf_ordinal": options.assigned_leaf_ordinal,
                "journal_hash": hex32(journal.canonical_hash().map_err(|error| format!("journal hash: {error}"))?.as_bytes()),
                "journal_sha256": sha256_hex(&receipt.journal.bytes),
                "ok": true,
                "source_receipt_sha256": source.receipt_sha256,
                "status": "persisted_adapter_receipt_verified",
            })
        );
        return Ok(());
    }

    match options.mode {
        HarnessMode::MissingAssumption => {
            return execute_assumption_reject(&input, None, "missing_source_assumption_rejected");
        }
        HarnessMode::SubstitutedSourceJournal => {
            let mut substituted = input.clone();
            let first_byte = substituted
                .source_journal_bytes
                .first_mut()
                .ok_or_else(|| "verified source journal is empty".to_owned())?;
            *first_byte ^= 1;
            return execute_assumption_reject(
                &substituted,
                Some(&source.receipt),
                "substituted_source_journal_rejected",
            );
        }
        HarnessMode::MislabeledAdapter => {
            return prove_mislabeled_adapter_reject(&source, options.assigned_leaf_ordinal);
        }
        HarnessMode::Prove => {}
        HarnessMode::VerifyReceipt => unreachable!("verify mode returned above"),
    }

    let expected = project_policy_bound_v1_journal(
        input.source_kind,
        &input.source_journal_bytes,
        input.assigned_leaf_ordinal,
        input.expected_adapter_image_id,
    )
    .map_err(|error| format!("host projection rejected: {error}"))?;
    let receipt = prove_adapter(&input, &source.receipt)?;
    let journal = verify_adapter_receipt(&receipt, &expected.journal)?;
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    if let Some(path) = &options.receipt_out {
        persist_receipt(path, &receipt_bytes)?;
    }
    println!(
        "{}",
        json!({
            "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
            "adapter_program_bytes": ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF.len(),
            "adapter_receipt_bytes": receipt_bytes.len(),
            "adapter_receipt_sha256": sha256_hex(&receipt_bytes),
            "adapter_receipt_written": options.receipt_out.is_some(),
            "assigned_leaf_ordinal": options.assigned_leaf_ordinal,
            "journal_hash": hex32(journal.canonical_hash().map_err(|error| format!("journal hash: {error}"))?.as_bytes()),
            "journal_sha256": sha256_hex(&receipt.journal.bytes),
            "ok": true,
            "source_receipt_sha256": source.receipt_sha256,
            "status": "temporary_path_spot_v1_adapter_receipt_verified",
            "nonclaims": [
                "temporary compiler-visible path is not a release image identity",
                "no aggregate V3 receipt or semantic-composition claim",
                "no settlement, ledger-admission, or production authority"
            ],
        })
    );
    Ok(())
}

fn usage() -> &'static str {
    "usage: zenodex-zrpf-risc0-harness <spot-v1-proof.json> [--ordinal N] [--receipt-out PATH|--verify-receipt PATH|--missing-assumption|--substituted-source-journal|--mislabeled-adapter]"
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<HarnessOptions, String> {
    let mut args = args.into_iter();
    let source_path = args
        .next()
        .filter(|value| !value.is_empty())
        .map(PathBuf::from)
        .ok_or_else(|| usage().to_owned())?;
    let mut assigned_leaf_ordinal = 0u64;
    let mut ordinal_set = false;
    let mut receipt_out = None;
    let mut adapter_receipt_in = None;
    let mut mode = HarnessMode::Prove;

    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--ordinal" if !ordinal_set => {
                let value = args.next().ok_or_else(|| usage().to_owned())?;
                assigned_leaf_ordinal = value
                    .parse::<u64>()
                    .map_err(|_| "ordinal must be a canonical unsigned integer".to_owned())?;
                if value != assigned_leaf_ordinal.to_string() {
                    return Err("ordinal must be a canonical unsigned integer".to_owned());
                }
                ordinal_set = true;
            }
            "--receipt-out" if receipt_out.is_none() => {
                let value = args
                    .next()
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| usage().to_owned())?;
                receipt_out = Some(PathBuf::from(value));
            }
            "--verify-receipt" if adapter_receipt_in.is_none() => {
                let value = args
                    .next()
                    .filter(|value| !value.is_empty())
                    .ok_or_else(|| usage().to_owned())?;
                set_mode(&mut mode, HarnessMode::VerifyReceipt)?;
                adapter_receipt_in = Some(PathBuf::from(value));
            }
            "--missing-assumption" => {
                set_mode(&mut mode, HarnessMode::MissingAssumption)?;
            }
            "--substituted-source-journal" => {
                set_mode(&mut mode, HarnessMode::SubstitutedSourceJournal)?;
            }
            "--mislabeled-adapter" => {
                set_mode(&mut mode, HarnessMode::MislabeledAdapter)?;
            }
            _ => return Err(usage().to_owned()),
        }
    }
    if mode != HarnessMode::Prove && receipt_out.is_some() {
        return Err("receipt output is only supported for a positive proof".to_owned());
    }
    if mode != HarnessMode::VerifyReceipt && adapter_receipt_in.is_some() {
        return Err("adapter receipt input requires verify mode".to_owned());
    }
    Ok(HarnessOptions {
        source_path,
        assigned_leaf_ordinal,
        receipt_out,
        adapter_receipt_in,
        mode,
    })
}

fn set_mode(mode: &mut HarnessMode, requested: HarnessMode) -> Result<(), String> {
    if *mode != HarnessMode::Prove {
        return Err("exactly one negative-control mode may be selected".to_owned());
    }
    *mode = requested;
    Ok(())
}

fn validate_adapter_method() -> Result<(), String> {
    if ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF.is_empty()
        || ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID
            .iter()
            .all(|word| *word == 0)
    {
        return Err("adapter method is a placeholder".to_owned());
    }
    let computed = compute_image_id(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF)
        .map_err(|error| format!("compute adapter image ID: {error}"))?;
    if computed != Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID) {
        return Err("adapter method image ID mismatch".to_owned());
    }
    Ok(())
}

fn load_verified_source(path: &Path) -> Result<VerifiedSourceReceipt, String> {
    let bytes = read_bounded_regular_file(path, "source proof")?;
    let artifact: SourceProofArtifact =
        serde_json::from_slice(&bytes).map_err(|error| format!("source proof JSON: {error}"))?;
    let canonical_artifact = serde_json::to_vec(&artifact)
        .map_err(|error| format!("source proof canonical encode: {error}"))?;
    if canonical_artifact != bytes {
        return Err("source proof JSON is not canonical".to_owned());
    }
    if artifact.schema != "tau_state_proof" || artifact.schema_version != 1 {
        return Err("source proof schema is unsupported".to_owned());
    }
    if artifact.proof_type != PROOF_TYPE_RECURSIVE_SPOT_LEAF {
        return Err("source proof type is not the pinned Spot leaf".to_owned());
    }
    let policy = source_policy_v1(SourceKindV1::Spot);
    if artifact.meta.proof_type != policy.proof_type
        || artifact.meta.proof_profile != policy.proof_profile
        || artifact.meta.risc0_image_id != Digest::from(policy.image_id).to_string()
        || artifact.meta.receipt_codec != RECEIPT_CODEC
        || artifact.meta.receipt_kind != "succinct"
    {
        return Err("source proof governed metadata mismatch".to_owned());
    }

    let proof_b64 = artifact.proof.as_str();
    if proof_b64.len() > MAX_SOURCE_ARTIFACT_BYTES.div_ceil(3) * 4 {
        return Err("source receipt base64 exceeds bound".to_owned());
    }
    let receipt_bytes = BASE64_STANDARD
        .decode(proof_b64)
        .map_err(|error| format!("source receipt base64: {error}"))?;
    if receipt_bytes.len() > MAX_SOURCE_ARTIFACT_BYTES
        || BASE64_STANDARD.encode(&receipt_bytes) != proof_b64
    {
        return Err("source receipt base64 is noncanonical or oversized".to_owned());
    }
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)
        .map_err(|error| format!("source receipt JSON: {error}"))?;
    let canonical =
        serde_json::to_vec(&receipt).map_err(|error| format!("source receipt encode: {error}"))?;
    if canonical != receipt_bytes {
        return Err("source receipt JSON is not canonical".to_owned());
    }
    require_succinct(&receipt, "source")?;
    receipt
        .verify(policy.image_id)
        .map_err(|error| format!("source receipt verification failed: {error}"))?;
    verify_source_artifact_bindings(&artifact, &receipt)?;
    Ok(VerifiedSourceReceipt {
        receipt,
        receipt_sha256: sha256_hex(&receipt_bytes),
    })
}

fn read_bounded_regular_file(path: &Path, label: &str) -> Result<Vec<u8>, String> {
    let input = fs::File::open(path).map_err(|error| format!("open {label}: {error}"))?;
    let metadata = input
        .metadata()
        .map_err(|error| format!("{label} metadata: {error}"))?;
    if !metadata.is_file() || metadata.len() > MAX_SOURCE_ARTIFACT_BYTES as u64 {
        return Err(format!("{label} must be a bounded regular file"));
    }
    let mut bytes = Vec::new();
    input
        .take((MAX_SOURCE_ARTIFACT_BYTES + 1) as u64)
        .read_to_end(&mut bytes)
        .map_err(|error| format!("read {label}: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_SOURCE_ARTIFACT_BYTES {
        return Err(format!("{label} byte length unsupported"));
    }
    Ok(bytes)
}

fn load_canonical_receipt(path: &Path, label: &str) -> Result<(Receipt, Vec<u8>), String> {
    let bytes = read_bounded_regular_file(path, label)?;
    let receipt: Receipt =
        serde_json::from_slice(&bytes).map_err(|error| format!("{label} JSON: {error}"))?;
    let canonical = canonical_receipt_bytes(&receipt)?;
    if canonical != bytes {
        return Err(format!("{label} JSON is not canonical"));
    }
    Ok((receipt, bytes))
}

fn verify_source_artifact_bindings(
    artifact: &SourceProofArtifact,
    receipt: &Receipt,
) -> Result<(), String> {
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
    let meta = &artifact.meta;
    let image_id = Digest::from(summary.risc0_image_id).to_string();
    let expected_hashes = [
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
    ];
    for (field, declared, expected) in expected_hashes {
        if declared != hex32(&expected) {
            return Err(format!("source metadata mismatch: {field}"));
        }
    }
    if meta.summary_version != summary.summary_version
        || meta.lane_id != summary.lane_id
        || meta.lane_kind != summary.lane_kind
        || meta.chain_id != summary.chain_id
        || meta.epoch_id != summary.epoch_id
        || meta.proof_profile != summary.proof_profile
        || meta.risc0_image_id != image_id
        || meta.child_image_id != image_id
        || !meta.asset_delta_rows.is_empty()
    {
        return Err("source metadata differs from authenticated journal".to_owned());
    }
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

fn adapter_input(
    source: &Receipt,
    assigned_leaf_ordinal: u64,
    expected_adapter_image_id: [u32; 8],
) -> Result<V1LeafAdapterInputV1, String> {
    let input = V1LeafAdapterInputV1 {
        schema_version: V1_LEAF_ADAPTER_INPUT_SCHEMA_VERSION,
        source_kind: SourceKindV1::Spot,
        source_journal_bytes: source.journal.bytes.clone(),
        assigned_leaf_ordinal,
        expected_adapter_image_id,
    };
    input
        .validate_envelope()
        .map_err(|error| format!("adapter input rejected: {error}"))?;
    Ok(input)
}

fn encode_input(input: &V1LeafAdapterInputV1) -> Result<(u32, Vec<u8>), String> {
    let bytes =
        postcard::to_allocvec(input).map_err(|error| format!("adapter input encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > V1_LEAF_ADAPTER_MAX_INPUT_BYTES {
        return Err("adapter input byte length unsupported".to_owned());
    }
    let length = u32::try_from(bytes.len()).map_err(|_| "adapter input length exceeds u32")?;
    Ok((length, bytes))
}

fn prove_adapter(input: &V1LeafAdapterInputV1, source: &Receipt) -> Result<Receipt, String> {
    require_succinct(source, "source assumption")?;
    let (length, bytes) = encode_input(input)?;
    let executor_env = ExecutorEnv::builder()
        .write_slice(&[length])
        .write_slice(&bytes)
        .add_assumption(source.clone())
        .build()
        .map_err(|error| format!("adapter executor environment: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("adapter proving failed: {error}"))?
        .receipt;
    require_succinct(&receipt, "adapter")?;
    Ok(receipt)
}

fn verify_adapter_receipt(
    receipt: &Receipt,
    expected: &NodeJournalV3,
) -> Result<NodeJournalV3, String> {
    match VerifiedNodeReceiptV3::verify_exact_succinct(
        receipt.clone(),
        ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID,
        expected,
    ) {
        Ok(verified) => Ok(verified.journal().clone()),
        Err(VerifiedNodeReceiptErrorV3::ProgramIdMismatch) => {
            Err("adapter journal program ID differs from verified image".to_owned())
        }
        Err(VerifiedNodeReceiptErrorV3::JournalBytesMismatch) => {
            Err("adapter journal differs from pure host projection".to_owned())
        }
        Err(error) => Err(format!("adapter receipt rejected: {error}")),
    }
}

fn execute_assumption_reject(
    input: &V1LeafAdapterInputV1,
    assumption: Option<&Receipt>,
    status: &str,
) -> Result<(), String> {
    let (length, bytes) = encode_input(input)?;
    let mut builder = ExecutorEnv::builder();
    builder.write_slice(&[length]).write_slice(&bytes);
    if let Some(receipt) = assumption {
        builder.add_assumption(receipt.clone());
    }
    let executor_env = builder
        .build()
        .map_err(|error| format!("missing-assumption environment: {error}"))?;
    let policy = source_policy_v1(SourceKindV1::Spot);
    let journal_digest = input.source_journal_bytes.as_slice().digest();
    let claim_digest = ReceiptClaim::ok(
        policy.image_id,
        MaybePruned::<Vec<u8>>::Pruned(journal_digest),
    )
    .digest();
    let expected_reason = format!(
        "sys_verify_integrity: no receipt found to resolve assumption: claim digest {claim_digest}, control root {}",
        Digest::ZERO
    );
    match default_executor().execute(executor_env, ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ELF) {
        Ok(_) => Err("adapter accepted a missing source receipt assumption".to_owned()),
        Err(error)
            if error
                .chain()
                .any(|cause| cause.to_string() == expected_reason) =>
        {
            println!(
                "{}",
                json!({
                    "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
                    "ok": true,
                    "status": status,
                })
            );
            Ok(())
        }
        Err(error) => Err(format!(
            "adapter failed without the exact missing-assumption reason: {error:#}"
        )),
    }
}

fn prove_mislabeled_adapter_reject(
    source: &VerifiedSourceReceipt,
    assigned_leaf_ordinal: u64,
) -> Result<(), String> {
    let mut substituted_image_id = ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID;
    substituted_image_id[0] ^= 1;
    let input = adapter_input(&source.receipt, assigned_leaf_ordinal, substituted_image_id)?;
    let expected = project_policy_bound_v1_journal(
        input.source_kind,
        &input.source_journal_bytes,
        input.assigned_leaf_ordinal,
        input.expected_adapter_image_id,
    )
    .map_err(|error| format!("host projection rejected: {error}"))?;
    let receipt = prove_adapter(&input, &source.receipt)?;
    match verify_adapter_receipt(&receipt, &expected.journal) {
        Ok(_) => Err("outer verifier accepted a mislabeled adapter program ID".to_owned()),
        Err(error) if error == "adapter journal program ID differs from verified image" => {
            println!(
                "{}",
                json!({
                    "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V1_LEAF_ADAPTER_ID).to_string(),
                    "adapter_receipt_sha256": receipt_sha256(&receipt)?,
                    "assigned_leaf_ordinal": assigned_leaf_ordinal,
                    "ok": true,
                    "status": "mislabeled_adapter_program_id_rejected_by_outer_verifier",
                    "substituted_program_id": hex32(&risc0_image_words_to_bytes(substituted_image_id)),
                })
            );
            Ok(())
        }
        Err(error) => Err(format!(
            "mislabeled adapter failed at the wrong boundary: {error}"
        )),
    }
}

fn require_succinct(receipt: &Receipt, label: &str) -> Result<(), String> {
    if !matches!(&receipt.inner, InnerReceipt::Succinct(_)) {
        return Err(format!("{label} receipt is not Succinct"));
    }
    Ok(())
}

fn receipt_sha256(receipt: &Receipt) -> Result<String, String> {
    let bytes = canonical_receipt_bytes(receipt)?;
    Ok(sha256_hex(&bytes))
}

fn canonical_receipt_bytes(receipt: &Receipt) -> Result<Vec<u8>, String> {
    let bytes = serde_json::to_vec(receipt).map_err(|error| format!("receipt encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > MAX_SOURCE_ARTIFACT_BYTES {
        return Err("canonical receipt bytes exceed evidence bound".to_owned());
    }
    Ok(bytes)
}

fn persist_receipt(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut output = fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .map_err(|error| format!("create receipt output: {error}"))?;
    output
        .write_all(bytes)
        .map_err(|error| format!("write receipt output: {error}"))?;
    output
        .sync_all()
        .map_err(|error| format!("sync receipt output: {error}"))
}

fn sha256_hex(bytes: &[u8]) -> String {
    hex32(&Sha256::digest(bytes))
}

fn hex32(bytes: &[u8]) -> String {
    hex::encode(bytes)
}

#[cfg(test)]
mod tests {
    use super::{parse_options, HarnessMode};

    fn strings(values: &[&str]) -> Vec<String> {
        values.iter().map(|value| (*value).to_owned()).collect()
    }

    #[test]
    fn options_accept_canonical_positive_form() {
        let options = parse_options(strings(&[
            "source.json",
            "--ordinal",
            "7",
            "--receipt-out",
            "receipt.json",
        ]))
        .expect("valid options");
        assert_eq!(options.mode, HarnessMode::Prove);
        assert_eq!(options.assigned_leaf_ordinal, 7);
        assert!(options.receipt_out.is_some());
        assert!(options.adapter_receipt_in.is_none());
    }

    #[test]
    fn options_reject_noncanonical_ordinal() {
        assert!(parse_options(strings(&["source.json", "--ordinal", "07"])).is_err());
    }

    #[test]
    fn options_reject_multiple_negative_modes() {
        assert!(parse_options(strings(&[
            "source.json",
            "--missing-assumption",
            "--mislabeled-adapter",
        ]))
        .is_err());
    }

    #[test]
    fn options_reject_negative_receipt_output() {
        assert!(parse_options(strings(&[
            "source.json",
            "--receipt-out",
            "receipt.json",
            "--substituted-source-journal",
        ]))
        .is_err());
    }

    #[test]
    fn options_accept_receipt_verification_mode() {
        let options = parse_options(strings(&[
            "source.json",
            "--ordinal",
            "3",
            "--verify-receipt",
            "adapter.json",
        ]))
        .expect("valid verify options");
        assert_eq!(options.mode, HarnessMode::VerifyReceipt);
        assert!(options.adapter_receipt_in.is_some());
        assert!(options.receipt_out.is_none());
    }

    #[test]
    fn options_reject_verify_and_negative_mode() {
        assert!(parse_options(strings(&[
            "source.json",
            "--verify-receipt",
            "adapter.json",
            "--missing-assumption",
        ]))
        .is_err());
    }
}
