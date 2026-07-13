use std::env;

use risc0_zkvm::{
    compute_image_id, default_executor, default_prover, sha::Digestible, Digest, ExecutorEnv,
    MaybePruned, ProverOpts, Receipt, ReceiptClaim,
};
use zenodex_zrpf_protocol_v3::NodeJournalV3;
use zenodex_zrpf_risc0_methods::{
    ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ELF, ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ID,
};
use zenodex_zrpf_risc0_shared::{
    project_policy_bound_v2_journal, source_policy_v2, SourceKindV2, V2LeafAdapterInputV2,
    V2_LEAF_ADAPTER_INPUT_SCHEMA_VERSION, V2_LEAF_ADAPTER_MAX_INPUT_BYTES,
};
use zenodex_zrpf_risc0_verifier::{VerifiedNodeReceiptErrorV3, VerifiedNodeReceiptV3};

#[path = "prove_spot_value_leaf_v4/artifact_io.rs"]
mod artifact_io;
#[path = "prove_v2_leaf_adapter/cli.rs"]
mod cli;
#[path = "prove_v2_leaf_adapter/source.rs"]
mod source;
#[cfg(test)]
#[path = "prove_v2_leaf_adapter/tests.rs"]
mod tests;

use artifact_io::{
    canonical_receipt_bytes, persist_receipt, read_bounded_regular_file, require_succinct,
    sha256_hex,
};
use cli::{parse_options, Mode, Options};
use source::{load_verified_source, VerifiedSourceReceipt};

struct VerifiedAdapterArtifact {
    receipt: Receipt,
    receipt_bytes: Vec<u8>,
    journal: NodeJournalV3,
    status: &'static str,
}

fn main() {
    if let Err(error) = run() {
        eprintln!("{error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    if env::var_os("RISC0_DEV_MODE").is_some() {
        return Err("ambient RISC0_DEV_MODE is forbidden".to_owned());
    }
    let options = parse_options(env::args().skip(1))?;
    validate_adapter_method()?;
    let source = load_verified_source(&options.source_proof)?;
    let input = adapter_input(&source.receipt, options.assigned_leaf_ordinal)?;
    if matches!(
        options.mode,
        Mode::MissingAssumption | Mode::SubstitutedSourceJournal
    ) {
        return execute_negative_control(&options, &source, input);
    }

    let expected = project_policy_bound_v2_journal(
        input.source_kind,
        &input.source_journal_bytes,
        input.assigned_leaf_ordinal,
        input.expected_adapter_image_id,
    )
    .map_err(|error| format!("V2 adapter host projection rejected: {error}"))?;
    let artifact = match options.mode {
        Mode::Prove => prove_and_persist(&options, &source, &input, &expected.journal)?,
        Mode::VerifyReceipt => load_and_verify(&options, &expected.journal)?,
        Mode::MissingAssumption | Mode::SubstitutedSourceJournal => {
            return Err("negative-control mode reached receipt handling".to_owned());
        }
    };
    emit_report(&options, &source, &artifact)
}

fn validate_adapter_method() -> Result<(), String> {
    if ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ELF.is_empty()
        || ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ID
            .iter()
            .all(|word| *word == 0)
    {
        return Err("V2 adapter method is a placeholder".to_owned());
    }
    let computed = compute_image_id(ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ELF)
        .map_err(|error| format!("compute V2 adapter image ID: {error}"))?;
    if computed != Digest::from(ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ID) {
        return Err("V2 adapter method image ID mismatch".to_owned());
    }
    Ok(())
}

fn adapter_input(
    source: &Receipt,
    assigned_leaf_ordinal: u64,
) -> Result<V2LeafAdapterInputV2, String> {
    let input = V2LeafAdapterInputV2 {
        schema_version: V2_LEAF_ADAPTER_INPUT_SCHEMA_VERSION,
        source_kind: SourceKindV2::Spot,
        source_journal_bytes: source.journal.bytes.clone(),
        assigned_leaf_ordinal,
        expected_adapter_image_id: ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ID,
    };
    input
        .validate_envelope()
        .map_err(|error| format!("V2 adapter input rejected: {error}"))?;
    Ok(input)
}

fn encode_input(input: &V2LeafAdapterInputV2) -> Result<(u32, Vec<u8>), String> {
    let bytes = postcard::to_allocvec(input)
        .map_err(|error| format!("V2 adapter input encode: {error}"))?;
    if bytes.is_empty() || bytes.len() > V2_LEAF_ADAPTER_MAX_INPUT_BYTES {
        return Err("V2 adapter input byte length unsupported".to_owned());
    }
    let length = u32::try_from(bytes.len()).map_err(|_| "V2 adapter input length exceeds u32")?;
    Ok((length, bytes))
}

fn prove_and_persist(
    options: &Options,
    source: &VerifiedSourceReceipt,
    input: &V2LeafAdapterInputV2,
    expected: &NodeJournalV3,
) -> Result<VerifiedAdapterArtifact, String> {
    let receipt_path = options
        .receipt_path
        .as_deref()
        .ok_or_else(|| "adapter receipt output path missing".to_owned())?;
    if receipt_path.exists() {
        return Err("adapter receipt output already exists".to_owned());
    }
    let receipt = prove_adapter(input, &source.receipt)?;
    let journal = verify_adapter_receipt(&receipt, expected)?;
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    persist_receipt(receipt_path, &receipt_bytes)?;
    let persisted = read_bounded_regular_file(receipt_path, "persisted V2 adapter receipt")?;
    if persisted != receipt_bytes {
        return Err("persisted V2 adapter receipt differs from verified bytes".to_owned());
    }
    verify_adapter_receipt_bytes(&persisted, expected)?;
    Ok(VerifiedAdapterArtifact {
        receipt,
        receipt_bytes,
        journal,
        status: "current_source_v2_adapter_succinct_receipt_verified_and_persisted",
    })
}

fn load_and_verify(
    options: &Options,
    expected: &NodeJournalV3,
) -> Result<VerifiedAdapterArtifact, String> {
    let receipt_path = options
        .receipt_path
        .as_deref()
        .ok_or_else(|| "adapter receipt input path missing".to_owned())?;
    let receipt_bytes = read_bounded_regular_file(receipt_path, "V2 adapter receipt")?;
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)
        .map_err(|error| format!("V2 adapter receipt JSON: {error}"))?;
    if canonical_receipt_bytes(&receipt)? != receipt_bytes {
        return Err("V2 adapter receipt JSON is not canonical".to_owned());
    }
    let journal = verify_adapter_receipt_bytes(&receipt_bytes, expected)?;
    Ok(VerifiedAdapterArtifact {
        receipt,
        receipt_bytes,
        journal,
        status: "persisted_current_source_v2_adapter_receipt_verified",
    })
}

fn prove_adapter(input: &V2LeafAdapterInputV2, source: &Receipt) -> Result<Receipt, String> {
    require_succinct(source, "current source assumption")?;
    let (length, bytes) = encode_input(input)?;
    let executor_env = ExecutorEnv::builder()
        .write_slice(&[length])
        .write_slice(&bytes)
        .add_assumption(source.clone())
        .build()
        .map_err(|error| format!("V2 adapter executor environment: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("V2 adapter proving failed: {error}"))?
        .receipt;
    require_succinct(&receipt, "V2 adapter")?;
    Ok(receipt)
}

fn verify_adapter_receipt(
    receipt: &Receipt,
    expected: &NodeJournalV3,
) -> Result<NodeJournalV3, String> {
    let receipt_bytes = canonical_receipt_bytes(receipt)?;
    verify_adapter_receipt_bytes(&receipt_bytes, expected)
}

fn verify_adapter_receipt_bytes(
    receipt_bytes: &[u8],
    expected: &NodeJournalV3,
) -> Result<NodeJournalV3, String> {
    match VerifiedNodeReceiptV3::verify_exact_succinct_bytes(
        receipt_bytes,
        ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ID,
        expected,
    ) {
        Ok(verified) => Ok(verified.journal().clone()),
        Err(VerifiedNodeReceiptErrorV3::ProgramIdMismatch) => {
            Err("V2 adapter journal program ID differs from verified image".to_owned())
        }
        Err(VerifiedNodeReceiptErrorV3::JournalBytesMismatch) => {
            Err("V2 adapter journal differs from pure host projection".to_owned())
        }
        Err(error) => Err(format!("V2 adapter receipt rejected: {error}")),
    }
}

fn execute_negative_control(
    options: &Options,
    source: &VerifiedSourceReceipt,
    mut input: V2LeafAdapterInputV2,
) -> Result<(), String> {
    let (assumption, status) = match options.mode {
        Mode::MissingAssumption => (None, "v2_missing_source_assumption_rejected"),
        Mode::SubstitutedSourceJournal => {
            let first = input
                .source_journal_bytes
                .first_mut()
                .ok_or_else(|| "verified source journal is empty".to_owned())?;
            *first ^= 1;
            (
                Some(&source.receipt),
                "v2_substituted_source_journal_rejected",
            )
        }
        Mode::Prove | Mode::VerifyReceipt => {
            return Err("positive mode reached negative control".to_owned());
        }
    };
    execute_assumption_reject(&input, assumption, status)
}

fn execute_assumption_reject(
    input: &V2LeafAdapterInputV2,
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
        .map_err(|error| format!("V2 negative-control environment: {error}"))?;
    let policy = source_policy_v2(SourceKindV2::Spot)
        .map_err(|error| format!("current source policy rejected: {error}"))?;
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
    match default_executor().execute(executor_env, ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ELF) {
        Ok(_) => Err("V2 adapter accepted an unresolved source receipt assumption".to_owned()),
        Err(error)
            if error
                .chain()
                .any(|cause| cause.to_string() == expected_reason) =>
        {
            println!(
                "{}",
                serde_json::json!({
                    "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ID).to_string(),
                    "ok": true,
                    "status": status,
                })
            );
            Ok(())
        }
        Err(error) => Err(format!(
            "V2 adapter failed outside the expected assumption boundary: {error:#}"
        )),
    }
}

fn emit_report(
    options: &Options,
    source: &VerifiedSourceReceipt,
    artifact: &VerifiedAdapterArtifact,
) -> Result<(), String> {
    let journal_hash = artifact
        .journal
        .canonical_hash()
        .map_err(|error| format!("V2 adapter journal hash: {error}"))?;
    let report = serde_json::json!({
        "adapter_image_id": Digest::from(ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ID).to_string(),
        "adapter_program_bytes": ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ELF.len(),
        "adapter_program_sha256": sha256_hex(ZENODEX_ZRPF_RISC0_V2_LEAF_ADAPTER_ELF),
        "adapter_receipt_bytes": artifact.receipt_bytes.len(),
        "adapter_receipt_sha256": sha256_hex(&artifact.receipt_bytes),
        "assigned_leaf_ordinal": options.assigned_leaf_ordinal,
        "journal_hash": hex::encode(journal_hash.as_bytes()),
        "journal_sha256": sha256_hex(&artifact.receipt.journal.bytes),
        "ok": true,
        "schema": "zenodex/zrpf_v2_leaf_adapter_proof_report/v1",
        "source_receipt_sha256": source.receipt_sha256,
        "status": artifact.status,
        "nonclaims": [
            "candidate current-source identities carry no release or production authority",
            "the adapter receipt proves no aggregate, settlement, ledger-admission, data-availability, or finality claim",
        ],
    });
    println!(
        "{}",
        serde_json::to_string(&report).map_err(|error| format!("V2 report encode: {error}"))?
    );
    Ok(())
}
