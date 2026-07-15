use std::{env, path::Path, path::PathBuf};

use base64::{engine::general_purpose::STANDARD as BASE64_STANDARD, Engine};
use risc0_zkvm::{compute_image_id, default_prover, Digest, ProverOpts, Receipt};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use tau_state_proof_risc0_shared::{
    compose_spot_recursive_leaf_summary_v1, RecursiveEffectSummaryV1, SpotRecursiveLeafInputV1,
    PROOF_TYPE_RECURSIVE_SPOT_LEAF,
};
use zenodex_zrpf_risc0_execution_profile::build_exact_framed_executor_env_v1;
use zenodex_zrpf_risc0_shared::{project_policy_bound_v2_journal, source_policy_v2, SourceKindV2};
use zenodex_zrpf_risc0_spot_v6_methods::{
    ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF, ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID,
};
use zenodex_zrpf_risc0_spot_value_leaf_v6_shared::{
    encode_source_opened_spot_value_leaf_input_v6,
    recompose_source_opened_spot_value_leaf_statement_v6, SourceOpenedSpotValueLeafEnvelopeV6,
    PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
};
use zenodex_zrpf_risc0_verifier::{
    VerifiedNodeReceiptV3, VerifiedSourceOpenedSpotValueLeafReceiptV6,
};

#[path = "prove_spot_value_leaf_v4/artifact_io.rs"]
mod artifact_io;

use artifact_io::{
    canonical_receipt_bytes, persist_receipt, read_bounded_regular_file, require_succinct,
    sha256_hex, MAX_ARTIFACT_BYTES,
};

const ASSIGNED_LEAF_ORDINAL: u64 = 0;

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceRequestArtifact {
    proof_type: String,
    receipt_kind: String,
    schema: String,
    schema_version: u32,
    spot_recursive_leaf_input: SpotRecursiveLeafInputV1,
    state_hash: String,
}

#[derive(Deserialize, Serialize)]
#[serde(deny_unknown_fields)]
struct SourceProofArtifact {
    meta: Value,
    proof: String,
    proof_type: String,
    schema: String,
    schema_version: u32,
    state_hash: String,
}

#[derive(Debug)]
struct Options {
    receipt_out: PathBuf,
    source_envelope_out: PathBuf,
    source_request: PathBuf,
    source_proof: PathBuf,
    adapter_receipt: PathBuf,
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
    validate_v6_method()?;
    let (source_input, source_receipt, source_proof_bytes) =
        load_exact_source(&options.source_request, &options.source_proof)?;
    let adapter_bytes = read_bounded_regular_file(&options.adapter_receipt, "adapter receipt")?;
    let adapter = load_exact_adapter(&adapter_bytes, &source_receipt)?;
    let envelope = SourceOpenedSpotValueLeafEnvelopeV6::new(
        ASSIGNED_LEAF_ORDINAL,
        adapter.receipt().journal.bytes.clone(),
        postcard::to_allocvec(&source_input)
            .map_err(|error| format!("source input Postcard encode: {error}"))?,
        source_receipt.journal.bytes.clone(),
    )
    .map_err(|error| format!("V6 envelope rejected: {error}"))?;
    let expected_statement = recompose_source_opened_spot_value_leaf_statement_v6(&envelope)
        .map_err(|error| format!("V6 host recomposition rejected: {error}"))?;
    let input_bytes = encode_source_opened_spot_value_leaf_input_v6(&envelope)
        .map_err(|error| format!("V6 input encoding rejected: {error}"))?;
    let executor_env =
        build_exact_framed_executor_env_v1(&input_bytes, std::slice::from_ref(adapter.receipt()))
            .map_err(|error| format!("V6 executor environment rejected: {error}"))?;
    let receipt = default_prover()
        .prove_with_opts(
            executor_env,
            ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF,
            &ProverOpts::succinct(),
        )
        .map_err(|error| format!("V6 source-opened Spot proving failed: {error}"))?
        .receipt;
    require_succinct(&receipt, "V6 source-opened Spot")?;
    let receipt_bytes = canonical_receipt_bytes(&receipt)?;
    let verified =
        VerifiedSourceOpenedSpotValueLeafReceiptV6::verify_governed_exact_succinct_bytes(
            &receipt_bytes,
            &expected_statement,
        )
        .map_err(|error| format!("fresh V6 receipt verification failed: {error}"))?;
    persist_receipt(&options.source_envelope_out, &input_bytes)?;
    persist_receipt(&options.receipt_out, &receipt_bytes)?;

    let report = serde_json::json!({
        "action_nullifier_root": hex::encode(expected_statement.action_nullifier_root().as_bytes()),
        "adapter_receipt_sha256": sha256_hex(&adapter_bytes),
        "candidate_accepted": true,
        "guest_program_binary_bytes": ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF.len(),
        "guest_program_binary_sha256": sha256_hex(ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF),
        "ok": true,
        "receipt_bytes": receipt_bytes.len(),
        "receipt_profile_id": verified.receipt_profile().profile_id(),
        "receipt_sha256": sha256_hex(&receipt_bytes),
        "source_envelope_bytes": input_bytes.len(),
        "source_envelope_sha256": sha256_hex(&input_bytes),
        "schema": "zenodex/zrpf_source_opened_spot_value_leaf_v6_proof_report/v2",
        "source_proof_sha256": sha256_hex(&source_proof_bytes),
        "statement_hash": hex::encode(expected_statement.statement_hash().as_bytes()),
        "status": "source_opened_spot_value_leaf_v6_succinct_receipt_verified",
        "v6_image_id": Digest::from(ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID).to_string(),
        "verified_program_manifest_root": hex::encode(verified.verified_program_manifest_root().as_bytes()),
        "nonclaims": [
            "the V6 receipt alone grants no ledger, settlement, release, or production authority",
            "this report proves one bounded singleton Spot transition and no maximum-fanout throughput claim",
        ],
    });
    println!(
        "{}",
        serde_json::to_string(&report).map_err(|error| format!("report encode: {error}"))?
    );
    Ok(())
}

fn parse_options(args: impl IntoIterator<Item = String>) -> Result<Options, String> {
    let args = args.into_iter().collect::<Vec<_>>();
    if args.len() != 10
        || args[0] != "--receipt-out"
        || args[2] != "--source-envelope-out"
        || args[4] != "--source-request"
        || args[6] != "--source-proof"
        || args[8] != "--adapter-receipt"
        || [1, 3, 5, 7, 9]
            .iter()
            .any(|index| args[*index].is_empty() || args[*index].starts_with("--"))
    {
        return Err(usage().to_owned());
    }
    Ok(Options {
        receipt_out: PathBuf::from(&args[1]),
        source_envelope_out: PathBuf::from(&args[3]),
        source_request: PathBuf::from(&args[5]),
        source_proof: PathBuf::from(&args[7]),
        adapter_receipt: PathBuf::from(&args[9]),
    })
}

fn usage() -> &'static str {
    "usage: prove_spot_value_leaf_v6 --receipt-out <v6.receipt.json> --source-envelope-out <v6.input.bin> --source-request <source.request.json> --source-proof <source.receipt.json> --adapter-receipt <adapter.receipt.json>"
}

fn validate_v6_method() -> Result<(), String> {
    if ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF.is_empty()
        || ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID
            .iter()
            .all(|word| *word == 0)
    {
        return Err("V6 source-opened Spot method is a placeholder".to_owned());
    }
    let computed = compute_image_id(ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ELF)
        .map_err(|error| format!("compute V6 image ID: {error}"))?;
    if computed != Digest::from(ZENODEX_ZRPF_RISC0_SPOT_VALUE_LEAF_V6_ID) {
        return Err("V6 source-opened Spot method image ID mismatch".to_owned());
    }
    Ok(())
}

fn load_exact_source(
    request_path: &Path,
    proof_path: &Path,
) -> Result<(SpotRecursiveLeafInputV1, Receipt, Vec<u8>), String> {
    let request_bytes = read_bounded_regular_file(request_path, "source request")?;
    let request: SourceRequestArtifact = serde_json::from_slice(&request_bytes)
        .map_err(|error| format!("source request JSON: {error}"))?;
    let proof_bytes = read_bounded_regular_file(proof_path, "source proof")?;
    let proof: SourceProofArtifact = serde_json::from_slice(&proof_bytes)
        .map_err(|error| format!("source proof JSON: {error}"))?;
    if request.schema != "tau_state_proof_request"
        || request.schema_version != 1
        || request.proof_type != PROOF_TYPE_RECURSIVE_SPOT_LEAF
        || request.receipt_kind != "succinct"
        || proof.schema != "tau_state_proof"
        || proof.schema_version != 1
        || proof.proof_type != PROOF_TYPE_RECURSIVE_SPOT_LEAF
        || request.state_hash != proof.state_hash
    {
        return Err("source request/proof envelope mismatch".to_owned());
    }
    let receipt_bytes = BASE64_STANDARD
        .decode(&proof.proof)
        .map_err(|error| format!("source receipt base64: {error}"))?;
    if receipt_bytes.is_empty()
        || receipt_bytes.len() > MAX_ARTIFACT_BYTES
        || BASE64_STANDARD.encode(&receipt_bytes) != proof.proof
    {
        return Err("source receipt base64 is noncanonical or oversized".to_owned());
    }
    let receipt: Receipt = serde_json::from_slice(&receipt_bytes)
        .map_err(|error| format!("source receipt JSON: {error}"))?;
    if canonical_receipt_bytes(&receipt)? != receipt_bytes {
        return Err("source receipt JSON is not canonical".to_owned());
    }
    require_succinct(&receipt, "source")?;
    let policy = source_policy_v2(SourceKindV2::Spot)
        .map_err(|error| format!("current source policy rejected: {error}"))?;
    receipt
        .verify(policy.image_id)
        .map_err(|error| format!("source receipt verification failed: {error}"))?;
    let expected_summary =
        compose_spot_recursive_leaf_summary_v1(request.spot_recursive_leaf_input.clone())
            .map_err(|error| format!("source request recomposition failed: {error:?}"))?;
    let expected_journal = postcard::to_allocvec(&expected_summary)
        .map_err(|error| format!("source summary encode: {error}"))?;
    if receipt.journal.bytes != expected_journal {
        return Err("source receipt journal differs from exact request recomposition".to_owned());
    }
    let decoded: RecursiveEffectSummaryV1 = postcard::from_bytes(&receipt.journal.bytes)
        .map_err(|error| format!("source summary decode: {error}"))?;
    if decoded != expected_summary {
        return Err("source summary exact decode mismatch".to_owned());
    }
    Ok((request.spot_recursive_leaf_input, receipt, proof_bytes))
}

fn load_exact_adapter(
    receipt_bytes: &[u8],
    source: &Receipt,
) -> Result<VerifiedNodeReceiptV3, String> {
    let expected = project_policy_bound_v2_journal(
        SourceKindV2::Spot,
        &source.journal.bytes,
        ASSIGNED_LEAF_ORDINAL,
        PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
    )
    .map_err(|error| format!("adapter host projection rejected: {error}"))?;
    VerifiedNodeReceiptV3::verify_exact_succinct_bytes(
        receipt_bytes,
        PINNED_SOURCE_OPENED_V6_ADAPTER_IMAGE_ID,
        &expected.journal,
    )
    .map_err(|error| format!("exact adapter receipt verification failed: {error}"))
}

#[cfg(test)]
mod tests {
    use super::{parse_options, usage};

    #[test]
    fn cli_is_exact_and_ordered() {
        let valid = [
            "--receipt-out",
            "v6.json",
            "--source-envelope-out",
            "v6.input.bin",
            "--source-request",
            "source.request.json",
            "--source-proof",
            "source.receipt.json",
            "--adapter-receipt",
            "adapter.json",
        ]
        .map(str::to_owned);
        assert!(parse_options(valid).is_ok());
        assert_eq!(
            parse_options(["--receipt-out".to_owned()]).unwrap_err(),
            usage()
        );
    }
}
