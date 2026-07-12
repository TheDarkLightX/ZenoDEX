use std::{fs, path::PathBuf};

use super::artifact_io::persist_receipt;
use super::report::guest_artifact_report;
use super::source::load_verified_source;
use super::{
    load_exact_adapter, parse_options, receipt_reject_json, Mode, RETAINED_ADAPTER_RECEIPT_SHA256,
    RETAINED_SEMANTIC_OPENING,
};
use zenodex_zrpf_risc0_verifier::{
    VerifiedNodeReceiptErrorV3, VerifiedSpotValueLeafReceiptErrorV4,
};

fn args(values: &[&str]) -> Vec<String> {
    values.iter().map(|value| (*value).to_owned()).collect()
}

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..")
}

#[test]
fn exact_prove_and_verify_cli_forms_are_distinct() -> Result<(), String> {
    let prove = parse_options(args(&[
        "--receipt-out",
        "value.json",
        "--source-proof",
        "source.json",
        "--adapter-receipt",
        "adapter.json",
    ]))?;
    assert_eq!(prove.mode, Mode::Prove);

    let verify = parse_options(args(&[
        "--verify-receipt",
        "value.json",
        "--source-proof",
        "source.json",
        "--adapter-receipt",
        "adapter.json",
    ]))?;
    assert_eq!(verify.mode, Mode::Verify);
    Ok(())
}

#[test]
fn cli_rejects_reordering_unknown_flags_and_extra_inputs() {
    for candidate in [
        args(&[
            "--receipt-out",
            "value.json",
            "--adapter-receipt",
            "adapter.json",
            "--source-proof",
            "source.json",
        ]),
        args(&[
            "--unknown",
            "value.json",
            "--source-proof",
            "source.json",
            "--adapter-receipt",
            "adapter.json",
        ]),
        args(&[
            "--receipt-out",
            "value.json",
            "--source-proof",
            "source.json",
            "--adapter-receipt",
            "adapter.json",
            "extra",
        ]),
    ] {
        assert!(parse_options(candidate).is_err());
    }
}

#[test]
fn retained_source_and_adapter_cross_the_exact_host_boundaries() -> Result<(), String> {
    let root = repository_root();
    let source = load_verified_source(
        &root.join(
            "evidence/zrpf-semantic-epoch-v1-local-proof-v1/source-inputs/source-ordinal-0.receipt.json",
        ),
    )?;
    let adapter = load_exact_adapter(
        &root.join(
            "evidence/zrpf-semantic-epoch-v1-local-proof-v1/receipts/adapter-ordinal-0.receipt.json",
        ),
        &source,
    )?;
    assert!(source.asset_rows.is_empty());
    assert_eq!(
        source.summary.pre_state_root,
        source.summary.post_state_root
    );
    assert_eq!(adapter.semantic_opening, RETAINED_SEMANTIC_OPENING);
    assert_eq!(adapter.receipt_sha256, RETAINED_ADAPTER_RECEIPT_SHA256);
    Ok(())
}

#[test]
fn receipt_persistence_is_create_new_and_rereads_exact_bytes() -> Result<(), String> {
    let scratch = std::env::temp_dir().join(format!(
        "zenodex-zrpf-v4-leaf-persist-test-{}",
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&scratch);
    fs::create_dir(&scratch).map_err(|error| format!("create scratch: {error}"))?;
    let path = scratch.join("receipt.json");
    persist_receipt(&path, b"verified-receipt-bytes")?;
    assert_eq!(
        fs::read(&path).map_err(|error| format!("read receipt: {error}"))?,
        b"verified-receipt-bytes"
    );
    assert!(persist_receipt(&path, b"replacement").is_err());
    fs::remove_dir_all(&scratch).map_err(|error| format!("remove scratch: {error}"))?;
    Ok(())
}

#[test]
fn verifier_only_report_cannot_emit_observed_guest_artifact_facts() {
    let report = guest_artifact_report(false);
    assert_eq!(report["loaded_and_matched"], false);
    assert!(report["observed_elf_bytes"].is_null());
    assert!(report["observed_elf_sha256"].is_null());
    assert_eq!(report["source_to_elf_provenance_verified"], false);
}

#[test]
fn prove_report_emits_observed_guest_artifact_facts_after_exact_match() {
    let report = guest_artifact_report(true);
    assert_eq!(report["loaded_and_matched"], true);
    assert_eq!(report["observed_elf_bytes"], 499_312);
    assert_eq!(
        report["observed_elf_sha256"],
        "195f1cd4bd4b6b4ddc4765d9ab33664834e64d58ee6c468dd0b254ea0012fa6e"
    );
    assert_eq!(report["source_to_elf_provenance_verified"], false);
}

#[test]
fn receipt_reject_report_preserves_exact_typed_verifier_boundary() -> Result<(), String> {
    let raw = receipt_reject_json(
        "ab",
        VerifiedSpotValueLeafReceiptErrorV4::ReceiptArtifact(
            VerifiedNodeReceiptErrorV3::ReceiptVerificationFailed,
        ),
    );
    let report: serde_json::Value =
        serde_json::from_str(&raw).map_err(|error| format!("decode reject report: {error}"))?;
    assert_eq!(report["candidate_accepted"], false);
    assert_eq!(
        report["reject"]["boundary"],
        "ExactSpotValueLeafReceiptV4::verify_exact_succinct_bytes"
    );
    assert_eq!(report["reject"]["code"], "receipt_verification_failed");
    assert_eq!(
        report["reject"]["outer_code"],
        "spot_value_leaf_receipt_artifact_rejected"
    );
    assert_eq!(
        report["reject"]["variant"],
        "ReceiptArtifact(ReceiptVerificationFailed)"
    );
    Ok(())
}
