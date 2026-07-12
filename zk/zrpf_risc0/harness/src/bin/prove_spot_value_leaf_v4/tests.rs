use std::{fs, path::PathBuf};

use super::artifact_io::persist_receipt;
use super::source::load_verified_source;
use super::{
    load_exact_adapter, parse_options, Mode, RETAINED_ADAPTER_RECEIPT_SHA256,
    RETAINED_SEMANTIC_OPENING,
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
