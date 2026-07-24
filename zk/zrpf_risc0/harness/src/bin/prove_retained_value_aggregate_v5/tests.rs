use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

use risc0_zkvm::Digest;
use serde_json::Value;
use sha2::Digest as _;

use super::{
    artifact_io::{persist_bundle, read_fixture_once, remove_fixture},
    cli::{parse_options, Mode},
    expected_level_one_identity, expected_level_two_identity, governed_programs_from_record,
    load_authenticated_child,
    report::{decode_receipt_bundle, encode_receipt_bundle_fixture_for_test},
    require_retained_host_feature_closure, require_sdk_ipc_prover, GOVERNED_BUILD_RECORD_BYTES,
    GOVERNED_BUILD_RECORD_SHA256, PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
    PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
};

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

struct ScratchDirectory(PathBuf);

impl ScratchDirectory {
    fn new(label: &str) -> Result<Self, String> {
        let ordinal = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "zrpf-retained-v5-{}-{label}-{ordinal}",
            std::process::id()
        ));
        fs::create_dir(&path).map_err(|error| format!("create scratch directory: {error}"))?;
        Ok(Self(path))
    }

    fn path(&self) -> &Path {
        &self.0
    }
}

impl Drop for ScratchDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn arguments(mode: &str) -> Vec<String> {
    let mut values = vec![
        mode.to_owned(),
        "--level-one-program".to_owned(),
        "l1.bin".to_owned(),
        "--level-two-program".to_owned(),
        "l2.bin".to_owned(),
        "--child-receipt".to_owned(),
        "child.json".to_owned(),
    ];
    if mode == "prove" {
        values.extend(["--bundle-out".to_owned(), "bundle.json".to_owned()]);
    } else if mode == "verify-existing" {
        values.extend(["--bundle".to_owned(), "bundle.json".to_owned()]);
    }
    values
}

fn repository_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../..")
}

#[test]
fn governed_build_record_binds_exact_programs_and_policies() -> Result<(), String> {
    let governed = governed_programs_from_record(GOVERNED_BUILD_RECORD_BYTES)?;
    assert_eq!(
        hex::encode(sha2::Sha256::digest(GOVERNED_BUILD_RECORD_BYTES)),
        GOVERNED_BUILD_RECORD_SHA256
    );
    assert_eq!(governed.child.size_bytes, 500_104);
    assert_eq!(
        hex::encode(governed.child.sha256),
        "1801e835035c7fd82356e8fe425679e991894dce45a7fb45a37e28349dc72abe"
    );
    assert_eq!(
        Digest::from(governed.child.image_id).to_string(),
        "d81406cf27ff2f776aed9e20fee3128b859387e4475d517c75f25e8e564f6a70"
    );
    assert_eq!(governed.level_one.size_bytes, 531_764);
    assert_eq!(
        governed.level_one.image_id,
        PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5
    );
    assert_eq!(governed.level_two.size_bytes, 446_372);
    assert_eq!(
        governed.level_two.image_id,
        PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5
    );
    assert_eq!(expected_level_one_identity()?.aggregate_level().get(), 1);
    assert_eq!(expected_level_two_identity()?.aggregate_level().get(), 2);
    Ok(())
}

#[test]
fn any_build_record_mutation_rejects_before_parsing() {
    let mut mutated = GOVERNED_BUILD_RECORD_BYTES.to_vec();
    mutated[0] ^= 1;
    assert_eq!(
        governed_programs_from_record(&mutated).err().as_deref(),
        Some("embedded V5 build record differs from governed SHA-256")
    );
}

#[test]
fn cli_is_strict_and_separates_preflight_from_persistence() -> Result<(), String> {
    let preflight = parse_options(arguments("preflight"))?;
    assert_eq!(preflight.mode, Mode::Preflight);
    assert!(preflight.bundle_input.is_none());
    assert!(preflight.bundle_output.is_none());

    let prove = parse_options(arguments("prove"))?;
    assert_eq!(prove.mode, Mode::Prove);
    assert_eq!(prove.bundle_output, Some(PathBuf::from("bundle.json")));
    assert!(prove.bundle_input.is_none());

    let verify = parse_options(arguments("verify-existing"))?;
    assert_eq!(verify.mode, Mode::VerifyExisting);
    assert_eq!(verify.bundle_input, Some(PathBuf::from("bundle.json")));
    assert!(verify.bundle_output.is_none());

    let mut duplicate = arguments("prove");
    duplicate.extend(["--bundle-out".to_owned(), "second.json".to_owned()]);
    assert!(parse_options(duplicate).is_err());
    let mut unknown = arguments("preflight");
    unknown.extend(["--profile".to_owned(), "candidate".to_owned()]);
    assert!(parse_options(unknown).is_err());
    assert!(parse_options(arguments("unknown")).is_err());
    let mut wrong_bundle_direction = arguments("verify-existing");
    wrong_bundle_direction[7] = "--bundle-out".to_owned();
    assert!(parse_options(wrong_bundle_direction).is_err());
    Ok(())
}

fn structurally_valid_bundle_bytes() -> Result<Vec<u8>, String> {
    let receipts = repository_root().join("evidence/zrpf-v4-spot-value-leaf-v1/receipts");
    let level_one = fs::read(receipts.join("spot-value-leaf-v4.receipt.json"))
        .map_err(|error| format!("read positive receipt fixture: {error}"))?;
    let level_two = fs::read(receipts.join("spot-value-leaf-v4.seal-word-1-xor-lsb.receipt.json"))
        .map_err(|error| format!("read mutation receipt fixture: {error}"))?;
    encode_receipt_bundle_fixture_for_test(&level_one, &level_two)
}

#[test]
fn existing_bundle_decoder_is_exact_bounded_and_fail_closed() -> Result<(), String> {
    let canonical = structurally_valid_bundle_bytes()?;
    let decoded = decode_receipt_bundle(&canonical)?;
    assert!(!decoded.level_one_receipt_bytes().is_empty());
    assert!(!decoded.level_two_receipt_bytes().is_empty());
    assert_ne!(
        decoded.level_one_receipt_bytes(),
        decoded.level_two_receipt_bytes()
    );

    let mut trailing = canonical.clone();
    trailing.push(b'\n');
    assert!(decode_receipt_bundle(&trailing).is_err());

    let mut promoted: Value = serde_json::from_slice(&canonical)
        .map_err(|error| format!("decode bundle fixture for mutation: {error}"))?;
    promoted["claims"]["production_authority"] = Value::Bool(true);
    assert!(decode_receipt_bundle(
        &serde_json::to_vec(&promoted)
            .map_err(|error| format!("encode promoted fixture: {error}"))?
    )
    .is_err());

    let mut unknown: Value = serde_json::from_slice(&canonical)
        .map_err(|error| format!("decode bundle fixture for unknown field: {error}"))?;
    unknown["unexpected"] = Value::Bool(false);
    assert!(decode_receipt_bundle(
        &serde_json::to_vec(&unknown)
            .map_err(|error| format!("encode unknown fixture: {error}"))?
    )
    .is_err());

    let mut hash_drift: Value = serde_json::from_slice(&canonical)
        .map_err(|error| format!("decode bundle fixture for hash drift: {error}"))?;
    hash_drift["level_one_receipt_sha256"] = Value::String("00".repeat(32));
    assert!(decode_receipt_bundle(
        &serde_json::to_vec(&hash_drift)
            .map_err(|error| format!("encode hash-drift fixture: {error}"))?
    )
    .is_err());
    Ok(())
}

#[test]
fn only_the_sdk_ipc_prover_name_is_admissible() {
    assert!(require_sdk_ipc_prover("ipc", "test").is_ok());
    assert!(require_sdk_ipc_prover("bonsai", "test").is_err());
    assert!(require_sdk_ipc_prover("local", "test").is_err());
    assert!(require_sdk_ipc_prover("", "test").is_err());
}

#[test]
fn runtime_feature_guard_matches_the_compiled_method_feature_closure() {
    assert!(cfg!(feature = "retained-value-aggregate-v5-harness"));
    let method_feature_enabled =
        cfg!(feature = "legacy-methods") || cfg!(feature = "spot-v6-methods");
    assert_eq!(
        require_retained_host_feature_closure().is_ok(),
        !method_feature_enabled
    );
}

#[test]
fn bounded_reads_reject_empty_oversized_and_symlink_inputs() -> Result<(), String> {
    let scratch = ScratchDirectory::new("reads")?;
    let valid = scratch.path().join("valid.bin");
    fs::write(&valid, b"program").map_err(|error| format!("write valid fixture: {error}"))?;
    assert_eq!(read_fixture_once(&valid, 7)?, b"program");
    assert!(read_fixture_once(&valid, 6).is_err());

    let empty = scratch.path().join("empty.bin");
    fs::write(&empty, []).map_err(|error| format!("write empty fixture: {error}"))?;
    assert!(read_fixture_once(&empty, 1).is_err());

    let link = scratch.path().join("link.bin");
    std::os::unix::fs::symlink(&valid, &link)
        .map_err(|error| format!("create fixture symlink: {error}"))?;
    assert!(read_fixture_once(&link, 7).is_err());
    remove_fixture(&valid);
    Ok(())
}

#[test]
fn bundle_persistence_is_create_new_and_rereads_exact_bytes() -> Result<(), String> {
    let scratch = ScratchDirectory::new("persist")?;
    let output = scratch.path().join("bundle.json");
    let persisted = persist_bundle(&output, b"verified bundle")?;
    assert_eq!(persisted.byte_length(), 15);
    assert_eq!(
        hex::encode(persisted.sha256()),
        "e1725ec7ac2147649eea270d65a2ca5fdb2f6efaf85d4225dbafdb1480aa232d"
    );
    assert_eq!(
        fs::read(&output).map_err(|error| format!("read persisted bundle: {error}"))?,
        b"verified bundle"
    );
    assert!(persist_bundle(&output, b"replacement").is_err());
    assert_eq!(
        fs::read(&output).map_err(|error| format!("reread persisted bundle: {error}"))?,
        b"verified bundle"
    );
    Ok(())
}

#[test]
fn positive_bundle_claims_require_the_sealed_proof_pair_type() {
    let report_source = include_str!("report.rs");
    assert!(report_source.contains("proved: &ProvedReceipts"));
    assert!(!report_source.contains("level_one_receipt: &[u8]"));
    assert!(report_source.contains("persisted_bundle_sha256"));
    assert!(report_source.contains("bundle.sha256() != persisted.sha256()"));
    assert!(report_source.contains("existing_bundle_stable_read_verified"));
    assert!(report_source.contains("V5 receipt bundle claims mismatch"));
}

#[test]
fn current_retained_v4_receipt_rejects_the_governed_child_image() -> Result<(), String> {
    let governed = governed_programs_from_record(GOVERNED_BUILD_RECORD_BYTES)?;
    let path = repository_root()
        .join("evidence/zrpf-v4-spot-value-leaf-v1/receipts/spot-value-leaf-v4.receipt.json");
    let error = load_authenticated_child(&path, &governed.child)
        .err()
        .ok_or_else(|| "the incompatible retained V4 receipt was accepted".to_owned())?;
    assert!(error.starts_with("V4 child receipt authentication failed:"));
    Ok(())
}

#[test]
fn source_contract_uses_retained_program_bytes_without_methods_feature() {
    let source = include_str!("../prove_retained_value_aggregate_v5.rs");
    assert!(!source.contains("zenodex_zrpf_risc0_methods"));
    assert!(source.contains("cannot be compiled with method-build features enabled"));
    assert_eq!(source.matches("BoundProgram::load_once").count(), 2);
    assert!(source.contains("prove_with_opts(environment, program.bytes()"));
    assert!(source.contains("require_sdk_ipc_prover(&prover.get_name(), label)"));
    assert!(source.contains("require_retained_host_feature_closure()"));
    assert!(source.contains("RISC0_DEV_MODE"));
    assert!(source.contains("RISC0_PROVER"));
    assert!(source.contains("BONSAI_API_URL"));
    assert!(source.contains("BONSAI_API_KEY"));
    assert!(source.contains("VerifiedValueAggregateReceiptV5::verify_exact_succinct_bytes"));
    assert!(source.contains("verify_existing_and_report"));
    assert!(source.contains("verified V5 receipt bundle differs from canonical re-encoding"));
}
