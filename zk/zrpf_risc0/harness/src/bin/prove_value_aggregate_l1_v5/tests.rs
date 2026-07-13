use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use zenodex_zrpf_protocol_v3::encode_node_journal_v4;
use zenodex_zrpf_risc0_value_aggregate_shared::ValueAggregateRecompositionErrorV5;

use super::{
    artifact_io::{persist_new_receipt, read_bounded_receipt_file},
    cli::{parse_options, Mode},
    recompose_exact_level_one, validate_governed_method, validate_method, verify_existing,
    LevelOneMaterialError,
};

#[path = "../../../../value_aggregate_shared/tests/support/mod.rs"]
mod aggregate_support;

static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

fn args(mode: &str, child_count: usize) -> Vec<String> {
    let receipt_flag = if mode == "prove" {
        "--receipt-out"
    } else {
        "--receipt"
    };
    let mut args = vec![
        mode.to_owned(),
        receipt_flag.to_owned(),
        "aggregate.receipt.json".to_owned(),
    ];
    for index in 0..child_count {
        args.push("--child".to_owned());
        args.push(format!("child-{index}.receipt.json"));
    }
    args
}

fn isolated_directory(label: &str) -> PathBuf {
    let ordinal = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "zrpf-v5-harness-{}-{label}-{ordinal}",
        std::process::id()
    ));
    fs::create_dir(&path).expect("create isolated test directory");
    path
}

#[test]
fn strict_cli_accepts_only_mode_output_and_one_to_eight_children() {
    let prove = parse_options(args("prove", 1)).expect("prove options");
    assert_eq!(prove.mode, Mode::Prove);
    assert_eq!(prove.child_paths.len(), 1);

    let verify = parse_options(args("verify-existing", 8)).expect("verify options");
    assert_eq!(verify.mode, Mode::VerifyExisting);
    assert_eq!(verify.child_paths.len(), 8);

    assert!(parse_options(args("prove", 0)).is_err());
    assert!(parse_options(args("prove", 9)).is_err());
    let mut unknown = args("prove", 1);
    unknown[3] = "--profile".to_owned();
    assert!(parse_options(unknown).is_err());
    let mut caller_identity = args("prove", 1);
    caller_identity.splice(
        3..3,
        ["--expected-proof-profile-id".to_owned(), "00".repeat(32)],
    );
    assert!(parse_options(caller_identity).is_err());
}

#[test]
fn exact_host_recomposition_accepts_valid_children_and_rejects_missing_children() {
    let identity = aggregate_support::identity(100, 70, 71);
    let scope = aggregate_support::scope();
    let child = aggregate_support::leaf_bytes(
        0,
        aggregate_support::indexed(60, 0),
        aggregate_support::indexed(60, 1),
        scope.clone(),
        identity,
    );
    let policy = aggregate_support::policy(scope.clone(), vec![identity]);
    let material = recompose_exact_level_one(vec![child], &policy).expect("valid child");
    assert_eq!(material.expected_proposal.aggregate_level(), 1);
    assert!(!material.guest_input_bytes.is_empty());

    assert_eq!(
        recompose_exact_level_one(Vec::new(), &policy).err(),
        Some(LevelOneMaterialError::Recomposition(
            ValueAggregateRecompositionErrorV5::InvalidChildCount {
                actual: 0,
                maximum: 8,
            }
        ))
    );
}

#[test]
fn substituted_child_identity_and_mutated_journal_bytes_reject() {
    let expected_identity = aggregate_support::identity(100, 70, 71);
    let substituted_identity = aggregate_support::identity(200, 70, 71);
    let scope = aggregate_support::scope();
    let substituted = aggregate_support::leaf_bytes(
        0,
        aggregate_support::indexed(60, 0),
        aggregate_support::indexed(60, 1),
        scope.clone(),
        substituted_identity,
    );
    let policy = aggregate_support::policy(scope.clone(), vec![expected_identity]);
    assert_eq!(
        recompose_exact_level_one(vec![substituted], &policy).err(),
        Some(LevelOneMaterialError::Recomposition(
            ValueAggregateRecompositionErrorV5::ChildProgramMismatch(0)
        ))
    );

    let mut mutated = aggregate_support::leaf_bytes(
        0,
        aggregate_support::indexed(60, 0),
        aggregate_support::indexed(60, 1),
        scope,
        expected_identity,
    );
    mutated.push(0);
    assert_eq!(
        recompose_exact_level_one(vec![mutated], &policy).err(),
        Some(LevelOneMaterialError::Recomposition(
            ValueAggregateRecompositionErrorV5::ChildV4JournalDecode(0)
        ))
    );
}

#[test]
fn exact_valid_child_statement_substitution_changes_expected_parent() {
    let identity = aggregate_support::identity(100, 70, 71);
    let scope = aggregate_support::scope();
    let baseline = aggregate_support::leaf_journal(
        0,
        0,
        aggregate_support::indexed(60, 0),
        aggregate_support::indexed(60, 1),
        scope.clone(),
        identity,
    );
    let substituted = aggregate_support::leaf_journal(
        0,
        99,
        aggregate_support::indexed(60, 0),
        aggregate_support::indexed(60, 1),
        scope.clone(),
        identity,
    );
    let policy = aggregate_support::policy(scope, vec![identity]);
    let baseline = recompose_exact_level_one(
        vec![encode_node_journal_v4(&baseline).expect("baseline journal")],
        &policy,
    )
    .expect("baseline parent");
    let substituted = recompose_exact_level_one(
        vec![encode_node_journal_v4(&substituted).expect("substituted journal")],
        &policy,
    )
    .expect("substituted parent");

    assert_ne!(
        baseline.expected_proposal.proposal_commitment(),
        substituted.expected_proposal.proposal_commitment()
    );
    assert_ne!(
        baseline.expected_proposal.children()[0].claim_binding(),
        substituted.expected_proposal.children()[0].claim_binding()
    );
}

#[test]
fn verify_existing_rejects_an_unverified_parent_artifact() {
    let identity = aggregate_support::identity(100, 70, 71);
    let scope = aggregate_support::scope();
    let child = aggregate_support::leaf_bytes(
        0,
        aggregate_support::indexed(60, 0),
        aggregate_support::indexed(60, 1),
        scope.clone(),
        identity,
    );
    let policy = aggregate_support::policy(scope, vec![identity]);
    let material = recompose_exact_level_one(vec![child], &policy).expect("valid material");
    let directory = isolated_directory("verify-existing");
    let artifact = directory.join("invalid-parent.json");
    fs::write(&artifact, b"{}").expect("write invalid parent artifact");
    let mut options = parse_options(args("verify-existing", 1)).expect("verify options");
    options.receipt_path = artifact;

    let error = verify_existing(options, 1, material).expect_err("unverified parent must reject");
    assert!(error.starts_with("sealed V5 aggregate verification failed:"));

    fs::remove_dir_all(directory).expect("remove isolated test directory");
}

#[test]
fn method_validation_and_receipt_file_shell_fail_closed() {
    assert_eq!(
        validate_method("placeholder", &[], [0; 8]),
        Err("placeholder method is a placeholder".to_owned())
    );
    assert_eq!(
        validate_governed_method("governed", &[1], [1; 8], [2; 8]),
        Err("governed generated image ID differs from governed policy".to_owned())
    );

    let directory = isolated_directory("files");
    let empty = directory.join("empty.json");
    fs::write(&empty, []).expect("write empty file");
    assert!(read_bounded_receipt_file(&empty).is_err());

    let output = directory.join("output.json");
    persist_new_receipt(&output, b"{}").expect("persist first output");
    assert!(persist_new_receipt(&output, b"replacement").is_err());
    assert_eq!(fs::read(&output).expect("read output"), b"{}");

    #[cfg(unix)]
    {
        let target = directory.join("target.json");
        let link = directory.join("link.json");
        fs::write(&target, b"{}").expect("write symlink target");
        std::os::unix::fs::symlink(&target, &link).expect("create symlink");
        assert!(read_bounded_receipt_file(&link).is_err());
    }

    fs::remove_dir_all(directory).expect("remove isolated test directory");
}
