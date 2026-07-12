use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v4, encode_value_aggregate_proposal_v5, NodeScopeV3,
};
use zenodex_zrpf_risc0_value_aggregate_l2_policy::{
    pinned_value_aggregate_level_one_identity_v5, PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
};
use zenodex_zrpf_risc0_value_aggregate_root_policy::{
    pinned_value_aggregate_level_two_root_identity_v5, PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    recompose_expected_value_aggregate_level_one_v5, ValueAggregateLevelOneInputV5,
    ValueAggregateRecompositionErrorV5, ValueAggregateRecompositionPolicyV5,
};

use super::{
    artifact_io::{persist_new_receipt, read_bounded_receipt_file},
    cli::{parse_options, Mode},
    expected_level_one_receipt_identity, expected_level_two_root_receipt_identity,
    load_authenticated_level_one_children, recompose_exact_level_two, validate_method,
    verify_existing, LevelTwoMaterialError,
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
        "root.receipt.json".to_owned(),
    ];
    for index in 0..child_count {
        args.push("--child".to_owned());
        args.push(format!("l1-child-{index}.receipt.json"));
    }
    args
}

fn isolated_directory(label: &str) -> PathBuf {
    let ordinal = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "zrpf-v5-l2-harness-{}-{label}-{ordinal}",
        std::process::id()
    ));
    fs::create_dir(&path).expect("create isolated test directory");
    path
}

fn level_one_proposal_bytes(start: u64, statement_offset: u64, scope: NodeScopeV3) -> Vec<u8> {
    let leaf_identity = aggregate_support::identity(100, 70, 71);
    let child_bytes = [start, start + 1]
        .into_iter()
        .map(|ordinal| {
            encode_node_journal_v4(&aggregate_support::leaf_journal(
                ordinal,
                ordinal + statement_offset,
                aggregate_support::indexed(60, ordinal),
                aggregate_support::indexed(60, ordinal + 1),
                scope.clone(),
                leaf_identity,
            ))
            .expect("encode V4 leaf")
        })
        .collect();
    let input = ValueAggregateLevelOneInputV5::new(child_bytes).expect("L1 input");
    let policy = aggregate_support::policy(scope, vec![leaf_identity, leaf_identity]);
    let proposal =
        recompose_expected_value_aggregate_level_one_v5(&input, &policy).expect("L1 proposal");
    encode_value_aggregate_proposal_v5(&proposal).expect("encode L1 proposal")
}

fn level_two_policy(scope: NodeScopeV3, child_count: usize) -> ValueAggregateRecompositionPolicyV5 {
    let identity = pinned_value_aggregate_level_one_identity_v5().expect("pinned L1 identity");
    ValueAggregateRecompositionPolicyV5::new(scope, vec![identity; child_count]).expect("L2 policy")
}

#[test]
fn strict_cli_accepts_only_pinned_policy_modes_and_one_to_eight_children() {
    let prove = parse_options(args("prove", 1)).expect("prove options");
    assert_eq!(prove.mode, Mode::Prove);
    assert_eq!(prove.child_paths.len(), 1);

    let verify = parse_options(args("verify-existing", 8)).expect("verify options");
    assert_eq!(verify.mode, Mode::VerifyExisting);
    assert_eq!(verify.child_paths.len(), 8);

    assert!(parse_options(args("prove", 0)).is_err());
    assert!(parse_options(args("prove", 9)).is_err());
    let mut unknown = args("prove", 1);
    unknown[3] = "--children".to_owned();
    assert!(parse_options(unknown).is_err());
    let mut injected_policy = args("prove", 1);
    injected_policy.splice(3..3, ["--expected-profile".to_owned(), "00".repeat(32)]);
    assert!(parse_options(injected_policy).is_err());
}

#[test]
fn receipt_identities_are_derived_only_from_the_two_pinned_policy_crates() {
    let child = expected_level_one_receipt_identity().expect("L1 receipt identity");
    let pinned_child = pinned_value_aggregate_level_one_identity_v5().expect("pinned L1 identity");
    assert_eq!(child.aggregate_level().get(), 1);
    assert_eq!(child.proof_profile_id(), pinned_child.expected_profile_id());
    assert_eq!(
        child.program_manifest_root(),
        pinned_child.expected_manifest_root()
    );

    let root = expected_level_two_root_receipt_identity().expect("L2 root identity");
    let pinned_root =
        pinned_value_aggregate_level_two_root_identity_v5().expect("pinned L2 identity");
    assert_eq!(root.aggregate_level().get(), 2);
    assert_eq!(root.proof_profile_id(), pinned_root.expected_profile_id());
    assert_eq!(
        root.program_manifest_root(),
        pinned_root.expected_manifest_root()
    );
}

#[test]
fn exact_l2_recomposition_accepts_valid_l1_children_and_rejects_missing_children() {
    let scope = aggregate_support::scope();
    let children = vec![
        level_one_proposal_bytes(0, 0, scope.clone()),
        level_one_proposal_bytes(2, 0, scope.clone()),
    ];
    let policy = level_two_policy(scope.clone(), children.len());
    let material = recompose_exact_level_two(children, &policy).expect("valid L2 material");
    assert_eq!(material.expected_proposal.aggregate_level(), 2);
    assert!(!material.guest_input_bytes.is_empty());

    assert_eq!(
        recompose_exact_level_two(Vec::new(), &policy).err(),
        Some(LevelTwoMaterialError::Recomposition(
            ValueAggregateRecompositionErrorV5::InvalidChildCount {
                actual: 0,
                maximum: 8,
            }
        ))
    );
}

#[test]
fn substituted_scope_mutated_bytes_and_duplicate_l1_children_reject() {
    let scope = aggregate_support::scope();
    let foreign_scope = aggregate_support::scope_with_application(9);
    let first = level_one_proposal_bytes(0, 0, scope.clone());
    let foreign = level_one_proposal_bytes(2, 0, foreign_scope);
    let policy = level_two_policy(scope.clone(), 2);
    assert_eq!(
        recompose_exact_level_two(vec![first.clone(), foreign], &policy).err(),
        Some(LevelTwoMaterialError::Recomposition(
            ValueAggregateRecompositionErrorV5::ChildScopeMismatch(1)
        ))
    );

    let mut mutated = first.clone();
    mutated.push(0);
    assert_eq!(
        recompose_exact_level_two(vec![mutated], &level_two_policy(scope.clone(), 1)).err(),
        Some(LevelTwoMaterialError::Recomposition(
            ValueAggregateRecompositionErrorV5::ChildV5ProposalDecode(0)
        ))
    );

    assert_eq!(
        recompose_exact_level_two(vec![first.clone(), first], &policy).err(),
        Some(LevelTwoMaterialError::Recomposition(
            ValueAggregateRecompositionErrorV5::DuplicateChildClaim
        ))
    );
}

#[test]
fn valid_l1_statement_substitution_changes_the_exact_expected_root() {
    let scope = aggregate_support::scope();
    let baseline = level_one_proposal_bytes(0, 0, scope.clone());
    let substituted = level_one_proposal_bytes(0, 99, scope.clone());
    let policy = level_two_policy(scope, 1);
    let baseline = recompose_exact_level_two(vec![baseline], &policy).expect("baseline root");
    let substituted =
        recompose_exact_level_two(vec![substituted], &policy).expect("substituted root");

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
fn child_and_existing_root_artifacts_must_cross_sealed_verifiers() {
    let scope = aggregate_support::scope();
    let child_bytes = level_one_proposal_bytes(0, 0, scope.clone());
    let material = recompose_exact_level_two(vec![child_bytes], &level_two_policy(scope, 1))
        .expect("valid root material");
    let directory = isolated_directory("sealed-artifacts");
    let invalid_child = directory.join("invalid-l1.json");
    let invalid_root = directory.join("invalid-l2.json");
    fs::write(&invalid_child, b"{}").expect("write invalid L1 receipt");
    fs::write(&invalid_root, b"{}").expect("write invalid L2 receipt");
    assert!(load_authenticated_level_one_children(&[invalid_child]).is_err());

    let mut options = parse_options(args("verify-existing", 1)).expect("verify options");
    options.receipt_path = invalid_root;
    let error = verify_existing(options, 1, material).expect_err("unverified root must reject");
    assert!(error.starts_with("sealed V5 L2 root verification failed:"));

    fs::remove_dir_all(directory).expect("remove isolated test directory");
}

#[test]
fn method_policy_binding_and_receipt_file_shell_fail_closed() {
    assert_eq!(
        validate_method(
            "placeholder",
            &[],
            [0; 8],
            PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5
        ),
        Err("placeholder method is a placeholder".to_owned())
    );
    assert_eq!(
        validate_method("substituted", &[1], [1; 8], [2; 8]),
        Err("substituted generated image ID differs from governed policy".to_owned())
    );
    assert_ne!(
        PINNED_VALUE_AGGREGATE_L1_IMAGE_ID_V5,
        PINNED_VALUE_AGGREGATE_L2_IMAGE_ID_V5
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

#[test]
fn report_source_keeps_every_authority_flag_false() {
    let report = include_str!("report.rs");
    for field in [
        "data_availability_verified: false",
        "ledger_admission_authority: false",
        "settlement_authority: false",
        "release_authority: false",
        "production_authority: false",
    ] {
        assert!(report.contains(field));
    }
}
