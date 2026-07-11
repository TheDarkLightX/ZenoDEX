use std::collections::BTreeSet;

use tau_state_proof_risc0_shared::{
    recursive_cross_shard_messages_root_v1, recursive_receipt_ids_root_v1,
    RecursiveEffectSummaryV1, RECURSIVE_SPOT_LEAF_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, LeafNodeInputV3, NodeJournalV3, NodeKindV3, NodeLevelV3, ProfileIdV3,
    ZrpfErrorV3, MAX_NODE_JOURNAL_BYTES_V3,
};
use zenodex_zrpf_risc0_aggregate_shared::{
    compose_structural_aggregate_after_receipt_verification_v1,
    decode_exact_structural_aggregate_input_v1, encode_structural_aggregate_input_v1,
    recompose_expected_structural_aggregate_v1, StructuralAggregateErrorV1,
    StructuralAggregateInputErrorV1, StructuralAggregateInputV1, StructuralAggregatePolicyV1,
    MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1, STRUCTURAL_AGGREGATE_INPUT_SCHEMA_VERSION_V1,
};
use zenodex_zrpf_risc0_shared::{
    project_policy_bound_v1_journal, SourceKindV1, PINNED_SPOT_LEAF_IMAGE_ID_V1,
};

const ADAPTER_IMAGE_ID: [u32; 8] = [
    3_045_257_841,
    281_444_177,
    3_435_235_465,
    2_147_567_259,
    867_057_786,
    252_644_892,
    735_118_677,
    1_951_735_332,
];
const AGGREGATE_IMAGE_ID: [u32; 8] = [9, 10, 11, 12, 13, 14, 15, 16];
const ROOT_IMAGE_ID: [u32; 8] = [17, 18, 19, 20, 21, 22, 23, 24];

fn root(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn summary(seed: u8) -> RecursiveEffectSummaryV1 {
    let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
    let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
    RecursiveEffectSummaryV1 {
        summary_version: 1,
        lane_id: format!("spot-lane-{seed}"),
        lane_kind: "spot".to_owned(),
        chain_id: "zenodex-structural-test".to_owned(),
        epoch_id: 29,
        proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1.to_owned(),
        risc0_image_id: PINNED_SPOT_LEAF_IMAGE_ID_V1,
        statement_hash: root(seed),
        pre_state_root: root(seed.wrapping_add(1)),
        post_state_root: root(seed.wrapping_add(2)),
        tx_root: root(seed.wrapping_add(3)),
        evidence_root: root(seed.wrapping_add(4)),
        receipt_root: root(seed.wrapping_add(5)),
        accepted_receipts_root: empty_receipts,
        rejected_receipts_root: empty_receipts,
        asset_delta_root: root(seed.wrapping_add(6)),
        cross_shard_outbox_root: empty_messages,
        cross_shard_inbox_root: empty_messages,
        write_set_root: root(seed.wrapping_add(7)),
        public_policy_hash: root(80),
        feature_suite_hash: root(81),
        dependency_lock_hash: root(82),
        toolchain_lock_hash: root(83),
    }
}

fn leaf(seed: u8, ordinal: u64) -> NodeJournalV3 {
    let source = postcard::to_allocvec(&summary(seed)).unwrap();
    project_policy_bound_v1_journal(SourceKindV1::Spot, &source, ordinal, ADAPTER_IMAGE_ID)
        .unwrap()
        .journal
}

fn input(children: &[NodeJournalV3]) -> StructuralAggregateInputV1 {
    input_with_self(children, AGGREGATE_IMAGE_ID)
}

fn input_with_self(
    children: &[NodeJournalV3],
    expected_self_image_id: [u32; 8],
) -> StructuralAggregateInputV1 {
    StructuralAggregateInputV1 {
        expected_self_image_id,
        child_journal_bytes: children
            .iter()
            .map(|journal| encode_node_journal_v3(journal).unwrap())
            .collect(),
    }
}

fn policy() -> StructuralAggregatePolicyV1 {
    StructuralAggregatePolicyV1::level_one_adapter_children(ADAPTER_IMAGE_ID)
}

#[test]
fn manual_input_codec_is_exact_bounded_and_canonical() {
    let value = input(&[leaf(1, 0), leaf(2, 1)]);
    let bytes = encode_structural_aggregate_input_v1(&value).unwrap();
    assert_eq!(
        decode_exact_structural_aggregate_input_v1(&bytes).unwrap(),
        value
    );
    assert!(bytes.len() <= MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1);

    let mut trailing = bytes.clone();
    trailing.push(0);
    assert_eq!(
        decode_exact_structural_aggregate_input_v1(&trailing),
        Err(StructuralAggregateInputErrorV1::TrailingBytes)
    );
    let mut stale = bytes.clone();
    stale[..2].copy_from_slice(&(STRUCTURAL_AGGREGATE_INPUT_SCHEMA_VERSION_V1 + 1).to_be_bytes());
    assert_eq!(
        decode_exact_structural_aggregate_input_v1(&stale),
        Err(StructuralAggregateInputErrorV1::InvalidSchema(2))
    );
    let mut zero_child_count = bytes;
    zero_child_count[34] = 0;
    assert_eq!(
        decode_exact_structural_aggregate_input_v1(&zero_child_count),
        Err(StructuralAggregateInputErrorV1::InvalidChildCount(0))
    );
    assert!(matches!(
        decode_exact_structural_aggregate_input_v1(&vec![
            0;
            MAX_STRUCTURAL_AGGREGATE_INPUT_BYTES_V1
                + 1
        ]),
        Err(StructuralAggregateInputErrorV1::InputTooLarge { .. })
    ));
}

#[test]
fn two_verified_adapter_journals_compose_a_structural_level_one_node() {
    let projection = compose_structural_aggregate_after_receipt_verification_v1(
        &input(&[leaf(1, 0), leaf(2, 1)]),
        policy(),
    )
    .unwrap();
    let journal = projection.journal;
    assert_eq!(journal.node_kind(), NodeKindV3::Aggregate);
    assert_eq!(journal.node_level(), NodeLevelV3::new(1).unwrap());
    assert_eq!(journal.immediate_child_count(), 2);
    assert_eq!(journal.leaf_count(), 2);
    assert_eq!(journal.operation_count(), 2);
    assert_eq!(journal.subtree_node_count(), 3);
    assert_eq!(journal.partition().start(), 0);
    assert_eq!(journal.partition().end_exclusive(), 2);
    assert_eq!(projection.child_claim_bindings.len(), 2);
    assert_ne!(
        projection.child_claim_bindings[0],
        projection.child_claim_bindings[1]
    );

    let commitments = serde_json::to_value(journal.commitments()).unwrap();
    let fields = commitments.as_object().unwrap();
    assert_eq!(fields.len(), 23);
    assert_eq!(
        fields
            .keys()
            .map(String::as_str)
            .collect::<BTreeSet<_>>()
            .len(),
        23
    );
    for value in fields.values() {
        assert_ne!(value, &serde_json::to_value([0u8; 32]).unwrap());
    }
}

#[test]
fn pure_expected_recomposition_matches_the_verified_caller_wrapper() {
    let input = input(&[leaf(1, 0), leaf(2, 1)]);
    let expected = recompose_expected_structural_aggregate_v1(&input, policy()).unwrap();
    let verified_caller =
        compose_structural_aggregate_after_receipt_verification_v1(&input, policy()).unwrap();

    assert_eq!(expected, verified_caller);
}

#[test]
fn child_input_order_does_not_change_the_canonical_parent() {
    let left = leaf(1, 0);
    let right = leaf(2, 1);
    let forward = compose_structural_aggregate_after_receipt_verification_v1(
        &input(&[left.clone(), right.clone()]),
        policy(),
    )
    .unwrap();
    let reverse = compose_structural_aggregate_after_receipt_verification_v1(
        &input(&[right, left]),
        policy(),
    )
    .unwrap();
    assert_eq!(forward, reverse);
}

#[test]
fn two_level_one_nodes_compose_a_common_journal_level_two_root() {
    let left = compose_structural_aggregate_after_receipt_verification_v1(
        &input(&[leaf(1, 0), leaf(2, 1)]),
        policy(),
    )
    .unwrap()
    .journal;
    let right = compose_structural_aggregate_after_receipt_verification_v1(
        &input(&[leaf(3, 2), leaf(4, 3)]),
        policy(),
    )
    .unwrap()
    .journal;
    let level_two_policy =
        StructuralAggregatePolicyV1::level_two_level_one_children(AGGREGATE_IMAGE_ID);
    let root = compose_structural_aggregate_after_receipt_verification_v1(
        &input_with_self(&[right, left], ROOT_IMAGE_ID),
        level_two_policy,
    )
    .unwrap()
    .journal;

    assert_eq!(root.node_kind(), NodeKindV3::Aggregate);
    assert_eq!(root.node_level(), NodeLevelV3::new(2).unwrap());
    assert_eq!(root.immediate_child_count(), 2);
    assert_eq!(root.leaf_count(), 4);
    assert_eq!(root.operation_count(), 4);
    assert_eq!(root.subtree_node_count(), 7);
    assert_eq!(root.partition().start(), 0);
    assert_eq!(root.partition().end_exclusive(), 4);
}

#[test]
fn wrong_child_program_and_manifest_reject_before_parent_construction() {
    let wrong_program = {
        let source = postcard::to_allocvec(&summary(1)).unwrap();
        project_policy_bound_v1_journal(SourceKindV1::Spot, &source, 0, [99; 8])
            .unwrap()
            .journal
    };
    assert_eq!(
        compose_structural_aggregate_after_receipt_verification_v1(
            &input(&[wrong_program]),
            policy(),
        ),
        Err(StructuralAggregateErrorV1::ChildProgramMismatch(0))
    );

    let original = leaf(1, 0);
    let wrong_manifest = NodeJournalV3::new_leaf(LeafNodeInputV3 {
        task_id: original.task_id(),
        partition: original.partition(),
        operation_count: original.operation_count(),
        count_unit_id: original.count_unit_id(),
        scope: original.scope().clone(),
        proof_profile_id: original.proof_profile_id(),
        actual_program_id: original.actual_program_id(),
        node_statement_hash: original.node_statement_hash(),
        program_manifest_root: zenodex_zrpf_protocol_v3::CommitmentV3::new([199; 32]).unwrap(),
        commitments: original.commitments().clone(),
    })
    .unwrap();
    assert_eq!(
        compose_structural_aggregate_after_receipt_verification_v1(
            &input(&[wrong_manifest]),
            policy(),
        ),
        Err(StructuralAggregateErrorV1::ChildManifestMismatch(0))
    );
}

#[test]
fn wrong_profile_level_duplicate_and_partition_gap_reject() {
    let original = leaf(1, 0);
    let wrong_profile = NodeJournalV3::new_leaf(LeafNodeInputV3 {
        task_id: original.task_id(),
        partition: original.partition(),
        operation_count: original.operation_count(),
        count_unit_id: original.count_unit_id(),
        scope: original.scope().clone(),
        proof_profile_id: ProfileIdV3::new([177; 32]).unwrap(),
        actual_program_id: original.actual_program_id(),
        node_statement_hash: original.node_statement_hash(),
        program_manifest_root: original.program_manifest_root(),
        commitments: original.commitments().clone(),
    })
    .unwrap();
    assert_eq!(
        compose_structural_aggregate_after_receipt_verification_v1(
            &input(&[wrong_profile]),
            policy(),
        ),
        Err(StructuralAggregateErrorV1::ChildProfileMismatch(0))
    );

    let duplicate = leaf(2, 1);
    assert!(matches!(
        compose_structural_aggregate_after_receipt_verification_v1(
            &input(&[duplicate.clone(), duplicate]),
            policy(),
        ),
        Err(StructuralAggregateErrorV1::Protocol(
            ZrpfErrorV3::DuplicateChildClaim
        ))
    ));
    assert!(matches!(
        compose_structural_aggregate_after_receipt_verification_v1(
            &input(&[leaf(1, 0), leaf(2, 2)]),
            policy(),
        ),
        Err(StructuralAggregateErrorV1::Protocol(
            ZrpfErrorV3::NonContiguousPartitions
        ))
    ));

    let level_one = compose_structural_aggregate_after_receipt_verification_v1(
        &input(&[leaf(1, 0), leaf(2, 1)]),
        policy(),
    )
    .unwrap()
    .journal;
    assert_eq!(
        compose_structural_aggregate_after_receipt_verification_v1(&input(&[level_one]), policy(),),
        Err(StructuralAggregateErrorV1::ChildProgramMismatch(0))
    );
}

#[test]
fn codec_rejects_oversized_child_before_allocation() {
    let mut bytes = Vec::new();
    bytes.extend_from_slice(&STRUCTURAL_AGGREGATE_INPUT_SCHEMA_VERSION_V1.to_be_bytes());
    for word in AGGREGATE_IMAGE_ID {
        bytes.extend_from_slice(&word.to_be_bytes());
    }
    bytes.push(1);
    bytes.extend_from_slice(
        &u16::try_from(MAX_NODE_JOURNAL_BYTES_V3 + 1)
            .unwrap()
            .to_be_bytes(),
    );
    assert_eq!(
        decode_exact_structural_aggregate_input_v1(&bytes),
        Err(StructuralAggregateInputErrorV1::InvalidChildJournalLength {
            index: 0,
            length: MAX_NODE_JOURNAL_BYTES_V3 + 1,
        })
    );
}
