use tau_state_proof_risc0_shared::{
    recursive_cross_shard_messages_root_v1, recursive_receipt_ids_root_v1,
    RecursiveEffectSummaryV1, RECURSIVE_SPOT_LEAF_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, AggregateNodeInputV3, CommitmentV3, NodeJournalV3, ProfileIdV3,
    ProjectedChildDescriptorV3, SemanticEpochErrorV1, TaskIdV3, V1AdapterSemanticLeafOpeningV1,
    MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_JOURNAL_BYTES_V3,
};
use zenodex_zrpf_risc0_aggregate_shared::{
    recompose_expected_structural_aggregate_v1, StructuralAggregateInputV1,
    StructuralAggregatePolicyV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    recompose_profile_bound_semantic_leaves_v1, DisclosedStructuralLevelOneV1,
    DisclosedV1AdapterLeafV1, SemanticRecompositionErrorV1, SemanticRecompositionInputV1,
    SemanticRecompositionPolicyV1, MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1,
};
use zenodex_zrpf_risc0_shared::{
    program_id_from_risc0_words_v3, project_policy_bound_v1_journal, SourceKindV1,
    PINNED_SPOT_LEAF_IMAGE_ID_V1,
};

const ADAPTER_IMAGE_ID: [u32; 8] = [31, 32, 33, 34, 35, 36, 37, 38];
const LEVEL_ONE_IMAGE_ID: [u32; 8] = [41, 42, 43, 44, 45, 46, 47, 48];
const WRONG_LEVEL_ONE_IMAGE_ID: [u32; 8] = [51, 52, 53, 54, 55, 56, 57, 58];

fn root(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn summary(seed: u8) -> RecursiveEffectSummaryV1 {
    let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
    let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
    RecursiveEffectSummaryV1 {
        summary_version: 1,
        lane_id: format!("spot-semantic-lane-{seed}"),
        lane_kind: "spot".to_owned(),
        chain_id: "zenodex-semantic-shared-test".to_owned(),
        epoch_id: 37,
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

#[derive(Clone)]
struct LeafFixture {
    journal: NodeJournalV3,
    disclosure: DisclosedV1AdapterLeafV1,
}

fn leaf(seed: u8, ordinal: u64) -> LeafFixture {
    let source_bytes = postcard::to_allocvec(&summary(seed)).unwrap();
    let projection = project_policy_bound_v1_journal(
        SourceKindV1::Spot,
        &source_bytes,
        ordinal,
        ADAPTER_IMAGE_ID,
    )
    .unwrap();
    let opening =
        V1AdapterSemanticLeafOpeningV1::new(projection.source_binding.canonical_hash().unwrap());
    let journal = projection.journal;
    let disclosure =
        DisclosedV1AdapterLeafV1::new(encode_node_journal_v3(&journal).unwrap(), opening).unwrap();
    LeafFixture {
        journal,
        disclosure,
    }
}

fn level_one(children: &[LeafFixture], image_id: [u32; 8]) -> NodeJournalV3 {
    recompose_expected_structural_aggregate_v1(
        &StructuralAggregateInputV1 {
            expected_self_image_id: image_id,
            child_journal_bytes: children
                .iter()
                .map(|child| encode_node_journal_v3(&child.journal).unwrap())
                .collect(),
        },
        StructuralAggregatePolicyV1::level_one_adapter_children(ADAPTER_IMAGE_ID),
    )
    .unwrap()
    .journal
}

fn subtree(children: &[LeafFixture]) -> DisclosedStructuralLevelOneV1 {
    let journal = level_one(children, LEVEL_ONE_IMAGE_ID);
    DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&journal).unwrap(),
        children
            .iter()
            .map(|child| child.disclosure.clone())
            .collect(),
    )
    .unwrap()
}

fn input(subtrees: Vec<DisclosedStructuralLevelOneV1>) -> SemanticRecompositionInputV1 {
    SemanticRecompositionInputV1::new(subtrees).unwrap()
}

fn policy() -> SemanticRecompositionPolicyV1 {
    SemanticRecompositionPolicyV1::new(ADAPTER_IMAGE_ID, LEVEL_ONE_IMAGE_ID).unwrap()
}

#[test]
fn exact_level_one_recomposition_returns_canonical_profile_bound_proposals() {
    let left = [leaf(1, 0), leaf(2, 1)];
    let right = [leaf(3, 2), leaf(4, 3)];
    let result = recompose_profile_bound_semantic_leaves_v1(
        &input(vec![subtree(&left), subtree(&right)]),
        policy(),
    )
    .unwrap();

    assert_eq!(result.len(), 4);
    for (ordinal, semantic_leaf) in result.iter().enumerate() {
        assert_eq!(semantic_leaf.partition().start(), ordinal as u64);
        assert_eq!(
            semantic_leaf.partition().end_exclusive(),
            ordinal as u64 + 1
        );
        assert_eq!(semantic_leaf.operation_count(), 1);
    }
    assert!(result
        .windows(2)
        .all(|pair| pair[0].semantic_source_id() != pair[1].semantic_source_id()));
}

#[test]
fn missing_leaf_rejects_exact_level_one_recomposition() {
    let children = [leaf(1, 0), leaf(2, 1)];
    let original = level_one(&children, LEVEL_ONE_IMAGE_ID);
    let disclosure = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&original).unwrap(),
        vec![children[0].disclosure.clone()],
    )
    .unwrap();

    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![disclosure]), policy()),
        Err(SemanticRecompositionErrorV1::LevelOneJournalMismatch { subtree: 0 })
    );
}

#[test]
fn substituted_leaf_rejects_exact_level_one_recomposition() {
    let original_children = [leaf(1, 0), leaf(2, 1)];
    let original = level_one(&original_children, LEVEL_ONE_IMAGE_ID);
    let replacement = leaf(9, 1);
    let disclosure = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&original).unwrap(),
        vec![
            original_children[0].disclosure.clone(),
            replacement.disclosure,
        ],
    )
    .unwrap();

    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![disclosure]), policy()),
        Err(SemanticRecompositionErrorV1::LevelOneJournalMismatch { subtree: 0 })
    );
}

#[test]
fn reordered_leaf_disclosures_reject_instead_of_being_silently_sorted() {
    let children = [leaf(1, 0), leaf(2, 1)];
    let original = level_one(&children, LEVEL_ONE_IMAGE_ID);
    let disclosure = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&original).unwrap(),
        vec![
            children[1].disclosure.clone(),
            children[0].disclosure.clone(),
        ],
    )
    .unwrap();

    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![disclosure]), policy()),
        Err(SemanticRecompositionErrorV1::NonCanonicalChildOrder {
            subtree: 0,
            child: 1,
        })
    );
}

#[test]
fn semantic_opening_must_match_the_adapter_commitments_and_statement() {
    let child = leaf(1, 0);
    let l1 = level_one(core::slice::from_ref(&child), LEVEL_ONE_IMAGE_ID);
    let wrong_opening = DisclosedV1AdapterLeafV1::new(
        encode_node_journal_v3(&child.journal).unwrap(),
        V1AdapterSemanticLeafOpeningV1::new(CommitmentV3::new(root(199)).unwrap()),
    )
    .unwrap();
    let disclosure = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&l1).unwrap(),
        vec![wrong_opening],
    )
    .unwrap();

    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![disclosure]), policy()),
        Err(SemanticRecompositionErrorV1::SemanticProjection {
            subtree: 0,
            child: 0,
            error: SemanticEpochErrorV1::V1AdapterProvenanceMismatch,
        })
    );
}

#[test]
fn noncanonical_parent_and_child_bytes_reject_before_recomposition() {
    let child = leaf(1, 0);
    let l1 = level_one(core::slice::from_ref(&child), LEVEL_ONE_IMAGE_ID);

    let mut malformed_parent = encode_node_journal_v3(&l1).unwrap();
    malformed_parent.push(0);
    let parent_disclosure =
        DisclosedStructuralLevelOneV1::new(malformed_parent, vec![child.disclosure.clone()])
            .unwrap();
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![parent_disclosure]), policy(),),
        Err(SemanticRecompositionErrorV1::LevelOneJournalDecode { subtree: 0 })
    );

    let mut malformed_child = child.disclosure.journal_bytes().to_vec();
    malformed_child.push(0);
    let child_disclosure =
        DisclosedV1AdapterLeafV1::new(malformed_child, child.disclosure.semantic_opening())
            .unwrap();
    let subtree_disclosure = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&l1).unwrap(),
        vec![child_disclosure],
    )
    .unwrap();
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![subtree_disclosure]), policy(),),
        Err(SemanticRecompositionErrorV1::AdapterJournalDecode {
            subtree: 0,
            child: 0,
        })
    );
}

#[test]
fn wrong_level_one_shape_program_and_profile_reject_before_semantic_projection() {
    let children = [leaf(1, 0), leaf(2, 1)];
    let leaf_in_parent_position = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&children[0].journal).unwrap(),
        vec![children[0].disclosure.clone()],
    )
    .unwrap();
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![leaf_in_parent_position]), policy(),),
        Err(SemanticRecompositionErrorV1::LevelOneAggregateRequired { subtree: 0 })
    );

    let wrong_program = level_one(&children, WRONG_LEVEL_ONE_IMAGE_ID);
    let wrong_program_disclosure = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&wrong_program).unwrap(),
        children
            .iter()
            .map(|child| child.disclosure.clone())
            .collect(),
    )
    .unwrap();
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(
            &input(vec![wrong_program_disclosure]),
            policy(),
        ),
        Err(SemanticRecompositionErrorV1::LevelOneProgramMismatch { subtree: 0 })
    );

    let wrong_profile = level_one_with_wrong_profile(&children);
    let wrong_profile_disclosure = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&wrong_profile).unwrap(),
        children
            .iter()
            .map(|child| child.disclosure.clone())
            .collect(),
    )
    .unwrap();
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(
            &input(vec![wrong_profile_disclosure]),
            policy(),
        ),
        Err(SemanticRecompositionErrorV1::LevelOneProfileMismatch { subtree: 0 })
    );
}

#[test]
fn duplicate_source_hidden_in_separate_subtrees_rejects_globally() {
    let left = [leaf(1, 0), leaf(2, 1)];
    let right = [leaf(1, 2), leaf(4, 3)];

    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(
            &input(vec![subtree(&left), subtree(&right)]),
            policy(),
        ),
        Err(SemanticRecompositionErrorV1::DuplicateSemanticSource)
    );
}

#[test]
fn subtree_order_and_global_partition_origin_are_fail_closed() {
    let left = [leaf(1, 0), leaf(2, 1)];
    let right = [leaf(3, 2), leaf(4, 3)];
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(
            &input(vec![subtree(&right), subtree(&left)]),
            policy(),
        ),
        Err(SemanticRecompositionErrorV1::PartitionMustStartAtZero)
    );

    let shifted = [leaf(1, 1), leaf(2, 2)];
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![subtree(&shifted)]), policy(),),
        Err(SemanticRecompositionErrorV1::PartitionMustStartAtZero)
    );
}

#[test]
fn zero_image_policy_and_empty_disclosures_cannot_be_constructed() {
    assert_eq!(
        SemanticRecompositionPolicyV1::new([0; 8], LEVEL_ONE_IMAGE_ID),
        Err(SemanticRecompositionErrorV1::ZeroAdapterImageId)
    );
    assert_eq!(
        SemanticRecompositionPolicyV1::new(ADAPTER_IMAGE_ID, [0; 8]),
        Err(SemanticRecompositionErrorV1::ZeroLevelOneImageId)
    );
    assert_eq!(
        SemanticRecompositionInputV1::new(vec![]),
        Err(SemanticRecompositionErrorV1::EmptyLevelOneNodes)
    );
}

#[test]
fn disclosure_constructors_enforce_every_count_and_byte_bound() {
    let valid = leaf(1, 0);
    let opening = valid.disclosure.semantic_opening();
    assert_eq!(
        DisclosedV1AdapterLeafV1::new(vec![], opening),
        Err(SemanticRecompositionErrorV1::InvalidAdapterJournalLength { length: 0 })
    );
    assert_eq!(
        DisclosedV1AdapterLeafV1::new(vec![0; MAX_NODE_JOURNAL_BYTES_V3 + 1], opening),
        Err(SemanticRecompositionErrorV1::InvalidAdapterJournalLength {
            length: MAX_NODE_JOURNAL_BYTES_V3 + 1,
        })
    );

    let l1_bytes = encode_node_journal_v3(&level_one(
        core::slice::from_ref(&valid),
        LEVEL_ONE_IMAGE_ID,
    ))
    .unwrap();
    assert_eq!(
        DisclosedStructuralLevelOneV1::new(l1_bytes.clone(), vec![]),
        Err(SemanticRecompositionErrorV1::EmptyAdapterLeaves)
    );
    assert_eq!(
        DisclosedStructuralLevelOneV1::new(
            l1_bytes,
            vec![valid.disclosure.clone(); MAX_IMMEDIATE_CHILDREN_V3 + 1],
        ),
        Err(SemanticRecompositionErrorV1::TooManyAdapterLeaves {
            actual: MAX_IMMEDIATE_CHILDREN_V3 + 1,
            maximum: MAX_IMMEDIATE_CHILDREN_V3,
        })
    );

    let valid_subtree = subtree(core::slice::from_ref(&valid));
    assert_eq!(
        SemanticRecompositionInputV1::new(vec![
            valid_subtree;
            MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1 + 1
        ]),
        Err(SemanticRecompositionErrorV1::TooManyLevelOneNodes {
            actual: MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1 + 1,
            maximum: MAX_SEMANTIC_LEVEL_ONE_DISCLOSURES_V1,
        })
    );
}

#[test]
fn child_and_subtree_partition_gaps_reject_before_semantic_projection() {
    let canonical_children = [leaf(1, 0), leaf(2, 1)];
    let original_l1 = level_one(&canonical_children, LEVEL_ONE_IMAGE_ID);
    let gapped_child = leaf(3, 2);
    let child_gap = DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&original_l1).unwrap(),
        vec![
            canonical_children[0].disclosure.clone(),
            gapped_child.disclosure,
        ],
    )
    .unwrap();
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(&input(vec![child_gap]), policy()),
        Err(SemanticRecompositionErrorV1::NonContiguousChildren {
            subtree: 0,
            child: 1,
        })
    );

    let left = [leaf(1, 0), leaf(2, 1)];
    let shifted_right = [leaf(3, 3), leaf(4, 4)];
    assert_eq!(
        recompose_profile_bound_semantic_leaves_v1(
            &input(vec![subtree(&left), subtree(&shifted_right)]),
            policy(),
        ),
        Err(SemanticRecompositionErrorV1::NonContiguousSubtrees { subtree: 1 })
    );
}

fn level_one_with_wrong_profile(children: &[LeafFixture]) -> NodeJournalV3 {
    let child_descriptors = children
        .iter()
        .enumerate()
        .map(|(index, child)| {
            ProjectedChildDescriptorV3::project_canonical_journal(
                CommitmentV3::new(root(100 + index as u8)).unwrap(),
                &encode_node_journal_v3(&child.journal).unwrap(),
            )
            .unwrap()
        })
        .collect();
    let reference = level_one(children, LEVEL_ONE_IMAGE_ID);
    NodeJournalV3::new_aggregate(AggregateNodeInputV3 {
        children: child_descriptors,
        task_id: TaskIdV3::new(root(150)).unwrap(),
        count_unit_id: children[0].journal.count_unit_id(),
        scope: children[0].journal.scope().clone(),
        proof_profile_id: ProfileIdV3::new(root(151)).unwrap(),
        actual_program_id: program_id_from_risc0_words_v3(LEVEL_ONE_IMAGE_ID).unwrap(),
        node_statement_hash: CommitmentV3::new(root(152)).unwrap(),
        program_manifest_root: CommitmentV3::new(root(153)).unwrap(),
        commitments: reference.commitments().clone(),
    })
    .unwrap()
}
