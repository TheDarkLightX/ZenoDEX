use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    decode_exact_node_journal_v3, derive_verifier_id_v3, encode_node_journal_v3,
    AggregateNodeInputV3, ApplicationIdV3, CommitmentV3, DomainIdV3, LeafNodeInputV3,
    NodeCommitmentsInputV3, NodeCommitmentsV3, NodeJournalV3, NodeKindV3, NodeLevelV3,
    NodeScopeInputV3, NodeScopeV3, PartitionV3, ProfileIdV3, ProgramIdV3,
    ProjectedChildDescriptorV3, TaskIdV3, ZrpfErrorV3, MAX_IMMEDIATE_CHILDREN_V3,
    MAX_LEAF_COUNT_V3, MAX_NODE_JOURNAL_BYTES_V3, MAX_OPERATIONS_PER_LEAF_V3,
    MAX_OPERATIONS_PER_ROOT_V3, MAX_SUBTREE_NODE_COUNT_V3,
};

const TEST_PROFILE_SEED: u8 = 240;

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed; 32]).unwrap()
}

fn program(seed: u8) -> ProgramIdV3 {
    ProgramIdV3::new([seed; 32]).unwrap()
}

fn profile(seed: u8) -> ProfileIdV3 {
    ProfileIdV3::new([seed; 32]).unwrap()
}

fn task(seed: u8) -> TaskIdV3 {
    TaskIdV3::new([seed; 32]).unwrap()
}

fn count_unit() -> CommitmentV3 {
    commitment(231)
}

fn scope() -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([225; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([226; 32]).unwrap(),
        epoch_start: 10,
        epoch_end: 10,
        public_policy_hash: commitment(227),
        feature_suite_hash: commitment(228),
        dependency_lock_hash: commitment(229),
        toolchain_lock_hash: commitment(230),
    })
    .unwrap()
}

fn commitments(seed: u8) -> NodeCommitmentsV3 {
    let root = |index: u8| {
        let mut bytes = [seed; 32];
        bytes[0] = index;
        CommitmentV3::new(bytes).unwrap()
    };
    NodeCommitmentsV3::new(NodeCommitmentsInputV3 {
        pre_state_vector_root: root(1),
        post_state_vector_root: root(2),
        input_root: root(3),
        transaction_root: root(4),
        evidence_root: root(5),
        provenance_root: root(6),
        receipt_root: root(7),
        accepted_receipts_root: root(8),
        rejected_receipts_root: root(9),
        effect_root: root(10),
        write_set_root: root(11),
        asset_delta_root: root(12),
        cross_lane_outbox_root: root(13),
        cross_lane_inbox_root: root(14),
        cross_lane_message_ids_root: root(15),
        conflict_schedule_hash: root(16),
        data_availability_root: root(17),
        data_availability_certificate_root: root(18),
        carry_queue_pre_root: root(19),
        carry_queue_post_root: root(20),
        task_set_root: root(21),
        semantic_source_set_root: root(22),
        partition_plan_root: root(23),
    })
}

fn leaf(start: u64, end_exclusive: u64, seed: u8, operation_count: u64) -> NodeJournalV3 {
    leaf_with_profile(
        start,
        end_exclusive,
        seed,
        operation_count,
        TEST_PROFILE_SEED,
    )
}

fn leaf_with_profile(
    start: u64,
    end_exclusive: u64,
    seed: u8,
    operation_count: u64,
    profile_seed: u8,
) -> NodeJournalV3 {
    NodeJournalV3::new_leaf(LeafNodeInputV3 {
        task_id: task(seed),
        partition: PartitionV3::new(start, end_exclusive).unwrap(),
        operation_count,
        count_unit_id: count_unit(),
        scope: scope(),
        proof_profile_id: profile(profile_seed),
        actual_program_id: program(seed.wrapping_add(1)),
        node_statement_hash: commitment(seed.wrapping_add(3)),
        program_manifest_root: commitment(seed.wrapping_add(4)),
        commitments: commitments(seed.wrapping_add(30)),
    })
    .unwrap()
}

fn descriptor(journal: &NodeJournalV3, claim_seed: u8) -> ProjectedChildDescriptorV3 {
    let journal_bytes = encode_node_journal_v3(journal).unwrap();
    ProjectedChildDescriptorV3::project_canonical_journal(commitment(claim_seed), &journal_bytes)
        .unwrap()
}

fn aggregate(
    children: Vec<ProjectedChildDescriptorV3>,
    seed: u8,
) -> Result<NodeJournalV3, ZrpfErrorV3> {
    NodeJournalV3::new_aggregate(AggregateNodeInputV3 {
        children,
        task_id: task(seed),
        count_unit_id: count_unit(),
        scope: scope(),
        proof_profile_id: profile(TEST_PROFILE_SEED),
        actual_program_id: program(seed.wrapping_add(1)),
        node_statement_hash: commitment(seed.wrapping_add(3)),
        program_manifest_root: commitment(seed.wrapping_add(4)),
        commitments: commitments(seed.wrapping_add(30)),
    })
}

#[test]
fn valid_leaf_is_a_closed_nonempty_level_zero_node() {
    let node = leaf(10, 11, 1, 7);

    assert_eq!(node.node_kind(), NodeKindV3::Leaf);
    assert_eq!(node.node_level(), NodeLevelV3::LEAF);
    assert_eq!(node.partition(), PartitionV3::new(10, 11).unwrap());
    assert_eq!(node.immediate_child_count(), 0);
    assert_eq!(node.leaf_count(), 1);
    assert_eq!(node.operation_count(), 7);
    assert_eq!(node.count_unit_id(), count_unit());
    assert_eq!(node.subtree_node_count(), 1);
    assert_ne!(node.child_claims_root().into_bytes(), [0; 32]);
    assert_eq!(
        decode_exact_node_journal_v3(&encode_node_journal_v3(&node).unwrap()).unwrap(),
        node
    );
}

#[test]
fn valid_multi_subtree_aggregate_derives_level_partitions_and_counts() {
    let a = leaf(0, 1, 1, 2);
    let b = leaf(1, 2, 11, 3);
    let c = leaf(2, 3, 21, 5);
    let d = leaf(3, 4, 31, 7);
    let left = aggregate(vec![descriptor(&a, 81), descriptor(&b, 82)], 41).unwrap();
    let right = aggregate(vec![descriptor(&c, 83), descriptor(&d, 84)], 51).unwrap();

    let root = aggregate(vec![descriptor(&right, 86), descriptor(&left, 85)], 61).unwrap();

    assert_eq!(root.node_kind(), NodeKindV3::Aggregate);
    assert_eq!(root.node_level().get(), 2);
    assert_eq!(root.partition(), PartitionV3::new(0, 4).unwrap());
    assert_eq!(root.immediate_child_count(), 2);
    assert_eq!(root.leaf_count(), 4);
    assert_eq!(root.operation_count(), 17);
    assert_eq!(root.subtree_node_count(), 7);
    assert_ne!(root.child_claims_root(), root.child_journals_root());
    assert_ne!(root.child_programs_root(), root.child_verifiers_root());
}

#[test]
fn fully_saturated_eight_by_eight_tree_hits_the_declared_bounds() {
    let mut subtrees = Vec::new();
    for subtree_index in 0..MAX_IMMEDIATE_CHILDREN_V3 {
        let mut leaves = Vec::new();
        for child_index in 0..MAX_IMMEDIATE_CHILDREN_V3 {
            let partition = subtree_index * MAX_IMMEDIATE_CHILDREN_V3 + child_index;
            let node = leaf(
                partition as u64,
                partition as u64 + 1,
                partition as u8 + 1,
                1,
            );
            leaves.push(descriptor(&node, partition as u8 + 100));
        }
        let subtree = aggregate(leaves, subtree_index as u8 + 170).unwrap();
        subtrees.push(descriptor(&subtree, subtree_index as u8 + 200));
    }

    let root = aggregate(subtrees, 220).unwrap();

    assert_eq!(root.node_level().get(), 2);
    assert_eq!(
        root.immediate_child_count(),
        MAX_IMMEDIATE_CHILDREN_V3 as u8
    );
    assert_eq!(root.leaf_count(), MAX_LEAF_COUNT_V3);
    assert_eq!(root.operation_count(), MAX_LEAF_COUNT_V3);
    assert!(root.operation_count() <= MAX_OPERATIONS_PER_ROOT_V3);
    assert_eq!(root.subtree_node_count(), MAX_SUBTREE_NODE_COUNT_V3);
    assert_eq!(root.partition(), PartitionV3::new(0, 64).unwrap());
}

#[test]
fn every_permutation_has_the_same_canonical_parent() {
    let a = descriptor(&leaf(0, 1, 1, 1), 90);
    let b = descriptor(&leaf(1, 2, 11, 2), 91);
    let c = descriptor(&leaf(2, 3, 21, 3), 92);
    let orders = [
        vec![a.clone(), b.clone(), c.clone()],
        vec![a.clone(), c.clone(), b.clone()],
        vec![b.clone(), a.clone(), c.clone()],
        vec![b.clone(), c.clone(), a.clone()],
        vec![c.clone(), a.clone(), b.clone()],
        vec![c, b, a],
    ];
    let expected = aggregate(orders[0].clone(), 41).unwrap();

    for order in orders {
        let actual = aggregate(order, 41).unwrap();
        assert_eq!(actual, expected);
        assert_eq!(actual.canonical_hash(), expected.canonical_hash());
    }
}

#[test]
fn child_provenance_is_committed_and_child_order_is_canonical() {
    let left = leaf(0, 1, 1, 1);
    let right = leaf(1, 2, 11, 1);
    let original = aggregate(vec![descriptor(&left, 90), descriptor(&right, 91)], 41).unwrap();

    let mut changed_json = serde_json::to_value(&right).unwrap();
    changed_json["commitments"]["provenance_root"] = serde_json::to_value(commitment(199)).unwrap();
    let changed: NodeJournalV3 = serde_json::from_value(changed_json).unwrap();
    let changed_left_first =
        aggregate(vec![descriptor(&left, 90), descriptor(&changed, 91)], 41).unwrap();
    let changed_right_first =
        aggregate(vec![descriptor(&changed, 91), descriptor(&left, 90)], 41).unwrap();

    assert_ne!(
        original.child_provenance_roots(),
        changed_left_first.child_provenance_roots()
    );
    assert_eq!(changed_left_first, changed_right_first);
}

#[test]
fn overlapping_partitions_reject() {
    let a = descriptor(&leaf(0, 1, 1, 1), 90);
    let b = descriptor(&leaf(0, 1, 11, 1), 91);

    assert_eq!(
        aggregate(vec![a, b], 41),
        Err(ZrpfErrorV3::OverlappingPartitions)
    );
}

#[test]
fn noncontiguous_partitions_reject() {
    let a = descriptor(&leaf(0, 1, 1, 1), 90);
    let b = descriptor(&leaf(2, 3, 11, 1), 91);

    assert_eq!(
        aggregate(vec![a, b], 41),
        Err(ZrpfErrorV3::NonContiguousPartitions)
    );
}

#[test]
fn duplicate_projected_child_rejects_before_partition_analysis() {
    let child = descriptor(&leaf(0, 1, 1, 1), 90);

    assert_eq!(
        aggregate(vec![child.clone(), child], 41),
        Err(ZrpfErrorV3::DuplicateChildClaim)
    );
}

#[test]
fn duplicate_journal_rejects_even_when_claim_ids_differ() {
    let node = leaf(0, 1, 1, 1);
    let first = descriptor(&node, 90);
    let second = descriptor(&node, 91);

    assert_eq!(
        aggregate(vec![first, second], 41),
        Err(ZrpfErrorV3::DuplicateChildJournal)
    );
}

#[test]
fn cross_level_child_set_rejects() {
    let a = leaf(0, 1, 1, 1);
    let b = leaf(1, 2, 11, 1);
    let subtree = aggregate(vec![descriptor(&b, 91)], 41).unwrap();

    assert_eq!(
        aggregate(vec![descriptor(&a, 92), descriptor(&subtree, 93)], 51),
        Err(ZrpfErrorV3::MixedChildLevels)
    );
}

#[test]
fn maximum_fanout_plus_one_rejects() {
    let children = (0..=MAX_IMMEDIATE_CHILDREN_V3)
        .map(|index| {
            let start = index as u64;
            descriptor(
                &leaf(start, start + 1, 1 + (index as u8) * 10, 1),
                100 + index as u8,
            )
        })
        .collect();

    assert_eq!(
        aggregate(children, 41),
        Err(ZrpfErrorV3::TooManyChildren {
            actual: MAX_IMMEDIATE_CHILDREN_V3 + 1,
            maximum: MAX_IMMEDIATE_CHILDREN_V3,
        })
    );
}

#[test]
fn maximum_depth_plus_one_rejects() {
    let leaf_node = leaf(0, 1, 1, 1);
    let level_one = aggregate(vec![descriptor(&leaf_node, 90)], 41).unwrap();
    let level_two = aggregate(vec![descriptor(&level_one, 91)], 51).unwrap();

    assert_eq!(
        aggregate(vec![descriptor(&level_two, 92)], 61),
        Err(ZrpfErrorV3::MaximumTreeLevelExceeded)
    );
}

#[test]
fn zero_commitments_and_zero_operations_reject() {
    assert_eq!(
        CommitmentV3::new([0; 32]),
        Err(ZrpfErrorV3::ZeroCommitment("commitment"))
    );

    let input = LeafNodeInputV3 {
        task_id: task(1),
        partition: PartitionV3::new(0, 1).unwrap(),
        operation_count: 0,
        count_unit_id: count_unit(),
        scope: scope(),
        proof_profile_id: profile(TEST_PROFILE_SEED),
        actual_program_id: program(2),
        node_statement_hash: commitment(4),
        program_manifest_root: commitment(5),
        commitments: commitments(30),
    };
    assert_eq!(
        NodeJournalV3::new_leaf(input),
        Err(ZrpfErrorV3::ZeroOperationCount)
    );

    let mut encoded = serde_json::to_value(leaf(0, 1, 1, 1)).unwrap();
    encoded.as_object_mut().unwrap().insert(
        "node_statement_hash".to_owned(),
        serde_json::Value::Array(vec![serde_json::Value::from(0); 32]),
    );
    assert!(serde_json::from_value::<NodeJournalV3>(encoded).is_err());
}

#[test]
fn operation_count_above_the_leaf_cap_rejects() {
    assert_eq!(
        NodeJournalV3::new_leaf(LeafNodeInputV3 {
            task_id: task(1),
            partition: PartitionV3::new(0, 1).unwrap(),
            operation_count: u64::MAX,
            count_unit_id: count_unit(),
            scope: scope(),
            proof_profile_id: profile(TEST_PROFILE_SEED),
            actual_program_id: program(2),
            node_statement_hash: commitment(4),
            program_manifest_root: commitment(5),
            commitments: commitments(30),
        }),
        Err(ZrpfErrorV3::OperationLimitExceeded {
            actual: u64::MAX,
            maximum: MAX_OPERATIONS_PER_LEAF_V3,
        })
    );
}

#[test]
fn exact_postcard_decoder_rejects_trailing_and_oversized_bytes() {
    let node = leaf(0, 1, 1, 1);
    let mut node_bytes = encode_node_journal_v3(&node).unwrap();
    node_bytes.push(0);

    assert_eq!(
        decode_exact_node_journal_v3(&node_bytes),
        Err(ZrpfErrorV3::TrailingBytes)
    );
    let oversized = vec![0; MAX_NODE_JOURNAL_BYTES_V3 + 1];
    assert_eq!(
        decode_exact_node_journal_v3(&oversized),
        Err(ZrpfErrorV3::InputTooLarge {
            actual: MAX_NODE_JOURNAL_BYTES_V3 + 1,
            maximum: MAX_NODE_JOURNAL_BYTES_V3,
        })
    );
}

#[test]
fn stale_version_and_nonminimal_postcard_integer_reject() {
    let node = leaf(0, 1, 1, 1);
    let mut stale = serde_json::to_value(&node).unwrap();
    stale["journal_version"] = serde_json::Value::from(2);
    assert!(serde_json::from_value::<NodeJournalV3>(stale).is_err());

    let canonical = encode_node_journal_v3(&node).unwrap();
    assert_eq!(canonical[0], 3);
    let mut nonminimal = vec![0x83, 0x00];
    nonminimal.extend_from_slice(&canonical[1..]);
    assert!(matches!(
        decode_exact_node_journal_v3(&nonminimal),
        Err(ZrpfErrorV3::PostcardDecode | ZrpfErrorV3::NonCanonicalEncoding)
    ));
}

#[test]
fn unknown_json_fields_reject_at_the_journal_boundary() {
    let node = leaf(0, 1, 1, 1);
    let mut node_json = serde_json::to_string(&node).unwrap();
    node_json.pop();
    node_json.push_str(",\"unknown_critical_field\":1}");

    assert!(serde_json::from_str::<NodeJournalV3>(&node_json).is_err());

    let mut nested = serde_json::to_value(node).unwrap();
    nested["scope"]["unknown_critical_field"] = serde_json::Value::from(1);
    assert!(serde_json::from_value::<NodeJournalV3>(nested).is_err());
}

#[test]
fn verifier_id_is_derived_and_tampering_rejects() {
    let node = leaf(0, 1, 1, 1);
    assert_eq!(
        node.verifier_id(),
        derive_verifier_id_v3(program(2), profile(TEST_PROFILE_SEED)).unwrap()
    );

    let mut tampered = serde_json::to_value(node).unwrap();
    tampered["verifier_id"] = serde_json::Value::Array(vec![serde_json::Value::from(99); 32]);
    assert!(serde_json::from_value::<NodeJournalV3>(tampered).is_err());
}

#[test]
fn scope_mismatch_and_duplicate_task_reject() {
    let left = leaf(0, 1, 1, 1);
    let mut wrong_scope = serde_json::to_value(leaf(1, 2, 11, 1)).unwrap();
    wrong_scope["scope"]["application_id"] =
        serde_json::Value::Array(vec![serde_json::Value::from(224); 32]);
    let wrong_scope: NodeJournalV3 = serde_json::from_value(wrong_scope).unwrap();
    assert_eq!(
        aggregate(
            vec![descriptor(&left, 90), descriptor(&wrong_scope, 91)],
            41,
        ),
        Err(ZrpfErrorV3::ScopeMismatch)
    );

    let mut duplicate_task = serde_json::to_value(leaf(1, 2, 11, 1)).unwrap();
    duplicate_task["task_id"] = serde_json::to_value(left.task_id()).unwrap();
    let duplicate_task: NodeJournalV3 = serde_json::from_value(duplicate_task).unwrap();
    assert_eq!(
        aggregate(
            vec![descriptor(&left, 92), descriptor(&duplicate_task, 93)],
            41,
        ),
        Err(ZrpfErrorV3::DuplicateChildTask)
    );

    let parent_task = leaf(0, 1, 41, 1);
    assert_eq!(
        aggregate(vec![descriptor(&parent_task, 94)], 41),
        Err(ZrpfErrorV3::DuplicateChildTask)
    );
}

#[test]
fn mixed_count_units_reject_before_counts_are_summed() {
    let left = leaf(0, 1, 1, 1);
    let mut wrong_unit = serde_json::to_value(leaf(1, 2, 11, 1)).unwrap();
    wrong_unit["count_unit_id"] = serde_json::to_value(commitment(232)).unwrap();
    let wrong_unit: NodeJournalV3 = serde_json::from_value(wrong_unit).unwrap();

    assert_eq!(
        aggregate(vec![descriptor(&left, 90), descriptor(&wrong_unit, 91)], 41,),
        Err(ZrpfErrorV3::CountUnitMismatch)
    );
}

#[test]
fn structural_decode_rejects_impossible_aggregate_geometry_and_empty_child_roots() {
    let left = leaf(0, 1, 1, 1);
    let right = leaf(1, 2, 11, 1);
    let aggregate_node =
        aggregate(vec![descriptor(&left, 90), descriptor(&right, 91)], 41).unwrap();

    let mut impossible = serde_json::to_value(&aggregate_node).unwrap();
    impossible["partition"]["end_exclusive"] = serde_json::Value::from(3);
    impossible["leaf_count"] = serde_json::Value::from(3);
    impossible["subtree_node_count"] = serde_json::Value::from(4);
    assert!(serde_json::from_value::<NodeJournalV3>(impossible).is_err());

    let mut empty_child_root = serde_json::to_value(aggregate_node).unwrap();
    empty_child_root["child_claims_root"] = serde_json::to_value(left.child_claims_root()).unwrap();
    assert!(serde_json::from_value::<NodeJournalV3>(empty_child_root).is_err());
}

#[test]
fn mutated_nonempty_child_root_remains_structural_and_has_no_proof_authority() {
    let left = leaf(0, 1, 1, 1);
    let right = leaf(1, 2, 11, 1);
    let aggregate_node =
        aggregate(vec![descriptor(&left, 90), descriptor(&right, 91)], 41).unwrap();
    let mut mutated = serde_json::to_value(aggregate_node).unwrap();
    mutated["child_claims_root"] = serde_json::Value::Array(vec![serde_json::Value::from(99); 32]);

    let decoded: NodeJournalV3 = serde_json::from_value(mutated).unwrap();

    assert_eq!(decoded.child_claims_root(), commitment(99));
}

#[test]
fn heterogeneous_child_profile_is_committed_without_self_authorizing_it() {
    let child = leaf_with_profile(0, 1, 1, 1, TEST_PROFILE_SEED.wrapping_sub(1));
    let parent = aggregate(vec![descriptor(&child, 90)], 41).unwrap();

    assert_ne!(parent.child_profiles_root().into_bytes(), [0; 32]);
    assert_ne!(parent.child_profiles_root(), parent.child_programs_root());
}

#[test]
fn leaf_partition_width_and_operation_caps_are_enforced() {
    let mut wrong_width = serde_json::to_value(leaf(0, 1, 1, 1)).unwrap();
    wrong_width["partition"]["end_exclusive"] = serde_json::Value::from(2);
    assert!(serde_json::from_value::<NodeJournalV3>(wrong_width).is_err());

    assert!(NodeJournalV3::new_leaf(LeafNodeInputV3 {
        task_id: task(1),
        partition: PartitionV3::new(0, 1).unwrap(),
        operation_count: MAX_OPERATIONS_PER_LEAF_V3,
        count_unit_id: count_unit(),
        scope: scope(),
        proof_profile_id: profile(TEST_PROFILE_SEED),
        actual_program_id: program(2),
        node_statement_hash: commitment(4),
        program_manifest_root: commitment(5),
        commitments: commitments(30),
    })
    .is_ok());
}

#[test]
fn leaf_hash_has_a_fixed_manual_canonical_vector() {
    let node = leaf(10, 11, 1, 7);
    let canonical_bytes = encode_node_journal_v3(&node).unwrap();

    assert_eq!(
        node.commitments().canonical_hash().unwrap().into_bytes(),
        [
            224, 158, 42, 219, 162, 160, 41, 65, 192, 21, 75, 246, 203, 77, 199, 89, 252, 63, 215,
            205, 81, 146, 117, 108, 44, 73, 236, 64, 12, 161, 157, 93,
        ]
    );
    assert_eq!(
        node.canonical_hash().unwrap().into_bytes(),
        [
            49, 156, 205, 8, 63, 163, 138, 51, 28, 85, 195, 166, 35, 158, 170, 242, 14, 211, 158,
            254, 128, 37, 67, 108, 37, 100, 84, 125, 9, 95, 119, 231,
        ]
    );
    assert_eq!(canonical_bytes.len(), 1_547);
    assert_eq!(
        <[u8; 32]>::from(Sha256::digest(canonical_bytes)),
        [
            92, 52, 87, 16, 132, 250, 236, 195, 240, 248, 146, 88, 200, 18, 118, 99, 249, 80, 156,
            25, 156, 254, 181, 143, 235, 43, 171, 194, 160, 50, 21, 253,
        ]
    );
}
