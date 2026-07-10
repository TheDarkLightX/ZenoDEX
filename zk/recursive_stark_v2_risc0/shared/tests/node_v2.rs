use std::boxed::Box;

use tau_state_proof_risc0_shared::{
    recursive_asset_delta_root_v1, recursive_authority_set_root_v1,
    recursive_child_journal_hash_v1, recursive_child_verification_claim_hash_v1,
    recursive_child_verifier_id_v1, recursive_cross_shard_message_id_v1,
    recursive_cross_shard_messages_root_v1, recursive_effect_summary_hash_v1,
    recursive_lane_state_vector_root_v1, recursive_receipt_ids_root_v1,
    recursive_verifier_set_root_v1, RecursiveChildDescriptorV1, RecursiveChildEffectV1,
    RecursiveCompositionStatementV1, RecursiveCrossShardMessageV1, RecursiveEffectSummaryV1,
    RECURSIVE_DOMAIN_SEPARATOR_V1, RECURSIVE_EFFECT_SUMMARY_VERSION_V1, RECURSIVE_EPOCH_PROFILE_V1,
    RECURSIVE_SPOT_LEAF_PROFILE_V1, RECURSIVE_STATEMENT_VERSION_V1,
    RECURSIVE_STRICT_CROSS_SHARD_MODE_V1, RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1,
};
use tau_state_proof_risc0_shared_v2::{
    compose_recursive_node_journal_v2, decode_exact_postcard_v2,
    derive_recursive_node_commitments_v2, preflight_recursive_node_input_v2,
    recursive_immediate_verifier_set_root_v2, recursive_node_journal_bytes_hash_v2,
    recursive_node_verification_claim_hash_v2, recursive_node_verifier_id_v2,
    RecursiveImmediateChildV2, RecursiveNodeBoundsV2, RecursiveNodeChildDescriptorV2,
    RecursiveNodeInputV2, RecursiveNodeLevelV2, RecursiveNodeProfileV2, RecursiveNodeStatementV2,
    RECURSIVE_NODE_DOMAIN_SEPARATOR_V2, RECURSIVE_NODE_SCHEMA_VERSION_V2,
    RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN,
};

fn h(byte: u8) -> [u8; 32] {
    [byte; 32]
}

fn leaf(lane_id: &str, statement_hash: [u8; 32]) -> RecursiveChildEffectV1 {
    let image_id = [7u32; 8];
    let empty_rows = Vec::new();
    let empty_messages = Vec::new();
    let empty_receipts = Vec::new();
    let summary = RecursiveEffectSummaryV1 {
        summary_version: RECURSIVE_EFFECT_SUMMARY_VERSION_V1,
        lane_id: lane_id.to_string(),
        lane_kind: "spot_transition_v1".to_string(),
        chain_id: "tau-test".to_string(),
        epoch_id: 9,
        proof_profile: RECURSIVE_SPOT_LEAF_PROFILE_V1.to_string(),
        risc0_image_id: image_id,
        statement_hash,
        pre_state_root: h(10),
        post_state_root: h(11),
        tx_root: h(12),
        evidence_root: h(13),
        receipt_root: h(14),
        accepted_receipts_root: recursive_receipt_ids_root_v1(&empty_receipts).unwrap(),
        rejected_receipts_root: recursive_receipt_ids_root_v1(&empty_receipts).unwrap(),
        asset_delta_root: recursive_asset_delta_root_v1(&empty_rows).unwrap(),
        cross_shard_outbox_root: recursive_cross_shard_messages_root_v1(&empty_messages).unwrap(),
        cross_shard_inbox_root: recursive_cross_shard_messages_root_v1(&empty_messages).unwrap(),
        write_set_root: h(15),
        public_policy_hash: h(16),
        feature_suite_hash: h(17),
        dependency_lock_hash: h(18),
        toolchain_lock_hash: h(19),
    };
    let journal_bytes = postcard::to_allocvec(&summary).unwrap();
    let child_verifier_id =
        recursive_child_verifier_id_v1(&image_id, RECURSIVE_SPOT_LEAF_PROFILE_V1).unwrap();
    RecursiveChildEffectV1 {
        descriptor: RecursiveChildDescriptorV1 {
            child_verification_claim_hash: recursive_child_verification_claim_hash_v1(
                &image_id,
                &journal_bytes,
            )
            .unwrap(),
            child_journal_hash: recursive_child_journal_hash_v1(&journal_bytes).unwrap(),
            child_effect_summary_hash: recursive_effect_summary_hash_v1(&summary),
            child_statement_hash: summary.statement_hash,
            child_image_id: image_id,
            child_verifier_id,
            child_profile: summary.proof_profile.clone(),
        },
        child_journal_bytes: journal_bytes,
        summary,
        asset_delta_rows: empty_rows,
        outbox_messages: empty_messages.clone(),
        inbox_messages: empty_messages,
        accepted_receipt_ids: empty_receipts.clone(),
        rejected_receipt_ids: empty_receipts,
    }
}

fn leaf_with_receipts(
    lane_id: &str,
    statement_hash: [u8; 32],
    accepted_receipt_ids: Vec<[u8; 32]>,
    rejected_receipt_ids: Vec<[u8; 32]>,
) -> RecursiveChildEffectV1 {
    let mut child = leaf(lane_id, statement_hash);
    child.summary.accepted_receipts_root =
        recursive_receipt_ids_root_v1(&accepted_receipt_ids).unwrap();
    child.summary.rejected_receipts_root =
        recursive_receipt_ids_root_v1(&rejected_receipt_ids).unwrap();
    child.accepted_receipt_ids = accepted_receipt_ids;
    child.rejected_receipt_ids = rejected_receipt_ids;
    refresh_leaf_bindings(&mut child);
    child
}

fn leaf_with_messages(
    lane_id: &str,
    statement_hash: [u8; 32],
    outbox_messages: Vec<RecursiveCrossShardMessageV1>,
    inbox_messages: Vec<RecursiveCrossShardMessageV1>,
) -> RecursiveChildEffectV1 {
    let mut child = leaf(lane_id, statement_hash);
    child.summary.cross_shard_outbox_root =
        recursive_cross_shard_messages_root_v1(&outbox_messages).unwrap();
    child.summary.cross_shard_inbox_root =
        recursive_cross_shard_messages_root_v1(&inbox_messages).unwrap();
    child.outbox_messages = outbox_messages;
    child.inbox_messages = inbox_messages;
    refresh_leaf_bindings(&mut child);
    child
}

fn refresh_leaf_bindings(child: &mut RecursiveChildEffectV1) {
    child.child_journal_bytes = postcard::to_allocvec(&child.summary).unwrap();
    child.descriptor.child_verification_claim_hash = recursive_child_verification_claim_hash_v1(
        &child.descriptor.child_image_id,
        &child.child_journal_bytes,
    )
    .unwrap();
    child.descriptor.child_journal_hash =
        recursive_child_journal_hash_v1(&child.child_journal_bytes).unwrap();
    child.descriptor.child_effect_summary_hash = recursive_effect_summary_hash_v1(&child.summary);
}

fn routed_message(
    source_shard_id: &str,
    destination_shard_id: &str,
    scope_seed: u8,
) -> RecursiveCrossShardMessageV1 {
    let mut message = RecursiveCrossShardMessageV1 {
        message_id: [0u8; 32],
        epoch_id: 9,
        source_shard_id: source_shard_id.to_string(),
        destination_shard_id: destination_shard_id.to_string(),
        asset_id: "ASSET0".to_string(),
        amount_atoms: 1,
        sender_scope_hash: h(scope_seed),
        recipient_scope_hash: h(scope_seed + 1),
        source_receipt_hash: h(scope_seed + 2),
        deadline_epoch: 9,
    };
    message.message_id = recursive_cross_shard_message_id_v1(&message).unwrap();
    message
}

fn flat_statement(leaves: &[RecursiveChildEffectV1]) -> RecursiveCompositionStatementV1 {
    let verifier_ids = vec![leaves[0].descriptor.child_verifier_id];
    let pre: Vec<_> = leaves
        .iter()
        .map(|leaf| (leaf.summary.lane_id.clone(), leaf.summary.pre_state_root))
        .collect();
    let post: Vec<_> = leaves
        .iter()
        .map(|leaf| (leaf.summary.lane_id.clone(), leaf.summary.post_state_root))
        .collect();
    RecursiveCompositionStatementV1 {
        domain_separator: RECURSIVE_DOMAIN_SEPARATOR_V1.to_string(),
        schema_version: RECURSIVE_STATEMENT_VERSION_V1,
        chain_id: "tau-test".to_string(),
        epoch_id: 9,
        proof_profile: RECURSIVE_EPOCH_PROFILE_V1.to_string(),
        verifier_set_root: recursive_verifier_set_root_v1(&verifier_ids).unwrap(),
        allowed_authority_roots_root: recursive_authority_set_root_v1(&[]).unwrap(),
        public_policy_hash: h(16),
        feature_suite_hash: h(17),
        dependency_lock_hash: h(18),
        toolchain_lock_hash: h(19),
        expected_pre_state_root: recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.pre_state_vector_root.v1",
            &pre,
        )
        .unwrap(),
        expected_post_state_root: recursive_lane_state_vector_root_v1(
            b"zenodex.risc0.recursive.post_state_vector_root.v1",
            &post,
        )
        .unwrap(),
        conflict_schedule_hash: h(20),
        carry_queue_pre_root: h(21),
        carry_queue_post_root: h(21),
        data_availability_root: h(22),
        expected_child_count: leaves.len() as u32,
        max_children: 64,
        max_child_journal_bytes: 4096,
        max_total_child_journal_bytes: 32768,
        max_asset_delta_rows: 64,
        max_cross_shard_messages: 64,
        max_receipt_ids: 64,
        cross_shard_mode: RECURSIVE_STRICT_CROSS_SHARD_MODE_V1.to_string(),
    }
}

fn input_from_leaves(leaves: Vec<RecursiveChildEffectV1>) -> RecursiveNodeInputV2 {
    let flat = flat_statement(&leaves);
    let verifier_ids = vec![leaves[0].descriptor.child_verifier_id];
    let child_count = leaves.len() as u32;
    let children = leaves
        .into_iter()
        .map(|child| RecursiveImmediateChildV2::LeafV1 {
            child: Box::new(child),
        })
        .collect();
    let mut input = RecursiveNodeInputV2 {
        statement: RecursiveNodeStatementV2 {
            schema_version: RECURSIVE_NODE_SCHEMA_VERSION_V2,
            domain_separator: RECURSIVE_NODE_DOMAIN_SEPARATOR_V2.to_string(),
            level: RecursiveNodeLevelV2::ClosedSubtreeOverLeaves,
            profile: RecursiveNodeProfileV2::ClosedSubtree,
            self_image_id: [9u32; 8],
            flat_statement: flat,
            immediate_verifier_set_root: recursive_immediate_verifier_set_root_v2(&verifier_ids)
                .unwrap(),
            expected_immediate_child_count: child_count,
            expected_flat_leaf_count: child_count,
            expected_tree_height: 1,
            expected_subtree_node_count: 1 + child_count,
            expected_assigned_leaf_ids_root: h(1),
            expected_descendant_claims_root: h(1),
            expected_descendant_sources_root: h(1),
            expected_partition_plan_root: h(1),
            bounds: RecursiveNodeBoundsV2 {
                max_immediate_children: 8,
                max_flat_leaves: 64,
                max_child_journal_bytes: 4096,
                max_total_child_journal_bytes: 32768,
                max_flat_disclosure_bytes: 1_048_576,
            },
        },
        allowed_immediate_verifier_ids: verifier_ids.clone(),
        allowed_flat_leaf_verifier_ids: verifier_ids,
        allowed_authority_roots: Vec::new(),
        children,
    };
    fill_expectations(&mut input);
    input
}

fn fill_expectations(input: &mut RecursiveNodeInputV2) {
    let commitments = derive_recursive_node_commitments_v2(input).unwrap();
    input.statement.expected_immediate_child_count = commitments.immediate_child_count;
    input.statement.expected_flat_leaf_count = commitments.flat_leaf_count;
    input.statement.expected_tree_height = commitments.tree_height;
    input.statement.expected_subtree_node_count = commitments.subtree_node_count;
    input.statement.expected_assigned_leaf_ids_root = commitments.assigned_leaf_ids_root;
    input.statement.expected_descendant_claims_root = commitments.descendant_claims_root;
    input.statement.expected_descendant_sources_root = commitments.descendant_sources_root;
    input.statement.expected_partition_plan_root = commitments.partition_plan_root;
}

fn err_text(input: &RecursiveNodeInputV2) -> String {
    format!(
        "{:?}",
        preflight_recursive_node_input_v2(input).unwrap_err()
    )
}

#[test]
fn valid_closed_subtree_composes_flat_v1_projection() {
    let input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    let claims = preflight_recursive_node_input_v2(&input).unwrap();
    let journal = compose_recursive_node_journal_v2(&input).unwrap();
    assert_eq!(claims.len(), 1);
    assert_eq!(journal.tree_height, 1);
    assert_eq!(journal.flat_leaf_count, 1);
    assert_eq!(journal.subtree_node_count, 2);
    assert_eq!(journal.flat_v1_projection.child_count, 1);
}

#[test]
fn valid_nonempty_receipt_sets_compose_independently_of_lane_order() {
    let input = input_from_leaves(vec![
        leaf_with_receipts("lane-a", h(30), vec![h(2)], vec![h(4)]),
        leaf_with_receipts("lane-b", h(31), vec![h(1)], vec![h(3)]),
    ]);

    let journal = compose_recursive_node_journal_v2(&input).unwrap();

    assert_eq!(
        journal.flat_v1_projection.accepted_receipts_root,
        recursive_receipt_ids_root_v1(&[h(1), h(2)]).unwrap()
    );
    assert_eq!(
        journal.flat_v1_projection.rejected_receipts_root,
        recursive_receipt_ids_root_v1(&[h(3), h(4)]).unwrap()
    );
}

#[test]
fn duplicate_receipt_id_across_v2_lanes_rejects() {
    let input = input_from_leaves(vec![
        leaf_with_receipts("lane-a", h(30), vec![h(2)], Vec::new()),
        leaf_with_receipts("lane-b", h(31), vec![h(2)], Vec::new()),
    ]);

    assert!(format!(
        "{:?}",
        compose_recursive_node_journal_v2(&input).unwrap_err()
    )
    .contains("accepted receipt ids not sorted unique"));
}

#[test]
fn accepted_and_rejected_receipt_partitions_each_use_the_v1_bound() {
    let mut input = input_from_leaves(vec![
        leaf_with_receipts("lane-a", h(30), vec![h(1)], vec![h(3)]),
        leaf_with_receipts("lane-b", h(31), vec![h(2)], vec![h(4)]),
    ]);
    input.statement.flat_statement.max_receipt_ids = 2;
    fill_expectations(&mut input);

    let journal = compose_recursive_node_journal_v2(&input).unwrap();

    assert_eq!(
        journal.flat_v1_projection.accepted_receipts_root,
        recursive_receipt_ids_root_v1(&[h(1), h(2)]).unwrap()
    );
    assert_eq!(
        journal.flat_v1_projection.rejected_receipts_root,
        recursive_receipt_ids_root_v1(&[h(3), h(4)]).unwrap()
    );
}

#[test]
fn accepted_receipt_partition_bound_plus_one_rejects() {
    let mut input = input_from_leaves(vec![
        leaf_with_receipts("lane-a", h(30), vec![h(1)], Vec::new()),
        leaf_with_receipts("lane-b", h(31), vec![h(2)], Vec::new()),
    ]);
    input.statement.flat_statement.max_receipt_ids = 1;

    assert!(format!(
        "{:?}",
        derive_recursive_node_commitments_v2(&input).unwrap_err()
    )
    .contains("flat disclosure rows exceed max"));
}

#[test]
fn rejected_receipt_partition_bound_plus_one_rejects() {
    let mut input = input_from_leaves(vec![
        leaf_with_receipts("lane-a", h(30), Vec::new(), vec![h(1)]),
        leaf_with_receipts("lane-b", h(31), Vec::new(), vec![h(2)]),
    ]);
    input.statement.flat_statement.max_receipt_ids = 1;

    assert!(format!(
        "{:?}",
        derive_recursive_node_commitments_v2(&input).unwrap_err()
    )
    .contains("flat disclosure rows exceed max"));
}

#[test]
fn outbox_and_inbox_message_partitions_each_use_the_v1_bound() {
    let left_to_right = routed_message("lane-a", "lane-b", 10);
    let right_to_left = routed_message("lane-b", "lane-a", 20);
    let mut input = input_from_leaves(vec![
        leaf_with_messages(
            "lane-a",
            h(30),
            vec![left_to_right.clone()],
            vec![right_to_left.clone()],
        ),
        leaf_with_messages("lane-b", h(31), vec![right_to_left], vec![left_to_right]),
    ]);
    input.statement.flat_statement.max_cross_shard_messages = 2;
    fill_expectations(&mut input);

    let journal = compose_recursive_node_journal_v2(&input).unwrap();

    assert_eq!(
        journal.flat_v1_projection.cross_shard_outbox_root,
        journal.flat_v1_projection.cross_shard_inbox_root
    );
}

#[test]
fn outbox_message_partition_bound_plus_one_rejects_independently() {
    let left_to_right = routed_message("lane-a", "lane-b", 10);
    let right_to_left = routed_message("lane-b", "lane-a", 20);
    let mut input = input_from_leaves(vec![
        leaf_with_messages("lane-a", h(30), vec![left_to_right.clone()], Vec::new()),
        leaf_with_messages("lane-b", h(31), vec![right_to_left], Vec::new()),
    ]);
    input.statement.flat_statement.max_cross_shard_messages = 1;

    assert!(format!(
        "{:?}",
        derive_recursive_node_commitments_v2(&input).unwrap_err()
    )
    .contains("flat disclosure rows exceed max"));
}

#[test]
fn inbox_message_partition_bound_plus_one_rejects_independently() {
    let left_to_right = routed_message("lane-a", "lane-b", 10);
    let right_to_left = routed_message("lane-b", "lane-a", 20);
    let mut input = input_from_leaves(vec![
        leaf_with_messages("lane-a", h(30), Vec::new(), vec![right_to_left]),
        leaf_with_messages("lane-b", h(31), Vec::new(), vec![left_to_right]),
    ]);
    input.statement.flat_statement.max_cross_shard_messages = 1;

    assert!(format!(
        "{:?}",
        derive_recursive_node_commitments_v2(&input).unwrap_err()
    )
    .contains("flat disclosure rows exceed max"));
}

#[test]
fn valid_epoch_root_composes_authenticated_node_child() {
    let leaf = leaf("lane-a", h(30));
    let inner_input = input_from_leaves(vec![leaf.clone()]);
    let inner = compose_recursive_node_journal_v2(&inner_input).unwrap();
    let inner_bytes = postcard::to_allocvec(&inner).unwrap();
    let aggregate_image_id = [9u32; 8];
    let node_verifier_id =
        recursive_node_verifier_id_v2(&aggregate_image_id, RecursiveNodeProfileV2::ClosedSubtree)
            .unwrap();
    let descriptor = RecursiveNodeChildDescriptorV2 {
        child_image_id: aggregate_image_id,
        child_profile: RecursiveNodeProfileV2::ClosedSubtree,
        child_verifier_id: node_verifier_id,
        child_verification_claim_hash: recursive_node_verification_claim_hash_v2(
            &aggregate_image_id,
            &inner_bytes,
        )
        .unwrap(),
        child_journal_hash: recursive_node_journal_bytes_hash_v2(&inner_bytes).unwrap(),
        child_statement_hash: inner.statement_hash,
    };
    let mut root_input = RecursiveNodeInputV2 {
        statement: RecursiveNodeStatementV2 {
            schema_version: RECURSIVE_NODE_SCHEMA_VERSION_V2,
            domain_separator: RECURSIVE_NODE_DOMAIN_SEPARATOR_V2.to_string(),
            level: RecursiveNodeLevelV2::EpochRootOverSubtrees,
            profile: RecursiveNodeProfileV2::EpochRoot,
            self_image_id: aggregate_image_id,
            flat_statement: inner_input.statement.flat_statement.clone(),
            immediate_verifier_set_root: recursive_immediate_verifier_set_root_v2(&[
                node_verifier_id,
            ])
            .unwrap(),
            expected_immediate_child_count: 1,
            expected_flat_leaf_count: 1,
            expected_tree_height: 2,
            expected_subtree_node_count: 3,
            expected_assigned_leaf_ids_root: h(1),
            expected_descendant_claims_root: h(1),
            expected_descendant_sources_root: h(1),
            expected_partition_plan_root: h(1),
            bounds: inner_input.statement.bounds.clone(),
        },
        allowed_immediate_verifier_ids: vec![node_verifier_id],
        allowed_flat_leaf_verifier_ids: inner_input.allowed_flat_leaf_verifier_ids.clone(),
        allowed_authority_roots: Vec::new(),
        children: vec![RecursiveImmediateChildV2::NodeV2 {
            descriptor: Box::new(descriptor),
            journal_bytes: Box::new(inner_bytes),
            flat_leaf_disclosures: Box::new(vec![leaf]),
        }],
    };
    fill_expectations(&mut root_input);

    let claims = preflight_recursive_node_input_v2(&root_input).unwrap();
    let root = compose_recursive_node_journal_v2(&root_input).unwrap();

    assert_eq!(claims.len(), 1);
    assert_eq!(root.tree_height, 2);
    assert_eq!(root.subtree_node_count, 3);
    assert_eq!(root.flat_v1_projection, inner.flat_v1_projection);
    assert_eq!(root.assigned_leaf_ids_root, inner.assigned_leaf_ids_root);
    assert_eq!(root.descendant_claims_root, inner.descendant_claims_root);
}

#[test]
fn recursive_node_input_postcard_round_trips_exactly() {
    let input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    let bytes = postcard::to_allocvec(&input).unwrap();
    let decoded: RecursiveNodeInputV2 = decode_exact_postcard_v2(&bytes).unwrap();
    assert_eq!(decoded, input);
}

#[test]
fn duplicate_source_under_lane_alias_rejects() {
    let first = leaf("lane-a", h(30));
    let second = leaf("lane-b", h(30));
    let mut input = input_from_leaves(vec![first]);
    input.children.push(RecursiveImmediateChildV2::LeafV1 {
        child: Box::new(second),
    });
    input.statement.expected_immediate_child_count = 2;
    input.statement.expected_flat_leaf_count = 2;
    input.statement.expected_subtree_node_count = 3;
    input.statement.flat_statement = flat_statement(
        &input
            .children
            .iter()
            .map(|child| match child {
                RecursiveImmediateChildV2::LeafV1 { child } => child.as_ref().clone(),
                _ => unreachable!(),
            })
            .collect::<Vec<_>>(),
    );
    assert!(format!(
        "{:?}",
        derive_recursive_node_commitments_v2(&input).unwrap_err()
    )
    .contains("descendant source IDs not unique"));
}

#[test]
fn wrong_child_kind_for_level_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    input.statement.level = RecursiveNodeLevelV2::EpochRootOverSubtrees;
    input.statement.profile = RecursiveNodeProfileV2::EpochRoot;
    input.statement.expected_tree_height = 2;
    assert!(err_text(&input).contains("wrong child kind for node level"));
}

#[test]
fn hard_fanout_cap_plus_one_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    input.statement.bounds.max_immediate_children = RECURSIVE_NODE_V2_MAX_IMMEDIATE_CHILDREN + 1;
    assert!(err_text(&input).contains("node bounds invalid"));
}

#[test]
fn trailing_leaf_journal_byte_rejects_after_preflight() {
    let mut child = leaf("lane-a", h(30));
    child.child_journal_bytes.push(0);
    child.descriptor.child_journal_hash =
        recursive_child_journal_hash_v1(&child.child_journal_bytes).unwrap();
    child.descriptor.child_verification_claim_hash = recursive_child_verification_claim_hash_v1(
        &child.descriptor.child_image_id,
        &child.child_journal_bytes,
    )
    .unwrap();
    let input = input_from_leaves(vec![child]);
    preflight_recursive_node_input_v2(&input).unwrap();
    assert!(format!(
        "{:?}",
        compose_recursive_node_journal_v2(&input).unwrap_err()
    )
    .contains("postcard trailing bytes"));
}

#[test]
fn expected_partition_root_substitution_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    input.statement.expected_partition_plan_root = h(99);
    assert!(err_text(&input).contains("partition plan root mismatch"));
}

#[test]
fn expected_source_root_substitution_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    input.statement.expected_descendant_sources_root = h(99);
    assert!(err_text(&input).contains("descendant sources root mismatch"));
}

#[test]
fn duplicate_immediate_verifier_authorization_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    input
        .allowed_immediate_verifier_ids
        .push(input.allowed_immediate_verifier_ids[0]);

    assert!(err_text(&input).contains("immediate verifier IDs not sorted unique"));
}

#[test]
fn duplicate_flat_leaf_verifier_authorization_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    input
        .allowed_flat_leaf_verifier_ids
        .push(input.allowed_flat_leaf_verifier_ids[0]);

    assert!(err_text(&input).contains("flat leaf verifier IDs not sorted unique"));
}

#[test]
fn leaf_verifier_image_binding_substitution_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    let RecursiveImmediateChildV2::LeafV1 { child } = &mut input.children[0] else {
        unreachable!();
    };
    child.descriptor.child_verifier_id = h(99);

    assert!(err_text(&input).contains("leaf immediate verifier is not allowed"));
}

#[test]
fn summary_test_profile_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    let RecursiveImmediateChildV2::LeafV1 { child } = &mut input.children[0] else {
        unreachable!();
    };
    child.summary.proof_profile = RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1.to_string();
    child.descriptor.child_profile = RECURSIVE_SUMMARY_LEAF_TEST_PROFILE_V1.to_string();
    assert!(err_text(&input).contains("summary test leaf is not admissible"));
}

#[test]
fn trusted_count_mismatch_rejects() {
    let mut input = input_from_leaves(vec![leaf("lane-a", h(30))]);
    input.statement.expected_subtree_node_count = 3;
    assert!(err_text(&input).contains("node derived count mismatch"));
}
