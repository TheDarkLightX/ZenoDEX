use tau_state_proof_risc0_shared::{
    recursive_cross_shard_messages_root_v1, recursive_receipt_ids_root_v1,
    RecursiveEffectSummaryV1, RECURSIVE_SPOT_LEAF_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, semantic_epoch_manifest_root_v1, NodeJournalV3,
    SemanticEpochDependencyProgramsInputV1, SemanticEpochDependencyProgramsV1,
    V1AdapterSemanticLeafOpeningV1, ZrpfErrorV3,
};
use zenodex_zrpf_risc0_aggregate_shared::{
    recompose_expected_structural_aggregate_v1, StructuralAggregateErrorV1,
    StructuralAggregateInputV1, StructuralAggregatePolicyV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    compose_semantic_epoch_after_level_one_verification_v1, recompose_expected_semantic_epoch_v1,
    DisclosedStructuralLevelOneV1, DisclosedV1AdapterLeafV1, SemanticEpochCompositionErrorV1,
    SemanticEpochCompositionInputV1, SemanticEpochCompositionPolicyV1,
    SemanticRecompositionErrorV1, SemanticRecompositionInputV1,
};
use zenodex_zrpf_risc0_shared::{
    program_id_from_risc0_words_v3, project_policy_bound_v1_journal, SourceKindV1,
    PINNED_SPOT_LEAF_IMAGE_ID_V1,
};

const ADAPTER_IMAGE_ID: [u32; 8] = [31, 32, 33, 34, 35, 36, 37, 38];
const LEVEL_ONE_IMAGE_ID: [u32; 8] = [41, 42, 43, 44, 45, 46, 47, 48];
const LEVEL_TWO_IMAGE_ID: [u32; 8] = [51, 52, 53, 54, 55, 56, 57, 58];
const SEMANTIC_IMAGE_ID: [u32; 8] = [61, 62, 63, 64, 65, 66, 67, 68];

fn root(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn summary(seed: u8, chain_id: &str) -> RecursiveEffectSummaryV1 {
    let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
    let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
    RecursiveEffectSummaryV1 {
        summary_version: 1,
        lane_id: format!("spot-semantic-epoch-{seed}"),
        lane_kind: "spot".to_owned(),
        chain_id: chain_id.to_owned(),
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

fn leaf(seed: u8, ordinal: u64, chain_id: &str) -> LeafFixture {
    let source_bytes = postcard::to_allocvec(&summary(seed, chain_id)).unwrap();
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

fn subtree(children: &[LeafFixture]) -> DisclosedStructuralLevelOneV1 {
    let child_journal_bytes = children
        .iter()
        .map(|child| encode_node_journal_v3(&child.journal).unwrap())
        .collect();
    let level_one = recompose_expected_structural_aggregate_v1(
        &StructuralAggregateInputV1 {
            expected_self_image_id: LEVEL_ONE_IMAGE_ID,
            child_journal_bytes,
        },
        StructuralAggregatePolicyV1::level_one_adapter_children(ADAPTER_IMAGE_ID),
    )
    .unwrap()
    .journal;
    DisclosedStructuralLevelOneV1::new(
        encode_node_journal_v3(&level_one).unwrap(),
        children
            .iter()
            .map(|child| child.disclosure.clone())
            .collect(),
    )
    .unwrap()
}

fn composition_input(
    groups: &[&[LeafFixture]],
) -> Result<SemanticEpochCompositionInputV1, SemanticEpochCompositionErrorV1> {
    let subtrees = groups.iter().map(|group| subtree(group)).collect();
    let recomposition = SemanticRecompositionInputV1::new(subtrees)
        .map_err(SemanticEpochCompositionErrorV1::SemanticRecomposition)?;
    SemanticEpochCompositionInputV1::new(SEMANTIC_IMAGE_ID, recomposition)
}

fn policy() -> SemanticEpochCompositionPolicyV1 {
    SemanticEpochCompositionPolicyV1::new(ADAPTER_IMAGE_ID, LEVEL_ONE_IMAGE_ID, LEVEL_TWO_IMAGE_ID)
        .unwrap()
}

#[test]
fn semantic_root_is_grouping_independent_while_proof_tree_root_binds_grouping() {
    let leaves = [
        leaf(1, 0, "semantic-epoch-test"),
        leaf(2, 1, "semantic-epoch-test"),
        leaf(3, 2, "semantic-epoch-test"),
        leaf(4, 3, "semantic-epoch-test"),
    ];
    let two_by_two = recompose_expected_semantic_epoch_v1(
        &composition_input(&[&leaves[0..2], &leaves[2..4]]).unwrap(),
        policy(),
    )
    .unwrap();
    let one_by_three = recompose_expected_semantic_epoch_v1(
        &composition_input(&[&leaves[0..1], &leaves[1..4]]).unwrap(),
        policy(),
    )
    .unwrap();

    assert_eq!(
        two_by_two.proposal().semantic_epoch_root(),
        one_by_three.proposal().semantic_epoch_root()
    );
    assert_ne!(
        two_by_two.proposal().proof_tree_root(),
        one_by_three.proposal().proof_tree_root()
    );
    assert_eq!(
        two_by_two.proposal().proof_tree_root(),
        two_by_two
            .structural_level_two_journal()
            .canonical_hash()
            .unwrap()
    );
}

#[test]
fn proposal_manifest_binds_semantic_adapter_and_both_structural_programs() {
    let leaves = [
        leaf(1, 0, "semantic-manifest-test"),
        leaf(2, 1, "semantic-manifest-test"),
    ];
    let projection = compose_semantic_epoch_after_level_one_verification_v1(
        &composition_input(&[&leaves[0..1], &leaves[1..2]]).unwrap(),
        policy(),
    )
    .unwrap();
    let dependencies =
        SemanticEpochDependencyProgramsV1::new(SemanticEpochDependencyProgramsInputV1 {
            adapter_program_id: program_id_from_risc0_words_v3(ADAPTER_IMAGE_ID).unwrap(),
            level_one_program_id: program_id_from_risc0_words_v3(LEVEL_ONE_IMAGE_ID).unwrap(),
            level_two_program_id: program_id_from_risc0_words_v3(LEVEL_TWO_IMAGE_ID).unwrap(),
        });
    let semantic_program = program_id_from_risc0_words_v3(SEMANTIC_IMAGE_ID).unwrap();

    assert_eq!(projection.proposal().actual_program_id(), semantic_program);
    assert_eq!(
        projection.proposal().program_manifest_root(),
        semantic_epoch_manifest_root_v1(semantic_program, &dependencies).unwrap()
    );
}

#[test]
fn cross_subtree_scope_mismatch_rejects_before_epoch_proposal_construction() {
    let left = [
        leaf(1, 0, "semantic-scope-a"),
        leaf(2, 1, "semantic-scope-a"),
    ];
    let right = [
        leaf(3, 2, "semantic-scope-b"),
        leaf(4, 3, "semantic-scope-b"),
    ];
    assert_eq!(
        recompose_expected_semantic_epoch_v1(
            &composition_input(&[&left, &right]).unwrap(),
            policy(),
        ),
        Err(SemanticEpochCompositionErrorV1::StructuralLevelTwo(
            StructuralAggregateErrorV1::Protocol(ZrpfErrorV3::ScopeMismatch),
        ))
    );
}

#[test]
fn zero_program_ids_reject_at_policy_and_input_construction() {
    assert_eq!(
        SemanticEpochCompositionPolicyV1::new([0; 8], LEVEL_ONE_IMAGE_ID, LEVEL_TWO_IMAGE_ID,),
        Err(SemanticEpochCompositionErrorV1::SemanticRecomposition(
            SemanticRecompositionErrorV1::ZeroAdapterImageId,
        ))
    );
    assert_eq!(
        SemanticEpochCompositionPolicyV1::new(ADAPTER_IMAGE_ID, [0; 8], LEVEL_TWO_IMAGE_ID),
        Err(SemanticEpochCompositionErrorV1::SemanticRecomposition(
            SemanticRecompositionErrorV1::ZeroLevelOneImageId,
        ))
    );
    assert_eq!(
        SemanticEpochCompositionPolicyV1::new(ADAPTER_IMAGE_ID, LEVEL_ONE_IMAGE_ID, [0; 8]),
        Err(SemanticEpochCompositionErrorV1::ZeroLevelTwoImageId)
    );

    let leaf = leaf(1, 0, "semantic-zero-self-test");
    let recomposition = SemanticRecompositionInputV1::new(vec![subtree(&[leaf])]).unwrap();
    assert_eq!(
        SemanticEpochCompositionInputV1::new([0; 8], recomposition),
        Err(SemanticEpochCompositionErrorV1::ZeroSemanticImageId)
    );
}
