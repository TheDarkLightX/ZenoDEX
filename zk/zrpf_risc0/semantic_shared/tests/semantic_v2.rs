use tau_state_proof_risc0_shared::{
    recursive_cross_shard_messages_root_v1, recursive_receipt_ids_root_v1,
    RecursiveEffectSummaryV1, RECURSIVE_SPOT_LEAF_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, semantic_epoch_dependency_manifest_root_v2, NodeJournalV3,
    SemanticEpochDependencyProgramsInputV1, SemanticEpochDependencyProgramsV1,
    V1AdapterSemanticLeafOpeningV1, MAX_IMMEDIATE_CHILDREN_V3, MAX_NODE_JOURNAL_BYTES_V3,
};
use zenodex_zrpf_risc0_aggregate_shared::{
    recompose_expected_structural_aggregate_v1, StructuralAggregateInputV1,
    StructuralAggregatePolicyV1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    bind_semantic_guest_input_after_level_one_verification_v2,
    compose_semantic_epoch_after_level_one_verification_v2, decode_exact_semantic_guest_input_v2,
    encode_semantic_guest_input_v2, DisclosedStructuralLevelOneV1, DisclosedV1AdapterLeafV1,
    SemanticEpochCompositionInputV2, SemanticEpochCompositionPolicyV2, SemanticGuestInputV2,
    SemanticGuestLeafDisclosureV1, SemanticGuestLevelOneDisclosureV1, SemanticRecompositionInputV1,
    MAX_SEMANTIC_GUEST_INPUT_BYTES_V2,
};
#[cfg(feature = "historical-v1")]
use zenodex_zrpf_risc0_semantic_shared::{
    compose_semantic_epoch_after_level_one_verification_v1, decode_exact_semantic_guest_input_v1,
    encode_semantic_guest_input_v1, SemanticEpochCompositionInputV1,
    SemanticEpochCompositionPolicyV1, SemanticGuestInputV1,
};
use zenodex_zrpf_risc0_shared::{
    program_id_from_risc0_words_v3, project_policy_bound_v1_journal, SourceKindV1,
    PINNED_SPOT_LEAF_IMAGE_ID_V1,
};

const ADAPTER_IMAGE_ID: [u32; 8] = [31, 32, 33, 34, 35, 36, 37, 38];
const LEVEL_ONE_IMAGE_ID: [u32; 8] = [41, 42, 43, 44, 45, 46, 47, 48];
const LEVEL_TWO_IMAGE_ID: [u32; 8] = [51, 52, 53, 54, 55, 56, 57, 58];
#[cfg(feature = "historical-v1")]
const LEGACY_SEMANTIC_IMAGE_ID: [u32; 8] = [61, 62, 63, 64, 65, 66, 67, 68];

fn root(seed: u8) -> [u8; 32] {
    [seed; 32]
}

fn summary(seed: u8, chain_id: &str) -> RecursiveEffectSummaryV1 {
    let empty_receipts = recursive_receipt_ids_root_v1(&[]).unwrap();
    let empty_messages = recursive_cross_shard_messages_root_v1(&[]).unwrap();
    RecursiveEffectSummaryV1 {
        summary_version: 1,
        lane_id: format!("spot-semantic-v2-{seed}"),
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

fn recomposition(groups: &[&[LeafFixture]]) -> SemanticRecompositionInputV1 {
    SemanticRecompositionInputV1::new(groups.iter().map(|group| subtree(group)).collect()).unwrap()
}

#[cfg(feature = "historical-v1")]
fn policy_v1() -> SemanticEpochCompositionPolicyV1 {
    SemanticEpochCompositionPolicyV1::new(ADAPTER_IMAGE_ID, LEVEL_ONE_IMAGE_ID, LEVEL_TWO_IMAGE_ID)
        .unwrap()
}

fn policy_v2() -> SemanticEpochCompositionPolicyV2 {
    SemanticEpochCompositionPolicyV2::new(ADAPTER_IMAGE_ID, LEVEL_ONE_IMAGE_ID, LEVEL_TWO_IMAGE_ID)
        .unwrap()
}

fn dependency_programs() -> SemanticEpochDependencyProgramsV1 {
    SemanticEpochDependencyProgramsV1::new(SemanticEpochDependencyProgramsInputV1 {
        adapter_program_id: program_id_from_risc0_words_v3(ADAPTER_IMAGE_ID).unwrap(),
        level_one_program_id: program_id_from_risc0_words_v3(LEVEL_ONE_IMAGE_ID).unwrap(),
        level_two_program_id: program_id_from_risc0_words_v3(LEVEL_TWO_IMAGE_ID).unwrap(),
    })
}

#[test]
fn v2_guest_codec_has_no_runtime_self_image_and_rejects_truncation() {
    let raw_group = SemanticGuestLevelOneDisclosureV1::new(
        vec![1, 2, 3],
        vec![SemanticGuestLeafDisclosureV1::new(vec![4, 5], [6; 32]).unwrap()],
    )
    .unwrap();
    let current = SemanticGuestInputV2::new(vec![raw_group]).unwrap();
    let current_bytes = encode_semantic_guest_input_v2(&current).unwrap();

    assert_eq!(&current_bytes[..3], &[0, 2, 1]);
    assert_eq!(
        decode_exact_semantic_guest_input_v2(&current_bytes).unwrap(),
        current
    );
    for length in 0..current_bytes.len() {
        assert!(decode_exact_semantic_guest_input_v2(&current_bytes[..length]).is_err());
    }
    assert_eq!(MAX_SEMANTIC_GUEST_INPUT_BYTES_V2, 297_115);
    let mut trailing = current_bytes;
    trailing.push(0);
    assert_eq!(
        decode_exact_semantic_guest_input_v2(&trailing),
        Err(zenodex_zrpf_risc0_semantic_shared::SemanticGuestInputErrorV2::TrailingBytes)
    );
}

#[cfg(feature = "historical-v1")]
#[test]
fn v1_and_v2_guest_codecs_reject_each_others_bytes() {
    let raw_group = SemanticGuestLevelOneDisclosureV1::new(
        vec![1, 2, 3],
        vec![SemanticGuestLeafDisclosureV1::new(vec![4, 5], [6; 32]).unwrap()],
    )
    .unwrap();
    let current = SemanticGuestInputV2::new(vec![raw_group.clone()]).unwrap();
    let legacy = SemanticGuestInputV1::new(LEGACY_SEMANTIC_IMAGE_ID, vec![raw_group]).unwrap();
    let current_bytes = encode_semantic_guest_input_v2(&current).unwrap();
    let legacy_bytes = encode_semantic_guest_input_v1(&legacy).unwrap();

    assert!(decode_exact_semantic_guest_input_v1(&current_bytes).is_err());
    assert!(decode_exact_semantic_guest_input_v2(&legacy_bytes).is_err());
}

#[test]
fn v2_guest_codec_exact_maximum_matches_the_declared_bound() {
    let maximal_leaf =
        || SemanticGuestLeafDisclosureV1::new(vec![1; MAX_NODE_JOURNAL_BYTES_V3], [2; 32]).unwrap();
    let maximal_group = || {
        SemanticGuestLevelOneDisclosureV1::new(
            vec![3; MAX_NODE_JOURNAL_BYTES_V3],
            (0..MAX_IMMEDIATE_CHILDREN_V3)
                .map(|_| maximal_leaf())
                .collect(),
        )
        .unwrap()
    };
    let maximal = SemanticGuestInputV2::new(
        (0..MAX_IMMEDIATE_CHILDREN_V3)
            .map(|_| maximal_group())
            .collect(),
    )
    .unwrap();
    let encoded = encode_semantic_guest_input_v2(&maximal).unwrap();

    assert_eq!(encoded.len(), MAX_SEMANTIC_GUEST_INPUT_BYTES_V2);
    assert_eq!(
        decode_exact_semantic_guest_input_v2(&encoded).unwrap(),
        maximal
    );
    assert!(
        decode_exact_semantic_guest_input_v2(&vec![0; MAX_SEMANTIC_GUEST_INPUT_BYTES_V2 + 1])
            .is_err()
    );
}

#[test]
fn v2_composition_derives_the_governed_dependency_manifest() {
    let leaves = [
        leaf(1, 0, "semantic-v2-composition"),
        leaf(2, 1, "semantic-v2-composition"),
        leaf(3, 2, "semantic-v2-composition"),
    ];
    let v2 = compose_semantic_epoch_after_level_one_verification_v2(
        &SemanticEpochCompositionInputV2::new(recomposition(&[&leaves[0..2], &leaves[2..3]])),
        policy_v2(),
    )
    .unwrap();

    assert_eq!(v2.proposal().leaf_count(), 3);
    assert_eq!(v2.proposal().operation_count(), 3);
    assert_eq!(
        v2.proposal().dependency_manifest_root(),
        semantic_epoch_dependency_manifest_root_v2(&dependency_programs()).unwrap()
    );
}

#[cfg(feature = "historical-v1")]
#[test]
fn v2_composition_preserves_v1_semantic_root_without_accepting_runtime_identity() {
    let leaves = [
        leaf(1, 0, "semantic-v2-equivalence"),
        leaf(2, 1, "semantic-v2-equivalence"),
        leaf(3, 2, "semantic-v2-equivalence"),
    ];
    let v1 = compose_semantic_epoch_after_level_one_verification_v1(
        &SemanticEpochCompositionInputV1::new(
            LEGACY_SEMANTIC_IMAGE_ID,
            recomposition(&[&leaves[0..2], &leaves[2..3]]),
        )
        .unwrap(),
        policy_v1(),
    )
    .unwrap();
    let v2 = compose_semantic_epoch_after_level_one_verification_v2(
        &SemanticEpochCompositionInputV2::new(recomposition(&[&leaves[0..2], &leaves[2..3]])),
        policy_v2(),
    )
    .unwrap();

    assert_eq!(
        v2.proposal().semantic_epoch_root(),
        v1.proposal().semantic_epoch_root()
    );
    assert_eq!(
        v2.proposal().proof_tree_root(),
        v1.proposal().proof_tree_root()
    );
    assert_eq!(
        v2.proposal().dependency_manifest_root(),
        semantic_epoch_dependency_manifest_root_v2(&dependency_programs()).unwrap()
    );
}

#[test]
fn v2_binding_carries_only_verified_disclosures_into_composition() {
    let group = SemanticGuestLevelOneDisclosureV1::new(
        vec![7, 8],
        vec![SemanticGuestLeafDisclosureV1::new(vec![9], [10; 32]).unwrap()],
    )
    .unwrap();
    let raw = SemanticGuestInputV2::new(vec![group]).unwrap();
    let bound = bind_semantic_guest_input_after_level_one_verification_v2(&raw).unwrap();

    assert_eq!(bound.recomposition().level_one_nodes().len(), 1);
    assert_eq!(
        bound.recomposition().level_one_nodes()[0].adapter_leaves()[0]
            .semantic_opening()
            .semantic_source_binding_hash()
            .as_bytes(),
        &[10; 32]
    );
}
