#![allow(dead_code)]

use zenodex_zrpf_protocol_v3::{
    encode_node_journal_v3, encode_node_journal_v4, AggregateNodeInputV3, ApplicationIdV3,
    CommitmentV3, DomainIdV3, LeafNodeInputV3, NodeCommitmentsInputV3, NodeCommitmentsV3,
    NodeJournalInputV4, NodeJournalV3, NodeJournalV4, NodeScopeInputV3, NodeScopeV3, PartitionV3,
    ProfileIdV3, ProgramIdV3, ProjectedChildDescriptorV3, SemanticAssetFlowInputV2,
    SemanticAssetFlowV2, SemanticSubtreeInputV2, SemanticSubtreeV2, SemanticValueLeafRecordInputV2,
    SemanticValueLeafRecordV2, TaskIdV3,
};
use zenodex_zrpf_risc0_value_aggregate_shared::{
    GovernedValueChildIdentityV5, ValueAggregateRecompositionPolicyV5,
};

pub fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

pub fn indexed(prefix: u8, index: u64) -> CommitmentV3 {
    let mut bytes = [prefix.max(1); 32];
    bytes[24..].copy_from_slice(&index.to_be_bytes());
    CommitmentV3::new(bytes).unwrap()
}

pub fn image(seed: u32) -> [u32; 8] {
    core::array::from_fn(|index| seed + u32::try_from(index).unwrap() + 1)
}

pub fn program_from_image(image: [u32; 8]) -> ProgramIdV3 {
    let mut bytes = [0u8; 32];
    for (chunk, word) in bytes.chunks_exact_mut(4).zip(image) {
        chunk.copy_from_slice(&word.to_le_bytes());
    }
    ProgramIdV3::new(bytes).unwrap()
}

pub fn identity(
    image_seed: u32,
    profile_seed: u8,
    manifest_seed: u8,
) -> GovernedValueChildIdentityV5 {
    let image = image(image_seed);
    GovernedValueChildIdentityV5::new(
        image,
        program_from_image(image),
        ProfileIdV3::new([profile_seed; 32]).unwrap(),
        commitment(manifest_seed),
    )
    .unwrap()
}

pub fn scope() -> NodeScopeV3 {
    scope_with_application(1)
}

pub fn scope_with_application(application_seed: u8) -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([application_seed; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        epoch_start: 41,
        epoch_end: 41,
        public_policy_hash: commitment(3),
        feature_suite_hash: commitment(4),
        dependency_lock_hash: commitment(5),
        toolchain_lock_hash: commitment(6),
    })
    .unwrap()
}

pub fn policy(
    scope: NodeScopeV3,
    identities: Vec<GovernedValueChildIdentityV5>,
) -> ValueAggregateRecompositionPolicyV5 {
    ValueAggregateRecompositionPolicyV5::new(scope, identities).unwrap()
}

pub fn leaf_bytes(
    ordinal: u64,
    raw_pre: CommitmentV3,
    raw_post: CommitmentV3,
    scope: NodeScopeV3,
    identity: GovernedValueChildIdentityV5,
) -> Vec<u8> {
    encode_node_journal_v4(&leaf_journal(
        ordinal, ordinal, raw_pre, raw_post, scope, identity,
    ))
    .unwrap()
}

pub fn leaf_journal(
    ordinal: u64,
    record_identity: u64,
    raw_pre: CommitmentV3,
    raw_post: CommitmentV3,
    scope: NodeScopeV3,
    identity: GovernedValueChildIdentityV5,
) -> NodeJournalV4 {
    let structural = structural_leaf(ordinal, scope.clone());
    NodeJournalV4::new(NodeJournalInputV4 {
        structural,
        semantic_subtree: subtree(
            ordinal,
            record_identity,
            raw_pre,
            raw_post,
            scope.canonical_hash().unwrap(),
        ),
        application_statement_hash: indexed(40, record_identity),
        proof_profile_id: identity.expected_profile_id(),
        actual_program_id: identity.expected_program_id(),
        proof_system_id: commitment(42),
        receipt_security_profile_id: commitment(43),
        verifier_parameters_root: commitment(44),
        program_manifest_root: identity.expected_manifest_root(),
        child_semantic_journal_hashes: vec![],
    })
    .unwrap()
}

pub fn aggregate_v4_bytes(
    start: u64,
    scope: NodeScopeV3,
    identity: GovernedValueChildIdentityV5,
) -> Vec<u8> {
    let left = structural_leaf(start, scope.clone());
    let right = structural_leaf(start + 1, scope.clone());
    let structural = NodeJournalV3::new_aggregate(AggregateNodeInputV3 {
        children: vec![descriptor(&left, 91), descriptor(&right, 92)],
        task_id: task(90, start),
        count_unit_id: commitment(9),
        scope: scope.clone(),
        proof_profile_id: ProfileIdV3::new([93; 32]).unwrap(),
        actual_program_id: ProgramIdV3::new([94; 32]).unwrap(),
        node_statement_hash: commitment(95),
        program_manifest_root: commitment(96),
        commitments: commitments(97),
    })
    .unwrap();
    let first = record(start, start, indexed(60, start), indexed(60, start + 1));
    let second = record(
        start + 1,
        start + 1,
        indexed(60, start + 1),
        indexed(60, start + 2),
    );
    let semantic_subtree = SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: commitment(20),
        accounting_domain_id: commitment(21),
        atoms_unit_id: commitment(22),
        state_root_scheme_id: commitment(23),
        scope_hash: scope.canonical_hash().unwrap(),
        lane_id_hash: commitment(24),
        partition: PartitionV3::new(start, start + 2).unwrap(),
        raw_subtree_pre_state_root: indexed(60, start),
        raw_subtree_post_state_root: indexed(60, start + 2),
        represented_row_count: 2,
        leaf_records: vec![first, second],
        authority_grants_root: commitment(25),
        asset_flows: vec![flow(2)],
        authority_uses: vec![],
    })
    .unwrap();
    encode_node_journal_v4(
        &NodeJournalV4::new(NodeJournalInputV4 {
            structural,
            semantic_subtree,
            application_statement_hash: commitment(40),
            proof_profile_id: identity.expected_profile_id(),
            actual_program_id: identity.expected_program_id(),
            proof_system_id: commitment(42),
            receipt_security_profile_id: commitment(43),
            verifier_parameters_root: commitment(44),
            program_manifest_root: identity.expected_manifest_root(),
            child_semantic_journal_hashes: vec![commitment(98), commitment(99)],
        })
        .unwrap(),
    )
    .unwrap()
}

fn structural_leaf(ordinal: u64, scope: NodeScopeV3) -> NodeJournalV3 {
    NodeJournalV3::new_leaf(LeafNodeInputV3 {
        task_id: task(8, ordinal),
        partition: PartitionV3::new(ordinal, ordinal + 1).unwrap(),
        operation_count: 1,
        count_unit_id: commitment(9),
        scope,
        proof_profile_id: ProfileIdV3::new([10; 32]).unwrap(),
        actual_program_id: ProgramIdV3::new([11; 32]).unwrap(),
        node_statement_hash: indexed(12, ordinal),
        program_manifest_root: commitment(13),
        commitments: commitments(14),
    })
    .unwrap()
}

fn descriptor(journal: &NodeJournalV3, seed: u8) -> ProjectedChildDescriptorV3 {
    ProjectedChildDescriptorV3::project_canonical_journal(
        commitment(seed),
        &encode_node_journal_v3(journal).unwrap(),
    )
    .unwrap()
}

fn subtree(
    ordinal: u64,
    record_identity: u64,
    raw_pre: CommitmentV3,
    raw_post: CommitmentV3,
    scope_hash: CommitmentV3,
) -> SemanticSubtreeV2 {
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: commitment(20),
        accounting_domain_id: commitment(21),
        atoms_unit_id: commitment(22),
        state_root_scheme_id: commitment(23),
        scope_hash,
        lane_id_hash: commitment(24),
        partition: PartitionV3::new(ordinal, ordinal + 1).unwrap(),
        raw_subtree_pre_state_root: raw_pre,
        raw_subtree_post_state_root: raw_post,
        represented_row_count: 1,
        leaf_records: vec![record(ordinal, record_identity, raw_pre, raw_post)],
        authority_grants_root: commitment(25),
        asset_flows: vec![flow(1)],
        authority_uses: vec![],
    })
    .unwrap()
}

fn record(
    ordinal: u64,
    identity: u64,
    raw_pre: CommitmentV3,
    raw_post: CommitmentV3,
) -> SemanticValueLeafRecordV2 {
    SemanticValueLeafRecordV2::new(SemanticValueLeafRecordInputV2 {
        partition: PartitionV3::new(ordinal, ordinal + 1).unwrap(),
        semantic_leaf_hash: indexed(30, identity),
        source_claim_id: indexed(31, identity),
        semantic_source_id: indexed(32, identity),
        task_id: task(33, identity),
        pre_state_vector_root: indexed(34, identity),
        post_state_vector_root: indexed(35, identity),
        transaction_root: indexed(36, identity),
        effect_root: indexed(37, identity),
        asset_delta_root: indexed(38, identity),
        raw_pre_state_root: raw_pre,
        raw_post_state_root: raw_post,
    })
    .unwrap()
}

fn flow(multiplier: u128) -> SemanticAssetFlowV2 {
    SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
        asset_id: [1; 32],
        outflow_atoms: multiplier,
        inflow_atoms: multiplier,
        issued_atoms: 0,
        destroyed_atoms: 0,
    })
    .unwrap()
}

fn task(prefix: u8, index: u64) -> TaskIdV3 {
    TaskIdV3::new(indexed(prefix, index).into_bytes()).unwrap()
}

fn commitments(seed: u8) -> NodeCommitmentsV3 {
    let root = |field: u8| {
        let mut bytes = [seed.max(1); 32];
        bytes[0] = field.max(1);
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
