#[path = "support/value_aggregate_v5_mirror.rs"]
mod mirror;

use zenodex_zrpf_protocol_v3::{
    decode_exact_value_aggregate_proposal_v5, encode_value_aggregate_proposal_v5, ApplicationIdV3,
    CommitmentV3, DomainIdV3, NodeScopeInputV3, NodeScopeV3, PartitionV3, ProfileIdV3, ProgramIdV3,
    ProposedValueAggregateV5, SemanticAssetFlowInputV2, SemanticAssetFlowV2,
    SemanticSubtreeInputV2, SemanticSubtreeV2, SemanticValueLeafRecordInputV2,
    SemanticValueLeafRecordV2, TaskIdV3, ValueAggregateChildDescriptorInputV5,
    ValueAggregateChildDescriptorV5, ValueAggregateErrorV5,
    ValueAggregateOperationalCommitmentsInputV5, ValueAggregateOperationalCommitmentsV5,
    ValueAggregateProposalInputV5, MAX_IMMEDIATE_CHILDREN_V3, MAX_LEAF_COUNT_V3,
    MAX_SEMANTIC_VALUE_RECORDS_V2, MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5,
    VALUE_AGGREGATE_PROPOSAL_VERSION_V5,
};

use mirror::{mirror_descriptor_hash, mirror_proposal, mirror_root};

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

fn indexed(prefix: u8, index: u64) -> CommitmentV3 {
    let mut bytes = [prefix.max(1); 32];
    bytes[24..].copy_from_slice(&index.to_be_bytes());
    CommitmentV3::new(bytes).unwrap()
}

fn scope() -> NodeScopeV3 {
    scope_for_epoch(19, 19)
}

fn scope_for_epoch(start: u64, end: u64) -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([1; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        epoch_start: start,
        epoch_end: end,
        public_policy_hash: commitment(3),
        feature_suite_hash: commitment(4),
        dependency_lock_hash: commitment(5),
        toolchain_lock_hash: commitment(6),
    })
    .unwrap()
}

fn record(index: u64, raw_pre: CommitmentV3, raw_post: CommitmentV3) -> SemanticValueLeafRecordV2 {
    SemanticValueLeafRecordV2::new(SemanticValueLeafRecordInputV2 {
        partition: PartitionV3::new(index, index + 1).unwrap(),
        semantic_leaf_hash: indexed(10, index),
        source_claim_id: indexed(11, index),
        semantic_source_id: indexed(12, index),
        task_id: TaskIdV3::new(indexed(13, index).into_bytes()).unwrap(),
        pre_state_vector_root: indexed(14, index),
        post_state_vector_root: indexed(15, index),
        transaction_root: indexed(16, index),
        effect_root: indexed(17, index),
        asset_delta_root: indexed(18, index),
        raw_pre_state_root: raw_pre,
        raw_post_state_root: raw_post,
    })
    .unwrap()
}

fn subtree(count: u64) -> SemanticSubtreeV2 {
    subtree_range(0, count)
}

fn subtree_range(start: u64, count: u64) -> SemanticSubtreeV2 {
    let end = start.checked_add(count).unwrap();
    let records = (start..end)
        .map(|index| record(index, indexed(30, index), indexed(30, index + 1)))
        .collect::<Vec<_>>();
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: commitment(31),
        accounting_domain_id: commitment(32),
        atoms_unit_id: commitment(33),
        state_root_scheme_id: commitment(34),
        scope_hash: scope().canonical_hash().unwrap(),
        lane_id_hash: commitment(35),
        partition: PartitionV3::new(start, end).unwrap(),
        raw_subtree_pre_state_root: indexed(30, start),
        raw_subtree_post_state_root: indexed(30, end),
        represented_row_count: count,
        leaf_records: records,
        authority_grants_root: commitment(36),
        asset_flows: vec![SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
            asset_id: [37; 32],
            outflow_atoms: u128::from(count),
            inflow_atoms: u128::from(count),
            issued_atoms: 0,
            destroyed_atoms: 0,
        })
        .unwrap()],
        authority_uses: vec![],
    })
    .unwrap()
}

fn child(index: u64, level: u8) -> ValueAggregateChildDescriptorV5 {
    child_partition(index, index + 1, index, level)
}

fn child_partition(
    start: u64,
    end_exclusive: u64,
    identity_index: u64,
    level: u8,
) -> ValueAggregateChildDescriptorV5 {
    ValueAggregateChildDescriptorV5::new(ValueAggregateChildDescriptorInputV5 {
        child_level: level,
        partition: PartitionV3::new(start, end_exclusive).unwrap(),
        verified_program_id: ProgramIdV3::new([40; 32]).unwrap(),
        proof_profile_id: ProfileIdV3::new([41; 32]).unwrap(),
        program_manifest_root: commitment(42),
        journal_hash: indexed(43, identity_index),
        claim_binding: indexed(44, identity_index),
        semantic_subtree_root: indexed(45, identity_index),
        operational_commitments: operational(identity_index),
    })
    .unwrap()
}

fn saturated_eight_by_eight_proposals() -> (Vec<ProposedValueAggregateV5>, ProposedValueAggregateV5)
{
    let fanout = u64::try_from(MAX_IMMEDIATE_CHILDREN_V3).unwrap();
    let mut level_one = Vec::with_capacity(MAX_IMMEDIATE_CHILDREN_V3);
    let mut root_children = Vec::with_capacity(MAX_IMMEDIATE_CHILDREN_V3);
    for subtree_index in 0..fanout {
        let start = subtree_index * fanout;
        let end = start + fanout;
        let proposal = ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
            aggregate_level: 1,
            scope: scope(),
            semantic_subtree: subtree_range(start, fanout),
            children: (start..end).map(|index| child(index, 0)).collect(),
        })
        .unwrap();
        root_children.push(
            ValueAggregateChildDescriptorV5::new(ValueAggregateChildDescriptorInputV5 {
                child_level: 1,
                partition: PartitionV3::new(start, end).unwrap(),
                verified_program_id: ProgramIdV3::new([60; 32]).unwrap(),
                proof_profile_id: ProfileIdV3::new([61; 32]).unwrap(),
                program_manifest_root: commitment(62),
                journal_hash: proposal.proposal_commitment(),
                claim_binding: indexed(63, subtree_index),
                semantic_subtree_root: proposal.semantic_subtree().canonical_hash().unwrap(),
                operational_commitments: proposal.operational_commitments(),
            })
            .unwrap(),
        );
        level_one.push(proposal);
    }
    let root = ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
        aggregate_level: 2,
        scope: scope(),
        semantic_subtree: subtree_range(0, MAX_LEAF_COUNT_V3),
        children: root_children,
    })
    .unwrap();
    (level_one, root)
}

fn operational(index: u64) -> ValueAggregateOperationalCommitmentsV5 {
    ValueAggregateOperationalCommitmentsV5::new(ValueAggregateOperationalCommitmentsInputV5 {
        data_availability_root: indexed(46, index),
        data_availability_certificate_root: indexed(47, index),
        conflict_schedule_root: indexed(48, index),
        cross_lane_outbox_root: indexed(49, index),
        cross_lane_inbox_root: indexed(50, index),
        cross_lane_message_ids_root: indexed(51, index),
        carry_queue_pre_root: indexed(52, index),
        carry_queue_post_root: indexed(53, index),
    })
    .unwrap()
}

fn proposal() -> ProposedValueAggregateV5 {
    ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
        aggregate_level: 1,
        scope: scope(),
        semantic_subtree: subtree(2),
        children: vec![child(0, 0), child(1, 0)],
    })
    .unwrap()
}

#[test]
fn exact_codec_roundtrips_bounded_proof_neutral_proposal() {
    let proposal = proposal();
    let bytes = encode_value_aggregate_proposal_v5(&proposal).unwrap();
    assert!(bytes.len() <= MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5);
    assert_eq!(
        decode_exact_value_aggregate_proposal_v5(&bytes).unwrap(),
        proposal
    );
    assert_eq!(
        proposal.proposal_version(),
        VALUE_AGGREGATE_PROPOSAL_VERSION_V5
    );
    assert_eq!(proposal.aggregate_level(), 1);
    assert_eq!(proposal.children().len(), 2);
    assert_eq!(proposal.scope().application_id().into_bytes(), [1; 32]);
    assert_eq!(proposal.scope().chain_or_domain_id().into_bytes(), [2; 32]);
}

#[test]
fn saturated_eight_by_eight_value_tree_is_deterministic_and_codec_bounded() {
    assert_eq!(
        usize::try_from(MAX_LEAF_COUNT_V3).unwrap(),
        MAX_SEMANTIC_VALUE_RECORDS_V2
    );
    let (level_one, root) = saturated_eight_by_eight_proposals();
    let (repeated_level_one, repeated_root) = saturated_eight_by_eight_proposals();

    assert_eq!(level_one.len(), MAX_IMMEDIATE_CHILDREN_V3);
    assert_eq!(level_one, repeated_level_one);
    for proposal in &level_one {
        assert_eq!(proposal.aggregate_level(), 1);
        assert_eq!(proposal.children().len(), MAX_IMMEDIATE_CHILDREN_V3);
        assert_eq!(
            proposal.semantic_subtree().leaf_count(),
            u64::try_from(MAX_IMMEDIATE_CHILDREN_V3).unwrap()
        );
    }
    assert_eq!(root, repeated_root);
    assert_eq!(root.aggregate_level(), 2);
    assert_eq!(root.children().len(), MAX_IMMEDIATE_CHILDREN_V3);
    assert_eq!(root.semantic_subtree().leaf_count(), MAX_LEAF_COUNT_V3);
    assert_eq!(
        root.semantic_subtree().represented_row_count(),
        MAX_LEAF_COUNT_V3
    );
    assert_eq!(
        root.semantic_subtree().partition(),
        PartitionV3::new(0, MAX_LEAF_COUNT_V3).unwrap()
    );
    assert_eq!(root.proposal_commitment(), mirror_proposal(&root));

    let encoded = encode_value_aggregate_proposal_v5(&root).unwrap();
    let repeated_encoded = encode_value_aggregate_proposal_v5(&repeated_root).unwrap();
    assert_eq!(encoded, repeated_encoded);
    assert!(encoded.len() <= MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5);
    assert_eq!(
        decode_exact_value_aggregate_proposal_v5(&encoded).unwrap(),
        root
    );
}

#[test]
fn proposal_roots_and_commitment_match_independent_fixed_width_mirror() {
    let proposal = proposal();
    let descriptor_hashes = proposal
        .children()
        .iter()
        .map(mirror_descriptor_hash)
        .collect::<Vec<_>>();
    assert_eq!(
        proposal.child_descriptors_root(),
        mirror_root(
            b"zenodex.zrpf.value_child_descriptors_root.v5",
            &descriptor_hashes
        )
    );
    assert_eq!(
        proposal.child_claims_root(),
        mirror_root(
            b"zenodex.zrpf.value_child_claims_root.v5",
            &proposal
                .children()
                .iter()
                .map(ValueAggregateChildDescriptorV5::claim_binding)
                .collect::<Vec<_>>()
        )
    );
    assert_eq!(
        proposal.child_journals_root(),
        mirror_root(
            b"zenodex.zrpf.value_child_journals_root.v5",
            &proposal
                .children()
                .iter()
                .map(ValueAggregateChildDescriptorV5::journal_hash)
                .collect::<Vec<_>>()
        )
    );
    assert_eq!(proposal.proposal_commitment(), mirror_proposal(&proposal));
}

#[test]
fn level_and_partition_contract_rejects_skips_gaps_and_multi_leaf_level_zero_children() {
    let base = subtree(2);
    for (level, children, expected) in [
        (
            0,
            vec![child(0, 0), child(1, 0)],
            ValueAggregateErrorV5::InvalidAggregateLevel(0),
        ),
        (
            1,
            vec![child(0, 1), child(1, 1)],
            ValueAggregateErrorV5::InvalidChildLevel {
                child: 0,
                actual: 1,
            },
        ),
    ] {
        assert_eq!(
            ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
                aggregate_level: level,
                scope: scope(),
                semantic_subtree: base.clone(),
                children,
            })
            .unwrap_err(),
            expected
        );
    }

    let mut gap = child(1, 0);
    let gap_json = serde_json::to_value(&gap).unwrap();
    let mut gap_json = gap_json.as_object().unwrap().clone();
    gap_json.insert(
        "partition".into(),
        serde_json::json!({"start": 2, "end_exclusive": 3}),
    );
    gap = serde_json::from_value(serde_json::Value::Object(gap_json)).unwrap();
    assert_eq!(
        ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
            aggregate_level: 1,
            scope: scope(),
            semantic_subtree: base,
            children: vec![child(0, 0), gap],
        })
        .unwrap_err(),
        ValueAggregateErrorV5::ChildPartitionGap { child: 1 }
    );
}

#[test]
fn duplicate_claim_or_journal_rejects_before_proposal_exists() {
    let first = child(0, 0);
    let second = child(1, 0);
    let duplicate_claim =
        ValueAggregateChildDescriptorV5::new(ValueAggregateChildDescriptorInputV5 {
            child_level: 0,
            partition: second.partition(),
            verified_program_id: second.verified_program_id(),
            proof_profile_id: second.proof_profile_id(),
            program_manifest_root: second.program_manifest_root(),
            journal_hash: second.journal_hash(),
            claim_binding: first.claim_binding(),
            semantic_subtree_root: second.semantic_subtree_root(),
            operational_commitments: second.operational_commitments(),
        })
        .unwrap();
    assert_eq!(
        ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
            aggregate_level: 1,
            scope: scope(),
            semantic_subtree: subtree(2),
            children: vec![first.clone(), duplicate_claim],
        })
        .unwrap_err(),
        ValueAggregateErrorV5::DuplicateChildClaim
    );

    let duplicate_journal =
        ValueAggregateChildDescriptorV5::new(ValueAggregateChildDescriptorInputV5 {
            child_level: 0,
            partition: second.partition(),
            verified_program_id: second.verified_program_id(),
            proof_profile_id: second.proof_profile_id(),
            program_manifest_root: second.program_manifest_root(),
            journal_hash: first.journal_hash(),
            claim_binding: second.claim_binding(),
            semantic_subtree_root: second.semantic_subtree_root(),
            operational_commitments: second.operational_commitments(),
        })
        .unwrap();
    assert_eq!(
        ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
            aggregate_level: 1,
            scope: scope(),
            semantic_subtree: subtree(2),
            children: vec![first, duplicate_journal],
        })
        .unwrap_err(),
        ValueAggregateErrorV5::DuplicateChildJournal
    );
}

#[test]
fn scope_and_epoch_are_closed_before_hashing() {
    assert_eq!(
        ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
            aggregate_level: 1,
            scope: scope_for_epoch(19, 20),
            semantic_subtree: subtree(2),
            children: vec![child(0, 0), child(1, 0)],
        })
        .unwrap_err(),
        ValueAggregateErrorV5::MultiEpochScope
    );

    let wrong_scope = NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([99; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        epoch_start: 19,
        epoch_end: 19,
        public_policy_hash: commitment(3),
        feature_suite_hash: commitment(4),
        dependency_lock_hash: commitment(5),
        toolchain_lock_hash: commitment(6),
    })
    .unwrap();
    assert_eq!(
        ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
            aggregate_level: 1,
            scope: wrong_scope,
            semantic_subtree: subtree(2),
            children: vec![child(0, 0), child(1, 0)],
        })
        .unwrap_err(),
        ValueAggregateErrorV5::ScopeHashMismatch
    );
}

#[test]
fn stored_root_substitution_unknown_fields_and_trailing_bytes_reject() {
    let proposal = proposal();
    let mut json = serde_json::to_value(&proposal).unwrap();
    json["child_claims_root"] = serde_json::to_value(commitment(250)).unwrap();
    assert!(serde_json::from_value::<ProposedValueAggregateV5>(json).is_err());

    let mut unknown = serde_json::to_value(&proposal).unwrap();
    unknown["verified"] = serde_json::json!(true);
    assert!(serde_json::from_value::<ProposedValueAggregateV5>(unknown).is_err());

    let mut encoded = encode_value_aggregate_proposal_v5(&proposal).unwrap();
    encoded.push(0);
    assert_eq!(
        decode_exact_value_aggregate_proposal_v5(&encoded).unwrap_err(),
        ValueAggregateErrorV5::TrailingBytes
    );
    assert!(matches!(
        decode_exact_value_aggregate_proposal_v5(&vec![
            0;
            MAX_VALUE_AGGREGATE_PROPOSAL_BYTES_V5 + 1
        ]),
        Err(ValueAggregateErrorV5::InputTooLarge { .. })
    ));
}
