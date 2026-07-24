#[path = "support/value_aggregate_v5_mirror.rs"]
mod mirror;

use zenodex_zrpf_protocol_v3::{
    aggregate_value_operational_commitments_v5, decode_exact_value_aggregate_proposal_v5,
    encode_value_aggregate_proposal_v5, ApplicationIdV3, CommitmentV3, DomainIdV3,
    NodeScopeInputV3, NodeScopeV3, PartitionV3, ProfileIdV3, ProgramIdV3, ProposedValueAggregateV5,
    SemanticAssetFlowInputV2, SemanticAssetFlowV2, SemanticSubtreeInputV2, SemanticSubtreeV2,
    SemanticValueLeafRecordInputV2, SemanticValueLeafRecordV2, TaskIdV3,
    ValueAggregateChildDescriptorInputV5, ValueAggregateChildDescriptorV5,
    ValueAggregateOperationalCommitmentsInputV5, ValueAggregateOperationalCommitmentsV5,
    ValueAggregateProposalInputV5,
};

use mirror::{mirror_operational_hash, mirror_proposal, mirror_root, operational_values};

const OPERATIONAL_FIELDS: [&str; 8] = [
    "data_availability_root",
    "data_availability_certificate_root",
    "conflict_schedule_root",
    "cross_lane_outbox_root",
    "cross_lane_inbox_root",
    "cross_lane_message_ids_root",
    "carry_queue_pre_root",
    "carry_queue_post_root",
];

fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

fn indexed(prefix: u8, index: u64) -> CommitmentV3 {
    let mut bytes = [prefix.max(1); 32];
    bytes[24..].copy_from_slice(&index.to_be_bytes());
    CommitmentV3::new(bytes).unwrap()
}

fn scope() -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([1; 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([2; 32]).unwrap(),
        epoch_start: 19,
        epoch_end: 19,
        public_policy_hash: commitment(3),
        feature_suite_hash: commitment(4),
        dependency_lock_hash: commitment(5),
        toolchain_lock_hash: commitment(6),
    })
    .unwrap()
}

fn operational(values: [CommitmentV3; 8]) -> ValueAggregateOperationalCommitmentsV5 {
    ValueAggregateOperationalCommitmentsV5::new(ValueAggregateOperationalCommitmentsInputV5 {
        data_availability_root: values[0],
        data_availability_certificate_root: values[1],
        conflict_schedule_root: values[2],
        cross_lane_outbox_root: values[3],
        cross_lane_inbox_root: values[4],
        cross_lane_message_ids_root: values[5],
        carry_queue_pre_root: values[6],
        carry_queue_post_root: values[7],
    })
    .unwrap()
}

fn child_operational(index: u64) -> ValueAggregateOperationalCommitmentsV5 {
    operational(core::array::from_fn(|field| {
        indexed(60 + u8::try_from(field).unwrap(), index)
    }))
}

fn record(index: u64) -> SemanticValueLeafRecordV2 {
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
        raw_pre_state_root: indexed(30, index),
        raw_post_state_root: indexed(30, index + 1),
    })
    .unwrap()
}

fn subtree() -> SemanticSubtreeV2 {
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: commitment(31),
        accounting_domain_id: commitment(32),
        atoms_unit_id: commitment(33),
        state_root_scheme_id: commitment(34),
        scope_hash: scope().canonical_hash().unwrap(),
        lane_id_hash: commitment(35),
        partition: PartitionV3::new(0, 2).unwrap(),
        raw_subtree_pre_state_root: indexed(30, 0),
        raw_subtree_post_state_root: indexed(30, 2),
        represented_row_count: 2,
        leaf_records: vec![record(0), record(1)],
        authority_grants_root: commitment(36),
        asset_flows: vec![SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
            asset_id: [37; 32],
            outflow_atoms: 2,
            inflow_atoms: 2,
            issued_atoms: 0,
            destroyed_atoms: 0,
        })
        .unwrap()],
        authority_uses: vec![],
    })
    .unwrap()
}

fn child(index: u64) -> ValueAggregateChildDescriptorV5 {
    ValueAggregateChildDescriptorV5::new(ValueAggregateChildDescriptorInputV5 {
        child_level: 0,
        partition: PartitionV3::new(index, index + 1).unwrap(),
        verified_program_id: ProgramIdV3::new([40; 32]).unwrap(),
        proof_profile_id: ProfileIdV3::new([41; 32]).unwrap(),
        program_manifest_root: commitment(42),
        journal_hash: indexed(43, index),
        claim_binding: indexed(44, index),
        semantic_subtree_root: indexed(45, index),
        operational_commitments: child_operational(index),
    })
    .unwrap()
}

fn proposal() -> ProposedValueAggregateV5 {
    ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
        aggregate_level: 1,
        scope: scope(),
        semantic_subtree: subtree(),
        children: vec![child(0), child(1)],
    })
    .unwrap()
}

#[test]
fn operational_bundle_hash_and_getters_bind_every_field() {
    let values = core::array::from_fn(|index| commitment(80 + index as u8));
    let baseline = operational(values);
    assert_eq!(operational_values(baseline), values);
    assert_eq!(
        baseline.canonical_hash().unwrap(),
        mirror_operational_hash(baseline)
    );

    for field in 0..values.len() {
        let mut mutated = values;
        mutated[field] = commitment(100 + field as u8);
        assert_ne!(
            operational(mutated).canonical_hash().unwrap(),
            baseline.canonical_hash().unwrap(),
            "operational field {field} was not hash-bound"
        );
    }
}

#[test]
fn parent_operational_fields_match_independent_ordered_root_mirror() {
    let proposal = proposal();
    let parent = proposal.operational_commitments();
    let child_commitments = proposal
        .children()
        .iter()
        .map(ValueAggregateChildDescriptorV5::operational_commitments)
        .collect::<Vec<_>>();
    assert_eq!(
        aggregate_value_operational_commitments_v5(&child_commitments).unwrap(),
        parent
    );
    let child_values = |select: fn(ValueAggregateOperationalCommitmentsV5) -> CommitmentV3| {
        proposal
            .children()
            .iter()
            .map(|child| select(child.operational_commitments()))
            .collect::<Vec<_>>()
    };
    for (actual, domain, select) in [
        (
            parent.data_availability_root(),
            b"zenodex.zrpf.value_operational_data_availability_root.v5".as_slice(),
            ValueAggregateOperationalCommitmentsV5::data_availability_root
                as fn(ValueAggregateOperationalCommitmentsV5) -> CommitmentV3,
        ),
        (
            parent.data_availability_certificate_root(),
            b"zenodex.zrpf.value_operational_data_availability_certificate_root.v5".as_slice(),
            ValueAggregateOperationalCommitmentsV5::data_availability_certificate_root,
        ),
        (
            parent.conflict_schedule_root(),
            b"zenodex.zrpf.value_operational_conflict_schedule_root.v5".as_slice(),
            ValueAggregateOperationalCommitmentsV5::conflict_schedule_root,
        ),
        (
            parent.cross_lane_outbox_root(),
            b"zenodex.zrpf.value_operational_cross_lane_outbox_root.v5".as_slice(),
            ValueAggregateOperationalCommitmentsV5::cross_lane_outbox_root,
        ),
        (
            parent.cross_lane_inbox_root(),
            b"zenodex.zrpf.value_operational_cross_lane_inbox_root.v5".as_slice(),
            ValueAggregateOperationalCommitmentsV5::cross_lane_inbox_root,
        ),
        (
            parent.cross_lane_message_ids_root(),
            b"zenodex.zrpf.value_operational_cross_lane_message_ids_root.v5".as_slice(),
            ValueAggregateOperationalCommitmentsV5::cross_lane_message_ids_root,
        ),
        (
            parent.carry_queue_pre_root(),
            b"zenodex.zrpf.value_operational_carry_queue_pre_root.v5".as_slice(),
            ValueAggregateOperationalCommitmentsV5::carry_queue_pre_root,
        ),
        (
            parent.carry_queue_post_root(),
            b"zenodex.zrpf.value_operational_carry_queue_post_root.v5".as_slice(),
            ValueAggregateOperationalCommitmentsV5::carry_queue_post_root,
        ),
    ] {
        assert_eq!(actual, mirror_root(domain, &child_values(select)));
    }
    assert_eq!(proposal.proposal_commitment(), mirror_proposal(&proposal));
}

#[test]
fn every_child_and_parent_operational_field_mutation_rejects() {
    let proposal = proposal();
    for field in OPERATIONAL_FIELDS {
        let mut parent = serde_json::to_value(&proposal).unwrap();
        parent["operational_commitments"][field] = serde_json::to_value(commitment(240)).unwrap();
        assert!(serde_json::from_value::<ProposedValueAggregateV5>(parent).is_err());

        let mut child = serde_json::to_value(&proposal).unwrap();
        child["children"][0]["operational_commitments"][field] =
            serde_json::to_value(commitment(241)).unwrap();
        assert!(serde_json::from_value::<ProposedValueAggregateV5>(child).is_err());
    }
}

#[test]
fn exact_codec_roundtrip_preserves_operational_commitments() {
    let proposal = proposal();
    let bytes = encode_value_aggregate_proposal_v5(&proposal).unwrap();
    let decoded = decode_exact_value_aggregate_proposal_v5(&bytes).unwrap();
    assert_eq!(decoded, proposal);
    assert_eq!(
        decoded.operational_commitments(),
        proposal.operational_commitments()
    );
}
