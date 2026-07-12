use zenodex_zrpf_protocol_v3::{
    derive_sparse_merkle_root_v1, ApplicationIdV3, AuthorizationGrantIdV1, AuthorizationScopeIdV1,
    AuthorizationSubjectIdV1, CommitmentV3, DomainIdV3, EconomicActionIdV1, NodeScopeInputV3,
    NodeScopeV3, PartitionV3, ProfileIdV3, ProgramIdV3, ProposedValueAggregateV5,
    SemanticAssetFlowInputV2, SemanticAssetFlowV2, SemanticSubtreeInputV2, SemanticSubtreeV2,
    SemanticValueLeafRecordInputV2, SemanticValueLeafRecordV2, SparseMerkleBatchTransitionErrorV1,
    SparseMerkleCellTransitionErrorV1, SparseMerkleCellTransitionWitnessInputV1,
    SparseMerkleCellTransitionWitnessV1, SparseMerkleSiblingPathV1, TaskIdV3,
    ValueAggregateChildDescriptorInputV5, ValueAggregateChildDescriptorV5,
    ValueAggregateOperationalCommitmentsInputV5, ValueAggregateOperationalCommitmentsV5,
    ValueAggregateProposalInputV5, ValueHashV2, SPARSE_MERKLE_TREE_DEPTH_V1,
    SPARSE_MERKLE_WITNESS_VERSION_V1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    derive_spot_settlement_projection_v1, derive_spot_settlement_state_projection_v2,
    propose_spot_settlement_state_projection_v2, spot_accounting_domain_id_v1,
    spot_atoms_unit_id_v1, spot_represented_value_profile_id_v1, spot_state_root_scheme_id_v1,
    SpotSettlementAuthorizationInputV1, SpotSettlementProjectionErrorV1,
};

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
        epoch_start: 27,
        epoch_end: 27,
        public_policy_hash: commitment(3),
        feature_suite_hash: commitment(4),
        dependency_lock_hash: commitment(5),
        toolchain_lock_hash: commitment(6),
    })
    .unwrap()
}

fn proposal() -> ProposedValueAggregateV5 {
    let scope = scope();
    let record = SemanticValueLeafRecordV2::new(SemanticValueLeafRecordInputV2 {
        partition: PartitionV3::new(0, 1).unwrap(),
        semantic_leaf_hash: commitment(10),
        source_claim_id: commitment(11),
        semantic_source_id: commitment(12),
        task_id: TaskIdV3::new([13; 32]).unwrap(),
        pre_state_vector_root: commitment(14),
        post_state_vector_root: commitment(15),
        transaction_root: commitment(16),
        effect_root: commitment(17),
        asset_delta_root: commitment(18),
        raw_pre_state_root: indexed(30, 0),
        raw_post_state_root: indexed(30, 1),
    })
    .unwrap();
    let subtree = SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: spot_represented_value_profile_id_v1().unwrap(),
        accounting_domain_id: spot_accounting_domain_id_v1().unwrap(),
        atoms_unit_id: spot_atoms_unit_id_v1().unwrap(),
        state_root_scheme_id: spot_state_root_scheme_id_v1().unwrap(),
        scope_hash: scope.canonical_hash().unwrap(),
        lane_id_hash: commitment(31),
        partition: PartitionV3::new(0, 1).unwrap(),
        raw_subtree_pre_state_root: indexed(30, 0),
        raw_subtree_post_state_root: indexed(30, 1),
        represented_row_count: 1,
        leaf_records: vec![record],
        authority_grants_root: commitment(32),
        asset_flows: vec![SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
            asset_id: [33; 32],
            outflow_atoms: 17,
            inflow_atoms: 17,
            issued_atoms: 0,
            destroyed_atoms: 0,
        })
        .unwrap()],
        authority_uses: vec![],
    })
    .unwrap();
    let operational =
        ValueAggregateOperationalCommitmentsV5::new(ValueAggregateOperationalCommitmentsInputV5 {
            data_availability_root: commitment(46),
            data_availability_certificate_root: commitment(47),
            conflict_schedule_root: commitment(48),
            cross_lane_outbox_root: commitment(49),
            cross_lane_inbox_root: commitment(50),
            cross_lane_message_ids_root: commitment(51),
            carry_queue_pre_root: commitment(52),
            carry_queue_post_root: commitment(53),
        })
        .unwrap();
    let child = ValueAggregateChildDescriptorV5::new(ValueAggregateChildDescriptorInputV5 {
        child_level: 0,
        partition: PartitionV3::new(0, 1).unwrap(),
        verified_program_id: ProgramIdV3::new([40; 32]).unwrap(),
        proof_profile_id: ProfileIdV3::new([41; 32]).unwrap(),
        program_manifest_root: commitment(42),
        journal_hash: commitment(43),
        claim_binding: commitment(44),
        semantic_subtree_root: commitment(45),
        operational_commitments: operational,
    })
    .unwrap();
    ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
        aggregate_level: 1,
        scope,
        semantic_subtree: subtree,
        children: vec![child],
    })
    .unwrap()
}

fn authorization() -> SpotSettlementAuthorizationInputV1 {
    SpotSettlementAuthorizationInputV1 {
        authorization_subject_id: AuthorizationSubjectIdV1::new([60; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([61; 32]).unwrap(),
        authorization_nonce: 7,
        authorization_grant_id: AuthorizationGrantIdV1::new([62; 32]).unwrap(),
    }
}

struct WitnessFixture {
    witness: SparseMerkleCellTransitionWitnessV1,
    pre_root: CommitmentV3,
    post_root: CommitmentV3,
}

fn witness_for(
    proposal: &ProposedValueAggregateV5,
    key: CommitmentV3,
    pre_value: ValueHashV2,
    post_value: ValueHashV2,
) -> WitnessFixture {
    let siblings = SparseMerkleSiblingPathV1::new([commitment(90); SPARSE_MERKLE_TREE_DEPTH_V1]);
    let pre_root = derive_sparse_merkle_root_v1(key, pre_value, &siblings).unwrap();
    let post_root = derive_sparse_merkle_root_v1(key, post_value, &siblings).unwrap();
    let proposed =
        propose_spot_settlement_state_projection_v2(proposal, authorization(), pre_root, post_root)
            .unwrap();
    let write = &proposed.settlement_plan().ledger_cell_writes()[0];
    let witness =
        SparseMerkleCellTransitionWitnessV1::new(SparseMerkleCellTransitionWitnessInputV1 {
            witness_version: SPARSE_MERKLE_WITNESS_VERSION_V1,
            economic_action_id: write.economic_action_id(),
            cell_key: key,
            pre_value_hash: pre_value,
            post_value_hash: post_value,
            sibling_commitments: siblings,
            claimed_pre_root: pre_root,
            claimed_post_root: post_root,
        })
        .unwrap();
    WitnessFixture {
        witness,
        pre_root,
        post_root,
    }
}

#[test]
fn state_bound_projection_uses_sparse_roots_and_exact_raw_cell_values() {
    let proposal = proposal();
    let compatibility = derive_spot_settlement_projection_v1(&proposal, authorization()).unwrap();
    let pre_value = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_pre_state_root()
            .into_bytes(),
    );
    let post_value = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_post_state_root()
            .into_bytes(),
    );
    let fixture = witness_for(&proposal, compatibility.cell_key(), pre_value, post_value);
    let result =
        derive_spot_settlement_state_projection_v2(&proposal, authorization(), fixture.witness)
            .unwrap();
    let plan = result.projection().settlement_plan();
    let write = &plan.ledger_cell_writes()[0];

    assert_eq!(
        plan.economic_action_batch().pre_state_root(),
        fixture.pre_root
    );
    assert_eq!(plan.post_state_root(), fixture.post_root);
    assert_eq!(write.pre_value_hash(), pre_value);
    assert_eq!(write.post_value_hash(), post_value);
    assert_eq!(result.state_transition().batch_pre_root(), fixture.pre_root);
    assert_eq!(
        result.state_transition().batch_post_root(),
        fixture.post_root
    );
    assert_ne!(
        fixture.pre_root,
        proposal.semantic_subtree().raw_subtree_pre_state_root()
    );
}

#[test]
fn valid_witness_for_wrong_key_rejects_at_exact_write_binding() {
    let proposal = proposal();
    let raw_pre = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_pre_state_root()
            .into_bytes(),
    );
    let raw_post = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_post_state_root()
            .into_bytes(),
    );
    let fixture = witness_for(&proposal, commitment(99), raw_pre, raw_post);
    assert_eq!(
        derive_spot_settlement_state_projection_v2(&proposal, authorization(), fixture.witness,),
        Err(SpotSettlementProjectionErrorV1::SparseMerkleBatch(
            SparseMerkleBatchTransitionErrorV1::CellTransition(
                SparseMerkleCellTransitionErrorV1::CellKeyMismatch,
            ),
        ))
    );
}

#[test]
fn valid_witness_for_wrong_raw_value_rejects_at_exact_write_binding() {
    let proposal = proposal();
    let compatibility = derive_spot_settlement_projection_v1(&proposal, authorization()).unwrap();
    let wrong_pre = ValueHashV2::new([88; 32]);
    let raw_post = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_post_state_root()
            .into_bytes(),
    );
    let fixture = witness_for(&proposal, compatibility.cell_key(), wrong_pre, raw_post);
    assert_eq!(
        derive_spot_settlement_state_projection_v2(&proposal, authorization(), fixture.witness,),
        Err(SpotSettlementProjectionErrorV1::SparseMerkleBatch(
            SparseMerkleBatchTransitionErrorV1::CellTransition(
                SparseMerkleCellTransitionErrorV1::PreValueMismatch,
            ),
        ))
    );
}

#[test]
fn action_id_substitution_rejects_even_with_exact_path_and_values() {
    let proposal = proposal();
    let compatibility = derive_spot_settlement_projection_v1(&proposal, authorization()).unwrap();
    let pre_value = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_pre_state_root()
            .into_bytes(),
    );
    let post_value = ValueHashV2::new(
        proposal
            .semantic_subtree()
            .raw_subtree_post_state_root()
            .into_bytes(),
    );
    let fixture = witness_for(&proposal, compatibility.cell_key(), pre_value, post_value);
    let replaced =
        SparseMerkleCellTransitionWitnessV1::new(SparseMerkleCellTransitionWitnessInputV1 {
            witness_version: SPARSE_MERKLE_WITNESS_VERSION_V1,
            economic_action_id: EconomicActionIdV1::new([99; 32]).unwrap(),
            cell_key: fixture.witness.cell_key(),
            pre_value_hash: fixture.witness.pre_value_hash(),
            post_value_hash: fixture.witness.post_value_hash(),
            sibling_commitments: fixture.witness.sibling_commitments().clone(),
            claimed_pre_root: fixture.pre_root,
            claimed_post_root: fixture.post_root,
        })
        .unwrap();
    assert_eq!(
        derive_spot_settlement_state_projection_v2(&proposal, authorization(), replaced),
        Err(SpotSettlementProjectionErrorV1::SparseMerkleBatch(
            SparseMerkleBatchTransitionErrorV1::CellTransition(
                SparseMerkleCellTransitionErrorV1::EconomicActionMismatch,
            ),
        ))
    );
}
