use sha2::{Digest, Sha256};
use zenodex_zrpf_protocol_v3::{
    ApplicationIdV3, AuthorizationGrantIdV1, AuthorizationScopeIdV1, AuthorizationSubjectIdV1,
    CommitmentV3, DomainIdV3, NodeScopeInputV3, NodeScopeV3, PartitionV3, ProfileIdV3, ProgramIdV3,
    ProposedValueAggregateV5, SemanticAssetFlowInputV2, SemanticAssetFlowV2,
    SemanticAuthorityUseInputV2, SemanticAuthorityUseV2, SemanticSubtreeInputV2, SemanticSubtreeV2,
    SemanticValueLeafRecordInputV2, SemanticValueLeafRecordV2, TaskIdV3,
    ValueAggregateChildDescriptorInputV5, ValueAggregateChildDescriptorV5,
    ValueAggregateProposalInputV5,
};
use zenodex_zrpf_risc0_semantic_shared::{
    derive_spot_settlement_projection_v1, spot_accounting_domain_id_v1, spot_atoms_unit_id_v1,
    spot_represented_value_profile_id_v1, spot_state_root_scheme_id_v1,
    spot_value_aggregate_journal_hash_v1, SpotSettlementAuthorizationInputV1,
    SpotSettlementProjectionErrorV1,
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

fn ordinary_subtree(amount: u128, value_profile: CommitmentV3) -> SemanticSubtreeV2 {
    let records = vec![record(0), record(1)];
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: value_profile,
        accounting_domain_id: spot_accounting_domain_id_v1().unwrap(),
        atoms_unit_id: spot_atoms_unit_id_v1().unwrap(),
        state_root_scheme_id: spot_state_root_scheme_id_v1().unwrap(),
        scope_hash: scope().canonical_hash().unwrap(),
        lane_id_hash: commitment(31),
        partition: PartitionV3::new(0, 2).unwrap(),
        raw_subtree_pre_state_root: indexed(30, 0),
        raw_subtree_post_state_root: indexed(30, 2),
        represented_row_count: 2,
        leaf_records: records,
        authority_grants_root: commitment(32),
        asset_flows: vec![SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
            asset_id: [33; 32],
            outflow_atoms: amount,
            inflow_atoms: amount,
            issued_atoms: 0,
            destroyed_atoms: 0,
        })
        .unwrap()],
        authority_uses: vec![],
    })
    .unwrap()
}

fn supply_subtree() -> SemanticSubtreeV2 {
    let source = record(0);
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: spot_represented_value_profile_id_v1().unwrap(),
        accounting_domain_id: spot_accounting_domain_id_v1().unwrap(),
        atoms_unit_id: spot_atoms_unit_id_v1().unwrap(),
        state_root_scheme_id: spot_state_root_scheme_id_v1().unwrap(),
        scope_hash: scope().canonical_hash().unwrap(),
        lane_id_hash: commitment(31),
        partition: PartitionV3::new(0, 1).unwrap(),
        raw_subtree_pre_state_root: indexed(30, 0),
        raw_subtree_post_state_root: indexed(30, 1),
        represented_row_count: 1,
        leaf_records: vec![source.clone()],
        authority_grants_root: commitment(32),
        asset_flows: vec![SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
            asset_id: [33; 32],
            outflow_atoms: 0,
            inflow_atoms: 5,
            issued_atoms: 5,
            destroyed_atoms: 0,
        })
        .unwrap()],
        authority_uses: vec![SemanticAuthorityUseV2::new(SemanticAuthorityUseInputV2 {
            source_claim_id: source.source_claim_id(),
            leaf_ordinal: 0,
            asset_id: [33; 32],
            atoms: 5,
            legacy_authority_root: commitment(34),
        })
        .unwrap()],
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
    })
    .unwrap()
}

fn proposal_for(subtree: SemanticSubtreeV2) -> ProposedValueAggregateV5 {
    let count = subtree.leaf_count();
    ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
        aggregate_level: 1,
        scope: scope(),
        semantic_subtree: subtree,
        children: (0..count).map(child).collect(),
    })
    .unwrap()
}

fn authorization(nonce: u64) -> SpotSettlementAuthorizationInputV1 {
    SpotSettlementAuthorizationInputV1 {
        authorization_subject_id: AuthorizationSubjectIdV1::new([50; 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([51; 32]).unwrap(),
        authorization_nonce: nonce,
        authorization_grant_id: AuthorizationGrantIdV1::new([52; 32]).unwrap(),
    }
}

#[test]
fn ordinary_spot_projection_deterministically_closes_action_and_plan_rows() {
    let proposal = proposal_for(ordinary_subtree(
        17,
        spot_represented_value_profile_id_v1().unwrap(),
    ));
    let projection = derive_spot_settlement_projection_v1(&proposal, authorization(7)).unwrap();
    let batch = projection.action_batch();
    let plan = projection.settlement_plan();

    assert_eq!(batch.actions().len(), 1);
    assert_eq!(
        batch.pre_state_root(),
        proposal.semantic_subtree().raw_subtree_pre_state_root()
    );
    assert_eq!(
        batch.actions()[0].record().effect_commitment(),
        projection.effect_commitment()
    );
    assert_eq!(batch.actions()[0].record().consumed_object_ids().len(), 2);
    assert_eq!(plan.economic_action_batch(), batch);
    assert_eq!(plan.ledger_cell_writes().len(), 1);
    assert_eq!(plan.asset_effects().len(), 1);
    assert_eq!(plan.asset_effects()[0].debit_atoms(), 17);
    assert_eq!(plan.asset_effects()[0].credit_atoms(), 17);
    assert!(plan.message_effects().is_empty());
    assert!(plan.carry_effects().is_empty());
    assert!(plan.reward_effects().is_empty());
    assert_eq!(
        projection.source_semantic_journal_hash(),
        spot_value_aggregate_journal_hash_v1(&proposal).unwrap()
    );
}

#[test]
fn source_cell_action_and_effect_hashes_match_independent_preimages() {
    let proposal = proposal_for(ordinary_subtree(
        23,
        spot_represented_value_profile_id_v1().unwrap(),
    ));
    let projection = derive_spot_settlement_projection_v1(&proposal, authorization(9)).unwrap();

    let mut cell = domain_hasher(b"zenodex.zrpf.spot_epoch_cell_key.v1");
    cell.update(proposal.scope().application_id().as_bytes());
    cell.update(proposal.scope().chain_or_domain_id().as_bytes());
    cell.update(proposal.semantic_subtree().lane_id_hash().as_bytes());
    assert_eq!(projection.cell_key(), commit(cell));

    let mut effect = domain_hasher(b"zenodex.zrpf.spot_epoch_effect_projection.v1");
    effect.update(projection.cell_key().as_bytes());
    effect.update(
        proposal
            .semantic_subtree()
            .raw_subtree_pre_state_root()
            .as_bytes(),
    );
    effect.update(
        proposal
            .semantic_subtree()
            .raw_subtree_post_state_root()
            .as_bytes(),
    );
    effect.update(1_u16.to_be_bytes());
    effect.update([33; 32]);
    for amount in [23_u128, 23, 0, 0] {
        effect.update(amount.to_be_bytes());
    }
    assert_eq!(projection.effect_commitment(), commit(effect));

    let bytes = zenodex_zrpf_protocol_v3::encode_value_aggregate_proposal_v5(&proposal).unwrap();
    let mut source = domain_hasher(b"zenodex.zrpf.spot_value_aggregate_journal.v1");
    source.update(u32::try_from(bytes.len()).unwrap().to_be_bytes());
    source.update(bytes);
    assert_eq!(projection.source_semantic_journal_hash(), commit(source));
}

#[test]
fn authorization_nonce_changes_identity_without_relabeling_semantic_effects() {
    let proposal = proposal_for(ordinary_subtree(
        17,
        spot_represented_value_profile_id_v1().unwrap(),
    ));
    let first = derive_spot_settlement_projection_v1(&proposal, authorization(1)).unwrap();
    let second = derive_spot_settlement_projection_v1(&proposal, authorization(2)).unwrap();
    assert_ne!(
        first.action_batch().actions()[0].action_id().unwrap(),
        second.action_batch().actions()[0].action_id().unwrap()
    );
    assert_eq!(first.effect_commitment(), second.effect_commitment());
    assert_eq!(
        first.action_semantics_hash(),
        second.action_semantics_hash()
    );
}

#[test]
fn flow_changes_rederive_effect_action_and_plan_commitments() {
    let first_proposal = proposal_for(ordinary_subtree(
        17,
        spot_represented_value_profile_id_v1().unwrap(),
    ));
    let second_proposal = proposal_for(ordinary_subtree(
        18,
        spot_represented_value_profile_id_v1().unwrap(),
    ));
    let first = derive_spot_settlement_projection_v1(&first_proposal, authorization(1)).unwrap();
    let second = derive_spot_settlement_projection_v1(&second_proposal, authorization(1)).unwrap();
    assert_ne!(first.effect_commitment(), second.effect_commitment());
    assert_ne!(
        first.action_semantics_hash(),
        second.action_semantics_hash()
    );
    assert_ne!(
        first.settlement_plan().canonical_commitment().unwrap(),
        second.settlement_plan().canonical_commitment().unwrap()
    );
}

#[test]
fn wrong_value_profile_and_supply_changing_flow_reject_before_plan_construction() {
    let wrong_profile = proposal_for(ordinary_subtree(17, commitment(99)));
    assert_eq!(
        derive_spot_settlement_projection_v1(&wrong_profile, authorization(1)).unwrap_err(),
        SpotSettlementProjectionErrorV1::ProfileMismatch("value_profile_id")
    );

    let supply = proposal_for(supply_subtree());
    assert_eq!(
        derive_spot_settlement_projection_v1(&supply, authorization(1)).unwrap_err(),
        SpotSettlementProjectionErrorV1::SupplyChangingFlow
    );
}

fn domain_hasher(domain: &[u8]) -> Sha256 {
    let mut hasher = Sha256::new();
    hasher.update(u16::try_from(domain.len()).unwrap().to_be_bytes());
    hasher.update(domain);
    hasher
}

fn commit(hasher: Sha256) -> CommitmentV3 {
    CommitmentV3::new(hasher.finalize().into()).unwrap()
}
