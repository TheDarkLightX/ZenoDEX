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
    spot_accounting_domain_id_v1, spot_atoms_unit_id_v1, spot_represented_value_profile_id_v1,
    spot_state_root_scheme_id_v1, SpotSettlementAuthorizationInputV1,
};

#[derive(Clone, Copy, Debug)]
pub struct FixtureConfig {
    pub aggregate_level: u8,
    pub row_count: u64,
    pub application_seed: u8,
    pub domain_seed: u8,
    pub epoch: u64,
    pub policy_seed: u8,
    pub feature_seed: u8,
    pub dependency_seed: u8,
    pub toolchain_seed: u8,
    pub lane_seed: u8,
    pub authority_grants_seed: u8,
    pub flow_amount: u128,
    pub wrong_value_profile: bool,
    pub supply_change: bool,
    pub child_program_seed: u8,
    pub child_profile_seed: u8,
    pub child_manifest_seed: u8,
    pub child_journal_seed: u8,
    pub child_claim_seed: u8,
    pub child_subtree_seed: u8,
}

impl Default for FixtureConfig {
    fn default() -> Self {
        Self {
            aggregate_level: 1,
            row_count: 2,
            application_seed: 1,
            domain_seed: 2,
            epoch: 27,
            policy_seed: 3,
            feature_seed: 4,
            dependency_seed: 5,
            toolchain_seed: 6,
            lane_seed: 31,
            authority_grants_seed: 32,
            flow_amount: 17,
            wrong_value_profile: false,
            supply_change: false,
            child_program_seed: 40,
            child_profile_seed: 41,
            child_manifest_seed: 42,
            child_journal_seed: 43,
            child_claim_seed: 44,
            child_subtree_seed: 45,
        }
    }
}

pub fn proposal(config: FixtureConfig) -> ProposedValueAggregateV5 {
    let scope = scope(config);
    let subtree = subtree(config, &scope);
    let children = (0..config.row_count)
        .map(|index| child(config, index))
        .collect();
    ProposedValueAggregateV5::derive(ValueAggregateProposalInputV5 {
        aggregate_level: config.aggregate_level,
        scope,
        semantic_subtree: subtree,
        children,
    })
    .unwrap()
}

pub fn authorization() -> SpotSettlementAuthorizationInputV1 {
    authorization_with(50, 51, 7, 52)
}

pub fn authorization_with(
    subject_seed: u8,
    scope_seed: u8,
    nonce: u64,
    grant_seed: u8,
) -> SpotSettlementAuthorizationInputV1 {
    SpotSettlementAuthorizationInputV1 {
        authorization_subject_id: AuthorizationSubjectIdV1::new([subject_seed.max(1); 32]).unwrap(),
        authorization_scope_id: AuthorizationScopeIdV1::new([scope_seed.max(1); 32]).unwrap(),
        authorization_nonce: nonce,
        authorization_grant_id: AuthorizationGrantIdV1::new([grant_seed.max(1); 32]).unwrap(),
    }
}

pub fn commitment(seed: u8) -> CommitmentV3 {
    CommitmentV3::new([seed.max(1); 32]).unwrap()
}

fn indexed(prefix: u8, index: u64) -> CommitmentV3 {
    let mut bytes = [prefix.max(1); 32];
    bytes[24..].copy_from_slice(&index.to_be_bytes());
    CommitmentV3::new(bytes).unwrap()
}

fn scope(config: FixtureConfig) -> NodeScopeV3 {
    NodeScopeV3::new(NodeScopeInputV3 {
        application_id: ApplicationIdV3::new([config.application_seed.max(1); 32]).unwrap(),
        chain_or_domain_id: DomainIdV3::new([config.domain_seed.max(1); 32]).unwrap(),
        epoch_start: config.epoch,
        epoch_end: config.epoch,
        public_policy_hash: commitment(config.policy_seed),
        feature_suite_hash: commitment(config.feature_seed),
        dependency_lock_hash: commitment(config.dependency_seed),
        toolchain_lock_hash: commitment(config.toolchain_seed),
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

fn subtree(config: FixtureConfig, scope: &NodeScopeV3) -> SemanticSubtreeV2 {
    let records = (0..config.row_count).map(record).collect::<Vec<_>>();
    let source = records[0].clone();
    let (outflow, inflow, issued) = if config.supply_change {
        (0, config.flow_amount, config.flow_amount)
    } else {
        (config.flow_amount, config.flow_amount, 0)
    };
    let authority_uses = if config.supply_change {
        vec![SemanticAuthorityUseV2::new(SemanticAuthorityUseInputV2 {
            source_claim_id: source.source_claim_id(),
            leaf_ordinal: 0,
            asset_id: [33; 32],
            atoms: config.flow_amount,
            legacy_authority_root: commitment(34),
        })
        .unwrap()]
    } else {
        vec![]
    };
    SemanticSubtreeV2::derive(SemanticSubtreeInputV2 {
        value_profile_id: if config.wrong_value_profile {
            commitment(99)
        } else {
            spot_represented_value_profile_id_v1().unwrap()
        },
        accounting_domain_id: spot_accounting_domain_id_v1().unwrap(),
        atoms_unit_id: spot_atoms_unit_id_v1().unwrap(),
        state_root_scheme_id: spot_state_root_scheme_id_v1().unwrap(),
        scope_hash: scope.canonical_hash().unwrap(),
        lane_id_hash: commitment(config.lane_seed),
        partition: PartitionV3::new(0, config.row_count).unwrap(),
        raw_subtree_pre_state_root: indexed(30, 0),
        raw_subtree_post_state_root: indexed(30, config.row_count),
        represented_row_count: config.row_count,
        leaf_records: records,
        authority_grants_root: commitment(config.authority_grants_seed),
        asset_flows: vec![SemanticAssetFlowV2::new(SemanticAssetFlowInputV2 {
            asset_id: [33; 32],
            outflow_atoms: outflow,
            inflow_atoms: inflow,
            issued_atoms: issued,
            destroyed_atoms: 0,
        })
        .unwrap()],
        authority_uses,
    })
    .unwrap()
}

fn child(config: FixtureConfig, index: u64) -> ValueAggregateChildDescriptorV5 {
    ValueAggregateChildDescriptorV5::new(ValueAggregateChildDescriptorInputV5 {
        child_level: config.aggregate_level - 1,
        partition: PartitionV3::new(index, index + 1).unwrap(),
        verified_program_id: ProgramIdV3::new([config.child_program_seed.max(1); 32]).unwrap(),
        proof_profile_id: ProfileIdV3::new([config.child_profile_seed.max(1); 32]).unwrap(),
        program_manifest_root: commitment(config.child_manifest_seed),
        journal_hash: indexed(config.child_journal_seed, index),
        claim_binding: indexed(config.child_claim_seed, index),
        semantic_subtree_root: indexed(config.child_subtree_seed, index),
    })
    .unwrap()
}
