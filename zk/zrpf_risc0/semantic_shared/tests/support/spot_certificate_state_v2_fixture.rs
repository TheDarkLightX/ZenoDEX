#![allow(dead_code)]

use zenodex_zrpf_protocol_v3::{
    derive_sparse_merkle_root_v1, ApplicationIdV3, CommitmentV3, DomainIdV3, EconomicActionIdV1,
    FullBlobDataAvailabilityCertificateInputV1, FullBlobDataAvailabilityCertificateV1,
    ProposedValueAggregateV5, SparseMerkleCellTransitionWitnessInputV1,
    SparseMerkleCellTransitionWitnessV1, SparseMerkleSiblingPathV1, ValueHashV2,
    SPARSE_MERKLE_TREE_DEPTH_V1, SPARSE_MERKLE_WITNESS_VERSION_V1,
};
use zenodex_zrpf_risc0_semantic_shared::{
    derive_spot_settlement_projection_v1, encode_ordinary_spot_settlement_replay_data_v2,
    ordinary_spot_settlement_replay_data_schema_id_v2, propose_spot_settlement_state_projection_v2,
    OrdinarySpotSettlementReplayDataV2, SpotSettlementAuthorizationInputV1,
};

use super::fixture::commitment;

#[derive(Clone, Debug)]
pub struct WitnessOverridesV2 {
    pub economic_action_id: Option<EconomicActionIdV1>,
    pub cell_key: Option<CommitmentV3>,
    pub pre_value_hash: Option<ValueHashV2>,
    pub post_value_hash: Option<ValueHashV2>,
    pub sibling_seed: u8,
}

impl Default for WitnessOverridesV2 {
    fn default() -> Self {
        Self {
            economic_action_id: None,
            cell_key: None,
            pre_value_hash: None,
            post_value_hash: None,
            sibling_seed: 90,
        }
    }
}

#[derive(Clone, Copy)]
pub struct DaCertificateMetadataV2 {
    pub application_id: ApplicationIdV3,
    pub chain_or_domain_id: DomainIdV3,
    pub epoch_id: u64,
    pub data_schema_id: CommitmentV3,
    pub retention_through_epoch: u64,
    pub storage_policy_hash: CommitmentV3,
}

impl DaCertificateMetadataV2 {
    pub fn matching(proposal: &ProposedValueAggregateV5) -> Self {
        let scope = proposal.scope();
        Self {
            application_id: scope.application_id(),
            chain_or_domain_id: scope.chain_or_domain_id(),
            epoch_id: scope.epoch_start(),
            data_schema_id: ordinary_spot_settlement_replay_data_schema_id_v2().unwrap(),
            retention_through_epoch: scope.epoch_start() + 10,
            storage_policy_hash: scope.public_policy_hash(),
        }
    }
}

pub fn witness(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
) -> SparseMerkleCellTransitionWitnessV1 {
    witness_with(proposal, authorization, WitnessOverridesV2::default())
}

pub fn witness_with(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    overrides: WitnessOverridesV2,
) -> SparseMerkleCellTransitionWitnessV1 {
    let compatibility = derive_spot_settlement_projection_v1(proposal, authorization).unwrap();
    let cell_key = overrides.cell_key.unwrap_or(compatibility.cell_key());
    let pre_value_hash = overrides.pre_value_hash.unwrap_or_else(|| {
        ValueHashV2::new(
            proposal
                .semantic_subtree()
                .raw_subtree_pre_state_root()
                .into_bytes(),
        )
    });
    let post_value_hash = overrides.post_value_hash.unwrap_or_else(|| {
        ValueHashV2::new(
            proposal
                .semantic_subtree()
                .raw_subtree_post_state_root()
                .into_bytes(),
        )
    });
    let siblings = SparseMerkleSiblingPathV1::new(
        [commitment(overrides.sibling_seed); SPARSE_MERKLE_TREE_DEPTH_V1],
    );
    let pre_root = derive_sparse_merkle_root_v1(cell_key, pre_value_hash, &siblings).unwrap();
    let post_root = derive_sparse_merkle_root_v1(cell_key, post_value_hash, &siblings).unwrap();
    let proposed =
        propose_spot_settlement_state_projection_v2(proposal, authorization, pre_root, post_root)
            .unwrap();
    SparseMerkleCellTransitionWitnessV1::new(SparseMerkleCellTransitionWitnessInputV1 {
        witness_version: SPARSE_MERKLE_WITNESS_VERSION_V1,
        economic_action_id: overrides
            .economic_action_id
            .unwrap_or(proposed.economic_action_id()),
        cell_key,
        pre_value_hash,
        post_value_hash,
        sibling_commitments: siblings,
        claimed_pre_root: pre_root,
        claimed_post_root: post_root,
    })
    .unwrap()
}

pub fn replay_blob(
    proposal: &ProposedValueAggregateV5,
    authorization: SpotSettlementAuthorizationInputV1,
    witness: &SparseMerkleCellTransitionWitnessV1,
) -> Vec<u8> {
    let replay =
        OrdinarySpotSettlementReplayDataV2::recompose(proposal, authorization, witness).unwrap();
    encode_ordinary_spot_settlement_replay_data_v2(&replay).unwrap()
}

pub fn da_certificate(
    blob: &[u8],
    metadata: DaCertificateMetadataV2,
) -> FullBlobDataAvailabilityCertificateV1 {
    FullBlobDataAvailabilityCertificateV1::derive(FullBlobDataAvailabilityCertificateInputV1 {
        application_id: metadata.application_id,
        chain_or_domain_id: metadata.chain_or_domain_id,
        epoch_id: metadata.epoch_id,
        data_schema_id: metadata.data_schema_id,
        blob,
        retention_through_epoch: metadata.retention_through_epoch,
        storage_policy_hash: metadata.storage_policy_hash,
    })
    .unwrap()
}

pub fn matching_da_certificate(
    proposal: &ProposedValueAggregateV5,
    blob: &[u8],
) -> FullBlobDataAvailabilityCertificateV1 {
    da_certificate(blob, DaCertificateMetadataV2::matching(proposal))
}
