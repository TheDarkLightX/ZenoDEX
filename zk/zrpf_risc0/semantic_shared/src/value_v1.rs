use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use sha2::{Digest, Sha256};
use tau_state_proof_risc0_shared::{
    recursive_asset_delta_root_v1, recursive_authority_scope_root_v1,
    recursive_lane_state_vector_root_v1, RecursiveAssetDeltaRowV1,
    RECURSIVE_AUTHORITY_EFFECT_MINT_V1, RECURSIVE_SPOT_LEAF_PROFILE_V1,
};
use zenodex_zrpf_protocol_v3::{
    CommitmentV3, ProposedSemanticEpochV1, ProposedSemanticLeafV1, SemanticEpochErrorV1,
    SemanticEpochProposalInputV1, ZrpfErrorV3,
};
use zenodex_zrpf_risc0_shared::PINNED_SPOT_LEAF_IMAGE_ID_V1;

pub const MAX_SPOT_VALUE_LEAVES_V1: usize = 8;
pub const MAX_SPOT_ASSET_ROWS_PER_LEAF_V1: usize = 16;
pub const MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2: usize = 128;
pub const MAX_SPOT_LANE_ID_BYTES_V1: usize = 128;
pub const MAX_SPOT_MINT_GRANTS_V1: usize = MAX_SPOT_REPRESENTED_ROWS_PER_SUMMARY_V2;
pub const MAX_SPOT_VALUE_SUBTREE_LEAVES_V2: usize = 64;
pub const CANONICAL_SPOT_ASSET_NAME_BYTES_V1: usize = 66;

const PRE_STATE_VECTOR_DOMAIN_V1: &[u8] = b"zenodex.risc0.recursive.pre_state_vector_root.v1";
const POST_STATE_VECTOR_DOMAIN_V1: &[u8] = b"zenodex.risc0.recursive.post_state_vector_root.v1";
const ATOMS_UNIT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_atoms_unit_id.v1";
const ACCOUNTING_DOMAIN_ID_V1: &[u8] = b"zenodex.zrpf.spot_accounting_domain_id.v1";
const STATE_ROOT_SCHEME_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_state_root_scheme_id.v1";
const VALUE_PROFILE_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_represented_value_profile_id.v1";
const AUTHORITY_GRANTS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_authority_grants_root.v1";
const ASSET_FLOWS_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_asset_flows_root.v1";
const AUTHORITY_USES_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_authority_uses_root.v1";
const STATE_CHAIN_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_state_chain_root.v1";
const LANE_ID_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_lane_id_hash.v1";
const VALUE_COMMITMENTS_HASH_DOMAIN_V1: &[u8] = b"zenodex.zrpf.spot_value_commitments_hash.v1";
const SEMANTIC_VALUE_ROOT_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_value_root.v1";
const SEMANTIC_VALUE_PROPOSAL_DOMAIN_V1: &[u8] = b"zenodex.zrpf.semantic_value_proposal.v1";
const SEMANTIC_LEAF_RECORDS_ROOT_DOMAIN_V2: &[u8] =
    b"zenodex.zrpf.spot_semantic_leaf_records_root.v2";
const ORDERED_TRANSACTION_ROOTS_DOMAIN_V1: &[u8] =
    b"zenodex.zrpf.spot_ordered_transaction_roots_root.v1";
const VALUE_SUBTREE_ROOT_DOMAIN_V2: &[u8] = b"zenodex.zrpf.spot_value_subtree_root.v2";

mod error;
pub use self::error::{ExpectedSpotSemanticValueFieldV1, SpotSemanticValueErrorV1};
#[derive(Clone, Debug, PartialEq, Eq)]
/// One proposed, scope-bound Spot faucet-mint allowance for a closed value root.
pub struct SpotMintAuthorityGrantV1 {
    asset_id: [u8; 32],
    legacy_authority_root: [u8; 32],
    max_atoms_per_value_root: u128,
}

impl SpotMintAuthorityGrantV1 {
    pub fn new(
        asset_id: [u8; 32],
        legacy_authority_root: [u8; 32],
        max_atoms_per_value_root: u128,
    ) -> Result<Self, SpotSemanticValueErrorV1> {
        if asset_id == [0; 32] || legacy_authority_root == [0; 32] || max_atoms_per_value_root == 0
        {
            return Err(SpotSemanticValueErrorV1::InvalidGrant);
        }
        Ok(Self {
            asset_id,
            legacy_authority_root,
            max_atoms_per_value_root,
        })
    }

    pub const fn asset_id(&self) -> [u8; 32] {
        self.asset_id
    }

    pub const fn legacy_authority_root(&self) -> [u8; 32] {
        self.legacy_authority_root
    }

    pub const fn max_atoms_per_value_root(&self) -> u128 {
        self.max_atoms_per_value_root
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Caller-proposed grant policy with a canonical root; construction grants no authority.
pub struct SpotRepresentedValuePolicyV1 {
    public_policy_hash: [u8; 32],
    grants: Vec<SpotMintAuthorityGrantV1>,
    authority_grants_root: CommitmentV3,
}

impl SpotRepresentedValuePolicyV1 {
    pub fn new(
        public_policy_hash: [u8; 32],
        grants: Vec<SpotMintAuthorityGrantV1>,
    ) -> Result<Self, SpotSemanticValueErrorV1> {
        if public_policy_hash == [0; 32] {
            return Err(SpotSemanticValueErrorV1::InvalidPublicPolicyHash);
        }
        if grants.len() > MAX_SPOT_MINT_GRANTS_V1 {
            return Err(SpotSemanticValueErrorV1::TooManyGrants {
                actual: grants.len(),
                maximum: MAX_SPOT_MINT_GRANTS_V1,
            });
        }
        validate_grants(public_policy_hash, &grants)?;
        let authority_grants_root = authority_grants_root(&grants)?;
        Ok(Self {
            public_policy_hash,
            grants,
            authority_grants_root,
        })
    }

    pub const fn public_policy_hash(&self) -> [u8; 32] {
        self.public_policy_hash
    }

    pub fn grants(&self) -> &[SpotMintAuthorityGrantV1] {
        &self.grants
    }

    pub const fn authority_grants_root(&self) -> CommitmentV3 {
        self.authority_grants_root
    }

    fn grant(&self, asset_id: &[u8; 32]) -> Option<&SpotMintAuthorityGrantV1> {
        self.grants
            .binary_search_by_key(asset_id, SpotMintAuthorityGrantV1::asset_id)
            .ok()
            .map(|index| &self.grants[index])
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Untrusted opening for one authenticated leaf's lane, raw endpoints, and asset rows.
pub struct SpotValueLeafOpeningV1 {
    lane_id: String,
    raw_pre_state_root: [u8; 32],
    raw_post_state_root: [u8; 32],
    asset_rows: Vec<RecursiveAssetDeltaRowV1>,
}

impl SpotValueLeafOpeningV1 {
    pub fn new(
        lane_id: String,
        raw_pre_state_root: [u8; 32],
        raw_post_state_root: [u8; 32],
        asset_rows: Vec<RecursiveAssetDeltaRowV1>,
    ) -> Result<Self, SpotSemanticValueErrorV1> {
        if !valid_lane_id(&lane_id) {
            return Err(SpotSemanticValueErrorV1::InvalidLaneId);
        }
        if raw_pre_state_root == [0; 32] || raw_post_state_root == [0; 32] {
            return Err(SpotSemanticValueErrorV1::ZeroStateRoot { ordinal: 0 });
        }
        if asset_rows.len() > MAX_SPOT_ASSET_ROWS_PER_LEAF_V1 {
            return Err(SpotSemanticValueErrorV1::TooManyRows {
                ordinal: 0,
                actual: asset_rows.len(),
                maximum: MAX_SPOT_ASSET_ROWS_PER_LEAF_V1,
            });
        }
        if asset_rows
            .iter()
            .any(|row| row.asset_id.len() > CANONICAL_SPOT_ASSET_NAME_BYTES_V1)
        {
            return Err(SpotSemanticValueErrorV1::NonCanonicalAssetId { ordinal: 0, row: 0 });
        }
        Ok(Self {
            lane_id,
            raw_pre_state_root,
            raw_post_state_root,
            asset_rows,
        })
    }

    pub fn lane_id(&self) -> &str {
        &self.lane_id
    }

    pub const fn raw_pre_state_root(&self) -> [u8; 32] {
        self.raw_pre_state_root
    }

    pub const fn raw_post_state_root(&self) -> [u8; 32] {
        self.raw_post_state_root
    }

    pub fn asset_rows(&self) -> &[RecursiveAssetDeltaRowV1] {
        &self.asset_rows
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Canonical checked residual totals for one represented asset.
pub struct SpotCanonicalAssetFlowV1 {
    asset_id: [u8; 32],
    outflow_atoms: u128,
    inflow_atoms: u128,
    issued_atoms: u128,
    destroyed_atoms: u128,
}

impl SpotCanonicalAssetFlowV1 {
    pub const fn asset_id(&self) -> [u8; 32] {
        self.asset_id
    }

    pub const fn outflow_atoms(&self) -> u128 {
        self.outflow_atoms
    }

    pub const fn inflow_atoms(&self) -> u128 {
        self.inflow_atoms
    }

    pub const fn issued_atoms(&self) -> u128 {
        self.issued_atoms
    }

    pub const fn destroyed_atoms(&self) -> u128 {
        self.destroyed_atoms
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// One exact use of a proposed Spot mint grant.
pub struct SpotMintAuthorityUseV1 {
    source_claim_id: [u8; 32],
    leaf_ordinal: u64,
    asset_id: [u8; 32],
    atoms: u128,
    legacy_authority_root: [u8; 32],
}

impl SpotMintAuthorityUseV1 {
    pub const fn asset_id(&self) -> [u8; 32] {
        self.asset_id
    }

    pub const fn atoms(&self) -> u128 {
        self.atoms
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Domain-separated commitments incorporated into a closed semantic value root.
pub struct SpotSemanticValueCommitmentsV1 {
    base_semantic_epoch_root: CommitmentV3,
    value_profile_id: CommitmentV3,
    accounting_domain_id: CommitmentV3,
    atoms_unit_id: CommitmentV3,
    state_root_scheme_id: CommitmentV3,
    semantic_leaf_records_root: CommitmentV3,
    ordered_transaction_roots_root: CommitmentV3,
    state_chain_root: CommitmentV3,
    authority_grants_root: CommitmentV3,
    asset_flows_root: CommitmentV3,
    authority_uses_root: CommitmentV3,
    value_subtree_root: CommitmentV3,
}

impl SpotSemanticValueCommitmentsV1 {
    pub const fn base_semantic_epoch_root(&self) -> CommitmentV3 {
        self.base_semantic_epoch_root
    }

    pub const fn value_profile_id(&self) -> CommitmentV3 {
        self.value_profile_id
    }

    pub const fn accounting_domain_id(&self) -> CommitmentV3 {
        self.accounting_domain_id
    }

    pub const fn atoms_unit_id(&self) -> CommitmentV3 {
        self.atoms_unit_id
    }

    pub const fn state_root_scheme_id(&self) -> CommitmentV3 {
        self.state_root_scheme_id
    }

    pub const fn semantic_leaf_records_root(&self) -> CommitmentV3 {
        self.semantic_leaf_records_root
    }

    pub const fn ordered_transaction_roots_root(&self) -> CommitmentV3 {
        self.ordered_transaction_roots_root
    }

    pub const fn state_chain_root(&self) -> CommitmentV3 {
        self.state_chain_root
    }

    pub const fn authority_grants_root(&self) -> CommitmentV3 {
        self.authority_grants_root
    }

    pub const fn asset_flows_root(&self) -> CommitmentV3 {
        self.asset_flows_root
    }

    pub const fn authority_uses_root(&self) -> CommitmentV3 {
        self.authority_uses_root
    }

    pub const fn value_subtree_root(&self) -> CommitmentV3 {
        self.value_subtree_root
    }

    fn canonical_hash(&self) -> Result<CommitmentV3, SpotSemanticValueErrorV1> {
        let mut hasher = domain_hasher(VALUE_COMMITMENTS_HASH_DOMAIN_V1)?;
        for value in [
            self.base_semantic_epoch_root,
            self.value_profile_id,
            self.accounting_domain_id,
            self.atoms_unit_id,
            self.state_root_scheme_id,
            self.semantic_leaf_records_root,
            self.ordered_transaction_roots_root,
            self.state_chain_root,
            self.authority_grants_root,
            self.asset_flows_root,
            self.authority_uses_root,
            self.value_subtree_root,
        ] {
            write_bytes32(&mut hasher, value.as_bytes());
        }
        commitment(hasher.finalize().into())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Pure closed-root projection with no receipt, admission, or settlement authority.
pub struct SpotSemanticValueProjectionV1 {
    scope_hash: CommitmentV3,
    lane_id_hash: CommitmentV3,
    raw_epoch_pre_state_root: [u8; 32],
    raw_epoch_post_state_root: [u8; 32],
    leaf_count: u64,
    represented_row_count: u64,
    asset_flows: Vec<SpotCanonicalAssetFlowV1>,
    authority_uses: Vec<SpotMintAuthorityUseV1>,
    commitments: SpotSemanticValueCommitmentsV1,
    semantic_value_root: CommitmentV3,
    proposal_hash: CommitmentV3,
}

impl SpotSemanticValueProjectionV1 {
    pub const fn scope_hash(&self) -> CommitmentV3 {
        self.scope_hash
    }

    pub const fn lane_id_hash(&self) -> CommitmentV3 {
        self.lane_id_hash
    }

    pub const fn raw_epoch_pre_state_root(&self) -> [u8; 32] {
        self.raw_epoch_pre_state_root
    }

    pub const fn raw_epoch_post_state_root(&self) -> [u8; 32] {
        self.raw_epoch_post_state_root
    }

    pub const fn leaf_count(&self) -> u64 {
        self.leaf_count
    }

    pub const fn represented_row_count(&self) -> u64 {
        self.represented_row_count
    }

    pub fn asset_flows(&self) -> &[SpotCanonicalAssetFlowV1] {
        &self.asset_flows
    }

    pub fn authority_uses(&self) -> &[SpotMintAuthorityUseV1] {
        &self.authority_uses
    }

    pub const fn commitments(&self) -> &SpotSemanticValueCommitmentsV1 {
        &self.commitments
    }

    pub const fn semantic_value_root(&self) -> CommitmentV3 {
        self.semantic_value_root
    }

    pub const fn proposal_hash(&self) -> CommitmentV3 {
        self.proposal_hash
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// Sealed composable residual summary; intentionally lacks a public raw constructor or codec.
pub struct SpotValueSubtreeSummaryV2 {
    leaves: Vec<ProposedSemanticLeafV1>,
    openings: Vec<SpotValueLeafOpeningV1>,
    partition_start: u64,
    partition_end_exclusive: u64,
    scope_hash: CommitmentV3,
    lane_id_hash: CommitmentV3,
    raw_subtree_pre_state_root: [u8; 32],
    raw_subtree_post_state_root: [u8; 32],
    leaf_count: u64,
    represented_row_count: u64,
    semantic_leaf_records_root: CommitmentV3,
    ordered_transaction_roots_root: CommitmentV3,
    state_chain_root: CommitmentV3,
    authority_grants_root: CommitmentV3,
    asset_flows_root: CommitmentV3,
    authority_uses_root: CommitmentV3,
    asset_flows: Vec<SpotCanonicalAssetFlowV1>,
    authority_uses: Vec<SpotMintAuthorityUseV1>,
    subtree_root: CommitmentV3,
}

impl SpotValueSubtreeSummaryV2 {
    pub const fn partition_start(&self) -> u64 {
        self.partition_start
    }

    pub const fn partition_end_exclusive(&self) -> u64 {
        self.partition_end_exclusive
    }

    pub const fn raw_subtree_pre_state_root(&self) -> [u8; 32] {
        self.raw_subtree_pre_state_root
    }

    pub const fn raw_subtree_post_state_root(&self) -> [u8; 32] {
        self.raw_subtree_post_state_root
    }

    pub const fn leaf_count(&self) -> u64 {
        self.leaf_count
    }

    pub fn asset_flows(&self) -> &[SpotCanonicalAssetFlowV1] {
        &self.asset_flows
    }

    pub const fn subtree_root(&self) -> CommitmentV3 {
        self.subtree_root
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct FlowAccumulatorV1 {
    outflow_atoms: u128,
    inflow_atoms: u128,
    issued_atoms: u128,
    destroyed_atoms: u128,
}

struct CompositionStateV1 {
    lane_id: Option<String>,
    previous_post: Option<[u8; 32]>,
    transaction_roots: BTreeSet<[u8; 32]>,
    flows: BTreeMap<[u8; 32], FlowAccumulatorV1>,
    grant_usage: BTreeMap<[u8; 32], u128>,
    authority_uses: Vec<SpotMintAuthorityUseV1>,
    state_records: Vec<StateRecordV1>,
    row_count: usize,
}

impl CompositionStateV1 {
    fn new() -> Self {
        Self {
            lane_id: None,
            previous_post: None,
            transaction_roots: BTreeSet::new(),
            flows: BTreeMap::new(),
            grant_usage: BTreeMap::new(),
            authority_uses: Vec::new(),
            state_records: Vec::new(),
            row_count: 0,
        }
    }
}

#[derive(Clone, Copy)]
struct StateRecordV1 {
    source_claim_id: [u8; 32],
    leaf_ordinal: u64,
    transaction_root: [u8; 32],
    raw_pre_state_root: [u8; 32],
    raw_post_state_root: [u8; 32],
}

struct ValueSubtreeRootInputV2 {
    partition_start: u64,
    partition_end_exclusive: u64,
    scope_hash: CommitmentV3,
    lane_id_hash: CommitmentV3,
    raw_pre: [u8; 32],
    raw_post: [u8; 32],
    leaf_count: u64,
    row_count: u64,
    semantic_leaf_records_root: CommitmentV3,
    ordered_transaction_roots_root: CommitmentV3,
    state_chain_root: CommitmentV3,
    authority_grants_root: CommitmentV3,
    asset_flows_root: CommitmentV3,
    authority_uses_root: CommitmentV3,
}

mod compose;
pub use self::compose::{
    close_spot_represented_value_epoch_v1, compose_spot_represented_value_v1,
    merge_spot_value_subtrees_v2, propose_spot_value_subtree_v2,
};
mod expected;
pub use self::expected::*;
mod hash;
mod validate;
mod wire_v4;
use self::hash::{
    authority_grants_root, commitment, domain_hasher, valid_lane_id, validate_grants, write_bytes32,
};
pub use self::hash::{
    canonical_spot_asset_name_v1, spot_accounting_domain_id_v1, spot_atoms_unit_id_v1,
    spot_represented_value_profile_id_v1, spot_state_root_scheme_id_v1,
};
pub use self::wire_v4::*;
