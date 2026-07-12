use alloc::vec::Vec;

use serde::{de, Deserialize, Deserializer, Serialize};
use sha2::Digest;

use super::super::{CommitmentV3, PartitionV3};
use super::bounded::deserialize_bounded_vec;
use super::{
    SemanticAssetFlowV2, SemanticAuthorityUseV2, SemanticValueLeafRecordV2, ValueNodeErrorV4,
    MAX_SEMANTIC_ASSET_FLOWS_V2, MAX_SEMANTIC_AUTHORITY_USES_V2, MAX_SEMANTIC_VALUE_RECORDS_V2,
    SEMANTIC_SUBTREE_VERSION_V2,
};

mod codec;
pub(super) mod hash;
mod validate;

pub use codec::{decode_exact_semantic_subtree_v2, encode_semantic_subtree_v2};
use hash::{
    checked_len_u64, commitment, derive_roots_from_input, derive_roots_from_subtree, domain_hasher,
    require_root, write_asset_flows, write_authority_uses, write_commitment, write_leaf_records,
    write_u16, write_u64,
};
use validate::{validate_input, validate_subtree};

const SEMANTIC_SUBTREE_HASH_DOMAIN_V2: &[u8] = b"zenodex.zrpf.semantic_subtree_hash.v2";

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticSubtreeInputV2 {
    pub value_profile_id: CommitmentV3,
    pub accounting_domain_id: CommitmentV3,
    pub atoms_unit_id: CommitmentV3,
    pub state_root_scheme_id: CommitmentV3,
    pub scope_hash: CommitmentV3,
    pub lane_id_hash: CommitmentV3,
    pub partition: PartitionV3,
    pub raw_subtree_pre_state_root: CommitmentV3,
    pub raw_subtree_post_state_root: CommitmentV3,
    pub represented_row_count: u64,
    pub leaf_records: Vec<SemanticValueLeafRecordV2>,
    pub authority_grants_root: CommitmentV3,
    pub asset_flows: Vec<SemanticAssetFlowV2>,
    pub authority_uses: Vec<SemanticAuthorityUseV2>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
/// Bounded self-consistent semantic residual summary with no proof authority.
pub struct SemanticSubtreeV2 {
    semantic_subtree_version: u16,
    value_profile_id: CommitmentV3,
    accounting_domain_id: CommitmentV3,
    atoms_unit_id: CommitmentV3,
    state_root_scheme_id: CommitmentV3,
    scope_hash: CommitmentV3,
    lane_id_hash: CommitmentV3,
    partition: PartitionV3,
    raw_subtree_pre_state_root: CommitmentV3,
    raw_subtree_post_state_root: CommitmentV3,
    leaf_count: u64,
    represented_row_count: u64,
    leaf_records: Vec<SemanticValueLeafRecordV2>,
    authority_grants_root: CommitmentV3,
    asset_flows: Vec<SemanticAssetFlowV2>,
    authority_uses: Vec<SemanticAuthorityUseV2>,
    semantic_leaf_records_root: CommitmentV3,
    ordered_transaction_roots_root: CommitmentV3,
    state_chain_root: CommitmentV3,
    asset_flows_root: CommitmentV3,
    authority_uses_root: CommitmentV3,
    value_subtree_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SemanticSubtreeWireV2 {
    semantic_subtree_version: u16,
    value_profile_id: CommitmentV3,
    accounting_domain_id: CommitmentV3,
    atoms_unit_id: CommitmentV3,
    state_root_scheme_id: CommitmentV3,
    scope_hash: CommitmentV3,
    lane_id_hash: CommitmentV3,
    partition: PartitionV3,
    raw_subtree_pre_state_root: CommitmentV3,
    raw_subtree_post_state_root: CommitmentV3,
    leaf_count: u64,
    represented_row_count: u64,
    #[serde(deserialize_with = "deserialize_leaf_records")]
    leaf_records: Vec<SemanticValueLeafRecordV2>,
    authority_grants_root: CommitmentV3,
    #[serde(deserialize_with = "deserialize_asset_flows")]
    asset_flows: Vec<SemanticAssetFlowV2>,
    #[serde(deserialize_with = "deserialize_authority_uses")]
    authority_uses: Vec<SemanticAuthorityUseV2>,
    semantic_leaf_records_root: CommitmentV3,
    ordered_transaction_roots_root: CommitmentV3,
    state_chain_root: CommitmentV3,
    asset_flows_root: CommitmentV3,
    authority_uses_root: CommitmentV3,
    value_subtree_root: CommitmentV3,
}

fn deserialize_leaf_records<'de, D>(
    deserializer: D,
) -> Result<Vec<SemanticValueLeafRecordV2>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_vec(
        deserializer,
        MAX_SEMANTIC_VALUE_RECORDS_V2,
        "semantic leaves",
    )
}

fn deserialize_asset_flows<'de, D>(deserializer: D) -> Result<Vec<SemanticAssetFlowV2>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_vec(
        deserializer,
        MAX_SEMANTIC_ASSET_FLOWS_V2,
        "semantic asset flows",
    )
}

fn deserialize_authority_uses<'de, D>(
    deserializer: D,
) -> Result<Vec<SemanticAuthorityUseV2>, D::Error>
where
    D: Deserializer<'de>,
{
    deserialize_bounded_vec(
        deserializer,
        MAX_SEMANTIC_AUTHORITY_USES_V2,
        "semantic authority uses",
    )
}

impl SemanticSubtreeV2 {
    /// Derive every semantic root from ordered records and residual summaries.
    pub fn derive(input: SemanticSubtreeInputV2) -> Result<Self, ValueNodeErrorV4> {
        validate_input(&input)?;
        let leaf_count = checked_len_u64(input.leaf_records.len(), "leaf_count")?;
        let roots = derive_roots_from_input(&input, leaf_count)?;
        let subtree = Self {
            semantic_subtree_version: SEMANTIC_SUBTREE_VERSION_V2,
            value_profile_id: input.value_profile_id,
            accounting_domain_id: input.accounting_domain_id,
            atoms_unit_id: input.atoms_unit_id,
            state_root_scheme_id: input.state_root_scheme_id,
            scope_hash: input.scope_hash,
            lane_id_hash: input.lane_id_hash,
            partition: input.partition,
            raw_subtree_pre_state_root: input.raw_subtree_pre_state_root,
            raw_subtree_post_state_root: input.raw_subtree_post_state_root,
            leaf_count,
            represented_row_count: input.represented_row_count,
            leaf_records: input.leaf_records,
            authority_grants_root: input.authority_grants_root,
            asset_flows: input.asset_flows,
            authority_uses: input.authority_uses,
            semantic_leaf_records_root: roots.semantic_leaf_records_root,
            ordered_transaction_roots_root: roots.ordered_transaction_roots_root,
            state_chain_root: roots.state_chain_root,
            asset_flows_root: roots.asset_flows_root,
            authority_uses_root: roots.authority_uses_root,
            value_subtree_root: roots.value_subtree_root,
        };
        subtree.validate()?;
        Ok(subtree)
    }

    pub fn validate(&self) -> Result<(), ValueNodeErrorV4> {
        if self.semantic_subtree_version != SEMANTIC_SUBTREE_VERSION_V2 {
            return Err(ValueNodeErrorV4::InvalidSemanticSubtreeVersion(
                self.semantic_subtree_version,
            ));
        }
        validate_subtree(self)?;
        if self.leaf_count != checked_len_u64(self.leaf_records.len(), "leaf_count")? {
            return Err(ValueNodeErrorV4::LeafCountMismatch);
        }
        let roots = derive_roots_from_subtree(self)?;
        require_root(
            self.semantic_leaf_records_root,
            roots.semantic_leaf_records_root,
            "semantic_leaf_records_root",
        )?;
        require_root(
            self.ordered_transaction_roots_root,
            roots.ordered_transaction_roots_root,
            "ordered_transaction_roots_root",
        )?;
        require_root(
            self.state_chain_root,
            roots.state_chain_root,
            "state_chain_root",
        )?;
        require_root(
            self.asset_flows_root,
            roots.asset_flows_root,
            "asset_flows_root",
        )?;
        require_root(
            self.authority_uses_root,
            roots.authority_uses_root,
            "authority_uses_root",
        )?;
        require_root(
            self.value_subtree_root,
            roots.value_subtree_root,
            "value_subtree_root",
        )
    }

    pub fn canonical_hash(&self) -> Result<CommitmentV3, ValueNodeErrorV4> {
        self.validate()?;
        let mut hasher = domain_hasher(SEMANTIC_SUBTREE_HASH_DOMAIN_V2)?;
        write_u16(&mut hasher, self.semantic_subtree_version);
        for value in [
            self.value_profile_id,
            self.accounting_domain_id,
            self.atoms_unit_id,
            self.state_root_scheme_id,
            self.scope_hash,
            self.lane_id_hash,
        ] {
            write_commitment(&mut hasher, value);
        }
        write_u64(&mut hasher, self.partition.start());
        write_u64(&mut hasher, self.partition.end_exclusive());
        write_commitment(&mut hasher, self.raw_subtree_pre_state_root);
        write_commitment(&mut hasher, self.raw_subtree_post_state_root);
        write_u64(&mut hasher, self.leaf_count);
        write_u64(&mut hasher, self.represented_row_count);
        write_leaf_records(&mut hasher, &self.leaf_records)?;
        write_commitment(&mut hasher, self.authority_grants_root);
        write_asset_flows(&mut hasher, &self.asset_flows)?;
        write_authority_uses(&mut hasher, &self.authority_uses)?;
        for value in [
            self.semantic_leaf_records_root,
            self.ordered_transaction_roots_root,
            self.state_chain_root,
            self.asset_flows_root,
            self.authority_uses_root,
            self.value_subtree_root,
        ] {
            write_commitment(&mut hasher, value);
        }
        commitment(hasher.finalize().into())
    }

    pub const fn scope_hash(&self) -> CommitmentV3 {
        self.scope_hash
    }

    pub const fn lane_id_hash(&self) -> CommitmentV3 {
        self.lane_id_hash
    }

    pub const fn partition(&self) -> PartitionV3 {
        self.partition
    }

    pub const fn leaf_count(&self) -> u64 {
        self.leaf_count
    }

    pub const fn represented_row_count(&self) -> u64 {
        self.represented_row_count
    }

    pub fn leaf_records(&self) -> &[SemanticValueLeafRecordV2] {
        &self.leaf_records
    }

    pub fn asset_flows(&self) -> &[SemanticAssetFlowV2] {
        &self.asset_flows
    }

    pub fn authority_uses(&self) -> &[SemanticAuthorityUseV2] {
        &self.authority_uses
    }

    pub const fn authority_grants_root(&self) -> CommitmentV3 {
        self.authority_grants_root
    }

    pub const fn ordered_transaction_roots_root(&self) -> CommitmentV3 {
        self.ordered_transaction_roots_root
    }

    pub const fn semantic_leaf_records_root(&self) -> CommitmentV3 {
        self.semantic_leaf_records_root
    }

    pub const fn state_chain_root(&self) -> CommitmentV3 {
        self.state_chain_root
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

    pub const fn raw_subtree_pre_state_root(&self) -> CommitmentV3 {
        self.raw_subtree_pre_state_root
    }

    pub const fn raw_subtree_post_state_root(&self) -> CommitmentV3 {
        self.raw_subtree_post_state_root
    }

    fn from_wire(wire: SemanticSubtreeWireV2) -> Result<Self, ValueNodeErrorV4> {
        let subtree = Self {
            semantic_subtree_version: wire.semantic_subtree_version,
            value_profile_id: wire.value_profile_id,
            accounting_domain_id: wire.accounting_domain_id,
            atoms_unit_id: wire.atoms_unit_id,
            state_root_scheme_id: wire.state_root_scheme_id,
            scope_hash: wire.scope_hash,
            lane_id_hash: wire.lane_id_hash,
            partition: wire.partition,
            raw_subtree_pre_state_root: wire.raw_subtree_pre_state_root,
            raw_subtree_post_state_root: wire.raw_subtree_post_state_root,
            leaf_count: wire.leaf_count,
            represented_row_count: wire.represented_row_count,
            leaf_records: wire.leaf_records,
            authority_grants_root: wire.authority_grants_root,
            asset_flows: wire.asset_flows,
            authority_uses: wire.authority_uses,
            semantic_leaf_records_root: wire.semantic_leaf_records_root,
            ordered_transaction_roots_root: wire.ordered_transaction_roots_root,
            state_chain_root: wire.state_chain_root,
            asset_flows_root: wire.asset_flows_root,
            authority_uses_root: wire.authority_uses_root,
            value_subtree_root: wire.value_subtree_root,
        };
        subtree.validate()?;
        Ok(subtree)
    }
}

impl<'de> Deserialize<'de> for SemanticSubtreeV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        Self::from_wire(SemanticSubtreeWireV2::deserialize(deserializer)?)
            .map_err(de::Error::custom)
    }
}
