use serde::{de, Deserialize, Deserializer, Serialize};

use super::super::{CommitmentV3, PartitionV3, TaskIdV3};
use super::ValueNodeErrorV4;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemanticValueLeafRecordInputV2 {
    pub partition: PartitionV3,
    pub semantic_leaf_hash: CommitmentV3,
    pub source_claim_id: CommitmentV3,
    pub semantic_source_id: CommitmentV3,
    pub task_id: TaskIdV3,
    pub pre_state_vector_root: CommitmentV3,
    pub post_state_vector_root: CommitmentV3,
    pub transaction_root: CommitmentV3,
    pub effect_root: CommitmentV3,
    pub asset_delta_root: CommitmentV3,
    pub raw_pre_state_root: CommitmentV3,
    pub raw_post_state_root: CommitmentV3,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SemanticValueLeafRecordV2 {
    pub(super) partition: PartitionV3,
    pub(super) semantic_leaf_hash: CommitmentV3,
    pub(super) source_claim_id: CommitmentV3,
    pub(super) semantic_source_id: CommitmentV3,
    pub(super) task_id: TaskIdV3,
    pub(super) pre_state_vector_root: CommitmentV3,
    pub(super) post_state_vector_root: CommitmentV3,
    pub(super) transaction_root: CommitmentV3,
    pub(super) effect_root: CommitmentV3,
    pub(super) asset_delta_root: CommitmentV3,
    pub(super) raw_pre_state_root: CommitmentV3,
    pub(super) raw_post_state_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SemanticValueLeafRecordWireV2 {
    partition: PartitionV3,
    semantic_leaf_hash: CommitmentV3,
    source_claim_id: CommitmentV3,
    semantic_source_id: CommitmentV3,
    task_id: TaskIdV3,
    pre_state_vector_root: CommitmentV3,
    post_state_vector_root: CommitmentV3,
    transaction_root: CommitmentV3,
    effect_root: CommitmentV3,
    asset_delta_root: CommitmentV3,
    raw_pre_state_root: CommitmentV3,
    raw_post_state_root: CommitmentV3,
}

impl SemanticValueLeafRecordV2 {
    pub fn new(input: SemanticValueLeafRecordInputV2) -> Result<Self, ValueNodeErrorV4> {
        let record = Self {
            partition: input.partition,
            semantic_leaf_hash: input.semantic_leaf_hash,
            source_claim_id: input.source_claim_id,
            semantic_source_id: input.semantic_source_id,
            task_id: input.task_id,
            pre_state_vector_root: input.pre_state_vector_root,
            post_state_vector_root: input.post_state_vector_root,
            transaction_root: input.transaction_root,
            effect_root: input.effect_root,
            asset_delta_root: input.asset_delta_root,
            raw_pre_state_root: input.raw_pre_state_root,
            raw_post_state_root: input.raw_post_state_root,
        };
        record.validate(0)?;
        Ok(record)
    }

    pub(super) fn validate(&self, ordinal: usize) -> Result<(), ValueNodeErrorV4> {
        let width = self
            .partition
            .end_exclusive()
            .checked_sub(self.partition.start())
            .ok_or(ValueNodeErrorV4::NonSingletonLeafRecord { ordinal })?;
        if width != 1 {
            return Err(ValueNodeErrorV4::NonSingletonLeafRecord { ordinal });
        }
        Ok(())
    }

    pub const fn partition(&self) -> PartitionV3 {
        self.partition
    }

    pub const fn semantic_leaf_hash(&self) -> CommitmentV3 {
        self.semantic_leaf_hash
    }

    pub const fn source_claim_id(&self) -> CommitmentV3 {
        self.source_claim_id
    }

    pub const fn semantic_source_id(&self) -> CommitmentV3 {
        self.semantic_source_id
    }

    pub const fn task_id(&self) -> TaskIdV3 {
        self.task_id
    }

    pub const fn pre_state_vector_root(&self) -> CommitmentV3 {
        self.pre_state_vector_root
    }

    pub const fn post_state_vector_root(&self) -> CommitmentV3 {
        self.post_state_vector_root
    }

    pub const fn transaction_root(&self) -> CommitmentV3 {
        self.transaction_root
    }

    pub const fn effect_root(&self) -> CommitmentV3 {
        self.effect_root
    }

    pub const fn asset_delta_root(&self) -> CommitmentV3 {
        self.asset_delta_root
    }

    pub const fn raw_pre_state_root(&self) -> CommitmentV3 {
        self.raw_pre_state_root
    }

    pub const fn raw_post_state_root(&self) -> CommitmentV3 {
        self.raw_post_state_root
    }
}

impl<'de> Deserialize<'de> for SemanticValueLeafRecordV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SemanticValueLeafRecordWireV2::deserialize(deserializer)?;
        Self::new(SemanticValueLeafRecordInputV2 {
            partition: wire.partition,
            semantic_leaf_hash: wire.semantic_leaf_hash,
            source_claim_id: wire.source_claim_id,
            semantic_source_id: wire.semantic_source_id,
            task_id: wire.task_id,
            pre_state_vector_root: wire.pre_state_vector_root,
            post_state_vector_root: wire.post_state_vector_root,
            transaction_root: wire.transaction_root,
            effect_root: wire.effect_root,
            asset_delta_root: wire.asset_delta_root,
            raw_pre_state_root: wire.raw_pre_state_root,
            raw_post_state_root: wire.raw_post_state_root,
        })
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticAssetFlowInputV2 {
    pub asset_id: [u8; 32],
    pub outflow_atoms: u128,
    pub inflow_atoms: u128,
    pub issued_atoms: u128,
    pub destroyed_atoms: u128,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct SemanticAssetFlowV2 {
    pub(super) asset_id: [u8; 32],
    pub(super) outflow_atoms: u128,
    pub(super) inflow_atoms: u128,
    pub(super) issued_atoms: u128,
    pub(super) destroyed_atoms: u128,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SemanticAssetFlowWireV2 {
    asset_id: [u8; 32],
    outflow_atoms: u128,
    inflow_atoms: u128,
    issued_atoms: u128,
    destroyed_atoms: u128,
}

impl SemanticAssetFlowV2 {
    pub fn new(input: SemanticAssetFlowInputV2) -> Result<Self, ValueNodeErrorV4> {
        let flow = Self {
            asset_id: input.asset_id,
            outflow_atoms: input.outflow_atoms,
            inflow_atoms: input.inflow_atoms,
            issued_atoms: input.issued_atoms,
            destroyed_atoms: input.destroyed_atoms,
        };
        flow.validate()?;
        Ok(flow)
    }

    pub(super) fn validate(&self) -> Result<(), ValueNodeErrorV4> {
        if self.outflow_atoms == 0
            && self.inflow_atoms == 0
            && self.issued_atoms == 0
            && self.destroyed_atoms == 0
        {
            return Err(ValueNodeErrorV4::InvalidAssetFlow);
        }
        Ok(())
    }

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

impl<'de> Deserialize<'de> for SemanticAssetFlowV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SemanticAssetFlowWireV2::deserialize(deserializer)?;
        Self::new(SemanticAssetFlowInputV2 {
            asset_id: wire.asset_id,
            outflow_atoms: wire.outflow_atoms,
            inflow_atoms: wire.inflow_atoms,
            issued_atoms: wire.issued_atoms,
            destroyed_atoms: wire.destroyed_atoms,
        })
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SemanticAuthorityUseInputV2 {
    pub source_claim_id: CommitmentV3,
    pub leaf_ordinal: u64,
    pub asset_id: [u8; 32],
    pub atoms: u128,
    pub legacy_authority_root: CommitmentV3,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct SemanticAuthorityUseV2 {
    pub(super) source_claim_id: CommitmentV3,
    pub(super) leaf_ordinal: u64,
    pub(super) asset_id: [u8; 32],
    pub(super) atoms: u128,
    pub(super) legacy_authority_root: CommitmentV3,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct SemanticAuthorityUseWireV2 {
    source_claim_id: CommitmentV3,
    leaf_ordinal: u64,
    asset_id: [u8; 32],
    atoms: u128,
    legacy_authority_root: CommitmentV3,
}

impl SemanticAuthorityUseV2 {
    pub fn new(input: SemanticAuthorityUseInputV2) -> Result<Self, ValueNodeErrorV4> {
        let use_record = Self {
            source_claim_id: input.source_claim_id,
            leaf_ordinal: input.leaf_ordinal,
            asset_id: input.asset_id,
            atoms: input.atoms,
            legacy_authority_root: input.legacy_authority_root,
        };
        use_record.validate()?;
        Ok(use_record)
    }

    pub(super) fn validate(&self) -> Result<(), ValueNodeErrorV4> {
        if self.asset_id == [0; 32] || self.atoms == 0 {
            return Err(ValueNodeErrorV4::InvalidAuthorityUse);
        }
        Ok(())
    }

    pub const fn source_claim_id(&self) -> CommitmentV3 {
        self.source_claim_id
    }

    pub const fn leaf_ordinal(&self) -> u64 {
        self.leaf_ordinal
    }

    pub const fn asset_id(&self) -> [u8; 32] {
        self.asset_id
    }

    pub const fn atoms(&self) -> u128 {
        self.atoms
    }

    pub const fn legacy_authority_root(&self) -> CommitmentV3 {
        self.legacy_authority_root
    }
}

impl<'de> Deserialize<'de> for SemanticAuthorityUseV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = SemanticAuthorityUseWireV2::deserialize(deserializer)?;
        Self::new(SemanticAuthorityUseInputV2 {
            source_claim_id: wire.source_claim_id,
            leaf_ordinal: wire.leaf_ordinal,
            asset_id: wire.asset_id,
            atoms: wire.atoms,
            legacy_authority_root: wire.legacy_authority_root,
        })
        .map_err(de::Error::custom)
    }
}
