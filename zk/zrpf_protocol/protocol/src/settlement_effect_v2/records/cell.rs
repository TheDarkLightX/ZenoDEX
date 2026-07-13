use serde::{de, Deserialize, Deserializer, Serialize};

use super::super::SettlementEffectErrorV2;
use crate::{CommitmentV3, EconomicActionIdV1};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ValueHashV2([u8; 32]);

impl ValueHashV2 {
    pub const fn new(bytes: [u8; 32]) -> Self {
        Self(bytes)
    }

    pub const fn as_bytes(&self) -> &[u8; 32] {
        &self.0
    }

    pub const fn into_bytes(self) -> [u8; 32] {
        self.0
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LedgerCellWriteInputV2 {
    pub economic_action_id: EconomicActionIdV1,
    pub cell_key: CommitmentV3,
    pub pre_value_hash: ValueHashV2,
    pub post_value_hash: ValueHashV2,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LedgerCellWriteV2 {
    economic_action_id: EconomicActionIdV1,
    cell_key: CommitmentV3,
    pre_value_hash: ValueHashV2,
    post_value_hash: ValueHashV2,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct LedgerCellWriteWireV2 {
    economic_action_id: EconomicActionIdV1,
    cell_key: CommitmentV3,
    pre_value_hash: ValueHashV2,
    post_value_hash: ValueHashV2,
}

impl LedgerCellWriteV2 {
    pub fn new(input: LedgerCellWriteInputV2) -> Result<Self, SettlementEffectErrorV2> {
        if input.pre_value_hash == input.post_value_hash {
            return Err(SettlementEffectErrorV2::NonChangingValue);
        }
        Ok(Self {
            economic_action_id: input.economic_action_id,
            cell_key: input.cell_key,
            pre_value_hash: input.pre_value_hash,
            post_value_hash: input.post_value_hash,
        })
    }

    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }

    pub const fn cell_key(&self) -> CommitmentV3 {
        self.cell_key
    }

    pub const fn pre_value_hash(&self) -> ValueHashV2 {
        self.pre_value_hash
    }

    pub const fn post_value_hash(&self) -> ValueHashV2 {
        self.post_value_hash
    }
}

impl<'de> Deserialize<'de> for LedgerCellWriteV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = LedgerCellWriteWireV2::deserialize(deserializer)?;
        Self::new(LedgerCellWriteInputV2 {
            economic_action_id: wire.economic_action_id,
            cell_key: wire.cell_key,
            pre_value_hash: wire.pre_value_hash,
            post_value_hash: wire.post_value_hash,
        })
        .map_err(de::Error::custom)
    }
}
