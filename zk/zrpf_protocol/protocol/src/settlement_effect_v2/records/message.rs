use serde::{de, Deserialize, Deserializer, Serialize};

use super::super::hash::message_effect_id_v2;
use super::super::SettlementEffectErrorV2;
use crate::{CommitmentV3, DomainIdV3, EconomicActionIdV1};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum MessageEffectKindV2 {
    OutboxEnqueue,
    InboxConsume,
}

impl MessageEffectKindV2 {
    pub(crate) const fn code(self) -> u8 {
        match self {
            Self::OutboxEnqueue => 0,
            Self::InboxConsume => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MessageEffectInputV2 {
    pub economic_action_id: EconomicActionIdV1,
    pub asset_effect_id: CommitmentV3,
    pub source_domain_id: DomainIdV3,
    pub destination_domain_id: DomainIdV3,
    pub asset_id: CommitmentV3,
    pub amount_atoms: u128,
    pub kind: MessageEffectKindV2,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MessageEffectV2 {
    economic_action_id: EconomicActionIdV1,
    asset_effect_id: CommitmentV3,
    source_domain_id: DomainIdV3,
    destination_domain_id: DomainIdV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    kind: MessageEffectKindV2,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct MessageEffectWireV2 {
    economic_action_id: EconomicActionIdV1,
    asset_effect_id: CommitmentV3,
    source_domain_id: DomainIdV3,
    destination_domain_id: DomainIdV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    kind: MessageEffectKindV2,
}

impl MessageEffectV2 {
    pub fn new(input: MessageEffectInputV2) -> Result<Self, SettlementEffectErrorV2> {
        if input.amount_atoms == 0 || input.source_domain_id == input.destination_domain_id {
            return Err(SettlementEffectErrorV2::MessageCarryMismatch);
        }
        Ok(Self {
            economic_action_id: input.economic_action_id,
            asset_effect_id: input.asset_effect_id,
            source_domain_id: input.source_domain_id,
            destination_domain_id: input.destination_domain_id,
            asset_id: input.asset_id,
            amount_atoms: input.amount_atoms,
            kind: input.kind,
        })
    }

    pub fn canonical_id(&self) -> Result<CommitmentV3, SettlementEffectErrorV2> {
        message_effect_id_v2(self)
    }

    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }
    pub const fn asset_effect_id(&self) -> CommitmentV3 {
        self.asset_effect_id
    }
    pub const fn source_domain_id(&self) -> DomainIdV3 {
        self.source_domain_id
    }
    pub const fn destination_domain_id(&self) -> DomainIdV3 {
        self.destination_domain_id
    }
    pub const fn asset_id(&self) -> CommitmentV3 {
        self.asset_id
    }
    pub const fn amount_atoms(&self) -> u128 {
        self.amount_atoms
    }
    pub const fn kind(&self) -> MessageEffectKindV2 {
        self.kind
    }
}

impl<'de> Deserialize<'de> for MessageEffectV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = MessageEffectWireV2::deserialize(deserializer)?;
        Self::new(MessageEffectInputV2 {
            economic_action_id: wire.economic_action_id,
            asset_effect_id: wire.asset_effect_id,
            source_domain_id: wire.source_domain_id,
            destination_domain_id: wire.destination_domain_id,
            asset_id: wire.asset_id,
            amount_atoms: wire.amount_atoms,
            kind: wire.kind,
        })
        .map_err(de::Error::custom)
    }
}
