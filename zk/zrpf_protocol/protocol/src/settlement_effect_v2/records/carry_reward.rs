use serde::{de, Deserialize, Deserializer, Serialize};

use super::super::hash::{carry_effect_id_v2, reward_effect_id_v2};
use super::super::SettlementEffectErrorV2;
use crate::{
    ActionAuthorizationBindingIdV1, AuthorizationScopeIdV1, CommitmentV3, EconomicActionIdV1,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CarryEffectKindV2 {
    Lock,
    Release,
}

impl CarryEffectKindV2 {
    pub(crate) const fn code(self) -> u8 {
        match self {
            Self::Lock => 0,
            Self::Release => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CarryEffectInputV2 {
    pub economic_action_id: EconomicActionIdV1,
    pub message_id: CommitmentV3,
    pub asset_id: CommitmentV3,
    pub amount_atoms: u128,
    pub kind: CarryEffectKindV2,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CarryEffectV2 {
    economic_action_id: EconomicActionIdV1,
    message_id: CommitmentV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    kind: CarryEffectKindV2,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct CarryEffectWireV2 {
    economic_action_id: EconomicActionIdV1,
    message_id: CommitmentV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    kind: CarryEffectKindV2,
}

impl CarryEffectV2 {
    pub fn new(input: CarryEffectInputV2) -> Result<Self, SettlementEffectErrorV2> {
        if input.amount_atoms == 0 {
            return Err(SettlementEffectErrorV2::ZeroEffect);
        }
        Ok(Self {
            economic_action_id: input.economic_action_id,
            message_id: input.message_id,
            asset_id: input.asset_id,
            amount_atoms: input.amount_atoms,
            kind: input.kind,
        })
    }

    pub fn canonical_id(&self) -> Result<CommitmentV3, SettlementEffectErrorV2> {
        carry_effect_id_v2(self)
    }

    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }
    pub const fn message_id(&self) -> CommitmentV3 {
        self.message_id
    }
    pub const fn asset_id(&self) -> CommitmentV3 {
        self.asset_id
    }
    pub const fn amount_atoms(&self) -> u128 {
        self.amount_atoms
    }
    pub const fn kind(&self) -> CarryEffectKindV2 {
        self.kind
    }
}

impl<'de> Deserialize<'de> for CarryEffectV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = CarryEffectWireV2::deserialize(deserializer)?;
        Self::new(CarryEffectInputV2 {
            economic_action_id: wire.economic_action_id,
            message_id: wire.message_id,
            asset_id: wire.asset_id,
            amount_atoms: wire.amount_atoms,
            kind: wire.kind,
        })
        .map_err(de::Error::custom)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RewardEffectInputV2 {
    pub economic_action_id: EconomicActionIdV1,
    pub asset_effect_id: CommitmentV3,
    pub recipient_cell_key: CommitmentV3,
    pub asset_id: CommitmentV3,
    pub amount_atoms: u128,
    pub authority_scope_id: AuthorizationScopeIdV1,
    pub action_authorization_binding: ActionAuthorizationBindingIdV1,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RewardEffectV2 {
    economic_action_id: EconomicActionIdV1,
    asset_effect_id: CommitmentV3,
    recipient_cell_key: CommitmentV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    authority_scope_id: AuthorizationScopeIdV1,
    action_authorization_binding: ActionAuthorizationBindingIdV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct RewardEffectWireV2 {
    economic_action_id: EconomicActionIdV1,
    asset_effect_id: CommitmentV3,
    recipient_cell_key: CommitmentV3,
    asset_id: CommitmentV3,
    amount_atoms: u128,
    authority_scope_id: AuthorizationScopeIdV1,
    action_authorization_binding: ActionAuthorizationBindingIdV1,
}

impl RewardEffectV2 {
    pub fn new(input: RewardEffectInputV2) -> Result<Self, SettlementEffectErrorV2> {
        if input.amount_atoms == 0 {
            return Err(SettlementEffectErrorV2::ZeroEffect);
        }
        Ok(Self {
            economic_action_id: input.economic_action_id,
            asset_effect_id: input.asset_effect_id,
            recipient_cell_key: input.recipient_cell_key,
            asset_id: input.asset_id,
            amount_atoms: input.amount_atoms,
            authority_scope_id: input.authority_scope_id,
            action_authorization_binding: input.action_authorization_binding,
        })
    }

    pub fn canonical_id(&self) -> Result<CommitmentV3, SettlementEffectErrorV2> {
        reward_effect_id_v2(self)
    }

    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }
    pub const fn asset_effect_id(&self) -> CommitmentV3 {
        self.asset_effect_id
    }
    pub const fn recipient_cell_key(&self) -> CommitmentV3 {
        self.recipient_cell_key
    }
    pub const fn asset_id(&self) -> CommitmentV3 {
        self.asset_id
    }
    pub const fn amount_atoms(&self) -> u128 {
        self.amount_atoms
    }
    pub const fn authority_scope_id(&self) -> AuthorizationScopeIdV1 {
        self.authority_scope_id
    }
    pub const fn action_authorization_binding(&self) -> ActionAuthorizationBindingIdV1 {
        self.action_authorization_binding
    }
}

impl<'de> Deserialize<'de> for RewardEffectV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = RewardEffectWireV2::deserialize(deserializer)?;
        Self::new(RewardEffectInputV2 {
            economic_action_id: wire.economic_action_id,
            asset_effect_id: wire.asset_effect_id,
            recipient_cell_key: wire.recipient_cell_key,
            asset_id: wire.asset_id,
            amount_atoms: wire.amount_atoms,
            authority_scope_id: wire.authority_scope_id,
            action_authorization_binding: wire.action_authorization_binding,
        })
        .map_err(de::Error::custom)
    }
}
