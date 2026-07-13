use serde::{de, Deserialize, Deserializer, Serialize};

use super::super::hash::asset_effect_id_v2;
use super::super::SettlementEffectErrorV2;
use crate::{
    ActionAuthorizationBindingIdV1, AuthorizationScopeIdV1, CommitmentV3, EconomicActionIdV1,
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum AssetEffectKindV2 {
    OrdinaryTransfer,
    AuthorizedMint,
    AuthorizedBurn,
    AuthorizedReward,
}

impl AssetEffectKindV2 {
    pub(crate) const fn code(self) -> u8 {
        match self {
            Self::OrdinaryTransfer => 0,
            Self::AuthorizedMint => 1,
            Self::AuthorizedBurn => 2,
            Self::AuthorizedReward => 3,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AssetEffectInputV2 {
    pub kind: AssetEffectKindV2,
    pub economic_action_id: EconomicActionIdV1,
    pub asset_id: CommitmentV3,
    pub debit_atoms: u128,
    pub credit_atoms: u128,
    pub authorized_mint_atoms: u128,
    pub authorized_burn_atoms: u128,
    pub authority_scope_id: Option<AuthorizationScopeIdV1>,
    pub action_authorization_binding: Option<ActionAuthorizationBindingIdV1>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AssetEffectV2 {
    kind: AssetEffectKindV2,
    economic_action_id: EconomicActionIdV1,
    asset_id: CommitmentV3,
    debit_atoms: u128,
    credit_atoms: u128,
    authorized_mint_atoms: u128,
    authorized_burn_atoms: u128,
    authority_scope_id: Option<AuthorizationScopeIdV1>,
    action_authorization_binding: Option<ActionAuthorizationBindingIdV1>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct AssetEffectWireV2 {
    kind: AssetEffectKindV2,
    economic_action_id: EconomicActionIdV1,
    asset_id: CommitmentV3,
    debit_atoms: u128,
    credit_atoms: u128,
    authorized_mint_atoms: u128,
    authorized_burn_atoms: u128,
    authority_scope_id: Option<AuthorizationScopeIdV1>,
    action_authorization_binding: Option<ActionAuthorizationBindingIdV1>,
}

impl AssetEffectV2 {
    pub fn new(input: AssetEffectInputV2) -> Result<Self, SettlementEffectErrorV2> {
        validate_asset_effect_shape(&input)?;
        Ok(Self {
            kind: input.kind,
            economic_action_id: input.economic_action_id,
            asset_id: input.asset_id,
            debit_atoms: input.debit_atoms,
            credit_atoms: input.credit_atoms,
            authorized_mint_atoms: input.authorized_mint_atoms,
            authorized_burn_atoms: input.authorized_burn_atoms,
            authority_scope_id: input.authority_scope_id,
            action_authorization_binding: input.action_authorization_binding,
        })
    }

    pub fn canonical_id(&self) -> Result<CommitmentV3, SettlementEffectErrorV2> {
        asset_effect_id_v2(self)
    }

    pub const fn kind(&self) -> AssetEffectKindV2 {
        self.kind
    }
    pub const fn economic_action_id(&self) -> EconomicActionIdV1 {
        self.economic_action_id
    }
    pub const fn asset_id(&self) -> CommitmentV3 {
        self.asset_id
    }
    pub const fn debit_atoms(&self) -> u128 {
        self.debit_atoms
    }
    pub const fn credit_atoms(&self) -> u128 {
        self.credit_atoms
    }
    pub const fn authorized_mint_atoms(&self) -> u128 {
        self.authorized_mint_atoms
    }
    pub const fn authorized_burn_atoms(&self) -> u128 {
        self.authorized_burn_atoms
    }
    pub const fn authority_scope_id(&self) -> Option<AuthorizationScopeIdV1> {
        self.authority_scope_id
    }
    pub const fn action_authorization_binding(&self) -> Option<ActionAuthorizationBindingIdV1> {
        self.action_authorization_binding
    }
    pub const fn requires_authorization(&self) -> bool {
        !matches!(self.kind, AssetEffectKindV2::OrdinaryTransfer)
    }
}

impl<'de> Deserialize<'de> for AssetEffectV2 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = AssetEffectWireV2::deserialize(deserializer)?;
        Self::new(AssetEffectInputV2 {
            kind: wire.kind,
            economic_action_id: wire.economic_action_id,
            asset_id: wire.asset_id,
            debit_atoms: wire.debit_atoms,
            credit_atoms: wire.credit_atoms,
            authorized_mint_atoms: wire.authorized_mint_atoms,
            authorized_burn_atoms: wire.authorized_burn_atoms,
            authority_scope_id: wire.authority_scope_id,
            action_authorization_binding: wire.action_authorization_binding,
        })
        .map_err(de::Error::custom)
    }
}

fn validate_asset_effect_shape(input: &AssetEffectInputV2) -> Result<(), SettlementEffectErrorV2> {
    if input.debit_atoms == 0
        && input.credit_atoms == 0
        && input.authorized_mint_atoms == 0
        && input.authorized_burn_atoms == 0
    {
        return Err(SettlementEffectErrorV2::ZeroEffect);
    }
    if input.authorized_mint_atoms != 0 && input.authorized_burn_atoms != 0 {
        return Err(SettlementEffectErrorV2::CombinedMintAndBurn);
    }
    let has_authority =
        input.authority_scope_id.is_some() && input.action_authorization_binding.is_some();
    let has_partial_authority =
        input.authority_scope_id.is_some() || input.action_authorization_binding.is_some();
    let valid = match input.kind {
        AssetEffectKindV2::OrdinaryTransfer => {
            !has_partial_authority
                && input.authorized_mint_atoms == 0
                && input.authorized_burn_atoms == 0
        }
        AssetEffectKindV2::AuthorizedMint => {
            has_authority
                && input.authorized_mint_atoms > 0
                && input.authorized_burn_atoms == 0
                && input.debit_atoms == 0
                && input.credit_atoms == input.authorized_mint_atoms
        }
        AssetEffectKindV2::AuthorizedBurn => {
            has_authority
                && input.authorized_burn_atoms > 0
                && input.authorized_mint_atoms == 0
                && input.credit_atoms == 0
                && input.debit_atoms == input.authorized_burn_atoms
        }
        AssetEffectKindV2::AuthorizedReward => {
            has_authority
                && input.authorized_mint_atoms == 0
                && input.authorized_burn_atoms == 0
                && input.debit_atoms > 0
                && input.debit_atoms == input.credit_atoms
        }
    };
    if valid {
        return Ok(());
    }
    if matches!(input.kind, AssetEffectKindV2::OrdinaryTransfer) && has_partial_authority {
        return Err(SettlementEffectErrorV2::UnexpectedAuthority);
    }
    if !matches!(input.kind, AssetEffectKindV2::OrdinaryTransfer) && !has_authority {
        return Err(SettlementEffectErrorV2::MissingAuthority);
    }
    Err(SettlementEffectErrorV2::InvalidEffectShape)
}
