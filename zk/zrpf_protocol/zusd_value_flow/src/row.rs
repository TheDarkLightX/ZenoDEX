use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use zenodex_zrpf_protocol_v3::{CommitmentV3, MAX_VALUE_TRANSFER_ACTION_INDEX_V2};

use crate::{ZusdValueFlowErrorV1, ZusdValueOperationKindV1, MAX_ZUSD_AMOUNT_ATOMS_V1};

pub const ZUSD_VALUE_FLOW_ROW_VERSION_V1: u16 = 1;
pub const MAX_ZUSD_VALUE_FLOW_ROWS_V1: usize = 512;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ZusdValueEffectKindV1 {
    OrdinaryDebit,
    OrdinaryCredit,
    AuthorizedMintCredit,
    AuthorizedBurnDebit,
}

impl ZusdValueEffectKindV1 {
    pub const fn tag(self) -> u8 {
        match self {
            Self::OrdinaryDebit => 1,
            Self::OrdinaryCredit => 2,
            Self::AuthorizedMintCredit => 3,
            Self::AuthorizedBurnDebit => 4,
        }
    }

    fn from_tag(tag: u8) -> Result<Self, ZusdValueFlowErrorV1> {
        match tag {
            1 => Ok(Self::OrdinaryDebit),
            2 => Ok(Self::OrdinaryCredit),
            3 => Ok(Self::AuthorizedMintCredit),
            4 => Ok(Self::AuthorizedBurnDebit),
            _ => Err(ZusdValueFlowErrorV1::InvalidRowShape),
        }
    }
}

impl Serialize for ZusdValueEffectKindV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u8(self.tag())
    }
}

impl<'de> Deserialize<'de> for ZusdValueEffectKindV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let tag = u8::deserialize(deserializer)?;
        Self::from_tag(tag).map_err(de::Error::custom)
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ZusdValueFlowRowInputV1 {
    pub operation_id: CommitmentV3,
    pub action_index: u32,
    pub leg_index: u8,
    pub operation_kind: ZusdValueOperationKindV1,
    pub effect_kind: ZusdValueEffectKindV1,
    pub asset_id: CommitmentV3,
    pub account_scope_id: CommitmentV3,
    pub amount_atoms: u128,
    pub authority_scope_id: Option<CommitmentV3>,
}

/// A derived one-sided accounting row with no independent proof authority.
///
/// Rows are exposed only after the enclosing proposal rederives and exactly
/// compares the complete ordered row set from validated operations.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize)]
pub struct ZusdValueFlowRowV1 {
    row_version: u16,
    operation_id: CommitmentV3,
    action_index: u32,
    leg_index: u8,
    operation_kind: ZusdValueOperationKindV1,
    effect_kind: ZusdValueEffectKindV1,
    asset_id: CommitmentV3,
    account_scope_id: CommitmentV3,
    debit_atoms: u128,
    credit_atoms: u128,
    authorized_mint_atoms: u128,
    authorized_burn_atoms: u128,
    authority_scope_id: Option<CommitmentV3>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZusdValueFlowRowWireV1 {
    row_version: u16,
    operation_id: CommitmentV3,
    action_index: u32,
    leg_index: u8,
    operation_kind: ZusdValueOperationKindV1,
    effect_kind: ZusdValueEffectKindV1,
    asset_id: CommitmentV3,
    account_scope_id: CommitmentV3,
    debit_atoms: u128,
    credit_atoms: u128,
    authorized_mint_atoms: u128,
    authorized_burn_atoms: u128,
    authority_scope_id: Option<CommitmentV3>,
}

impl ZusdValueFlowRowV1 {
    pub(crate) fn new(input: ZusdValueFlowRowInputV1) -> Result<Self, ZusdValueFlowErrorV1> {
        let (debit_atoms, credit_atoms, authorized_mint_atoms, authorized_burn_atoms) =
            amounts_for_kind(input.effect_kind, input.amount_atoms);
        Self::from_wire(ZusdValueFlowRowWireV1 {
            row_version: ZUSD_VALUE_FLOW_ROW_VERSION_V1,
            operation_id: input.operation_id,
            action_index: input.action_index,
            leg_index: input.leg_index,
            operation_kind: input.operation_kind,
            effect_kind: input.effect_kind,
            asset_id: input.asset_id,
            account_scope_id: input.account_scope_id,
            debit_atoms,
            credit_atoms,
            authorized_mint_atoms,
            authorized_burn_atoms,
            authority_scope_id: input.authority_scope_id,
        })
    }

    fn from_wire(wire: ZusdValueFlowRowWireV1) -> Result<Self, ZusdValueFlowErrorV1> {
        let row = Self {
            row_version: wire.row_version,
            operation_id: wire.operation_id,
            action_index: wire.action_index,
            leg_index: wire.leg_index,
            operation_kind: wire.operation_kind,
            effect_kind: wire.effect_kind,
            asset_id: wire.asset_id,
            account_scope_id: wire.account_scope_id,
            debit_atoms: wire.debit_atoms,
            credit_atoms: wire.credit_atoms,
            authorized_mint_atoms: wire.authorized_mint_atoms,
            authorized_burn_atoms: wire.authorized_burn_atoms,
            authority_scope_id: wire.authority_scope_id,
        };
        row.validate_self_consistency()?;
        Ok(row)
    }

    pub fn validate_self_consistency(&self) -> Result<(), ZusdValueFlowErrorV1> {
        if self.row_version != ZUSD_VALUE_FLOW_ROW_VERSION_V1 {
            return Err(ZusdValueFlowErrorV1::InvalidRowVersion(self.row_version));
        }
        if self.leg_index >= 4 {
            return Err(ZusdValueFlowErrorV1::InvalidRowShape);
        }
        if self.action_index > MAX_VALUE_TRANSFER_ACTION_INDEX_V2 {
            return Err(ZusdValueFlowErrorV1::ActionIndexOutOfRange {
                actual: self.action_index,
                maximum: MAX_VALUE_TRANSFER_ACTION_INDEX_V2,
            });
        }
        if [
            self.debit_atoms,
            self.credit_atoms,
            self.authorized_mint_atoms,
            self.authorized_burn_atoms,
        ]
        .into_iter()
        .any(|amount| amount > MAX_ZUSD_AMOUNT_ATOMS_V1)
        {
            return Err(ZusdValueFlowErrorV1::AmountOutOfRange {
                action_index: self.action_index,
                field: "row_amount",
            });
        }
        let valid = match self.effect_kind {
            ZusdValueEffectKindV1::OrdinaryDebit => {
                self.debit_atoms > 0
                    && self.credit_atoms == 0
                    && self.authorized_mint_atoms == 0
                    && self.authorized_burn_atoms == 0
                    && self.authority_scope_id.is_none()
            }
            ZusdValueEffectKindV1::OrdinaryCredit => {
                self.debit_atoms == 0
                    && self.credit_atoms > 0
                    && self.authorized_mint_atoms == 0
                    && self.authorized_burn_atoms == 0
                    && self.authority_scope_id.is_none()
            }
            ZusdValueEffectKindV1::AuthorizedMintCredit => {
                self.debit_atoms == 0
                    && self.credit_atoms > 0
                    && self.credit_atoms == self.authorized_mint_atoms
                    && self.authorized_burn_atoms == 0
                    && self.authority_scope_id.is_some()
            }
            ZusdValueEffectKindV1::AuthorizedBurnDebit => {
                self.debit_atoms > 0
                    && self.credit_atoms == 0
                    && self.authorized_mint_atoms == 0
                    && self.debit_atoms == self.authorized_burn_atoms
                    && self.authority_scope_id.is_some()
            }
        };
        if !valid {
            return Err(ZusdValueFlowErrorV1::InvalidRowShape);
        }
        Ok(())
    }

    pub const fn action_index(&self) -> u32 {
        self.action_index
    }

    pub const fn leg_index(&self) -> u8 {
        self.leg_index
    }

    pub const fn operation_kind(&self) -> ZusdValueOperationKindV1 {
        self.operation_kind
    }

    pub const fn effect_kind(&self) -> ZusdValueEffectKindV1 {
        self.effect_kind
    }

    pub const fn asset_id(&self) -> CommitmentV3 {
        self.asset_id
    }

    pub const fn account_scope_id(&self) -> CommitmentV3 {
        self.account_scope_id
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

    pub const fn authority_scope_id(&self) -> Option<CommitmentV3> {
        self.authority_scope_id
    }
}

impl<'de> Deserialize<'de> for ZusdValueFlowRowV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZusdValueFlowRowWireV1::deserialize(deserializer)?;
        Self::from_wire(wire).map_err(de::Error::custom)
    }
}

const fn amounts_for_kind(kind: ZusdValueEffectKindV1, amount: u128) -> (u128, u128, u128, u128) {
    match kind {
        ZusdValueEffectKindV1::OrdinaryDebit => (amount, 0, 0, 0),
        ZusdValueEffectKindV1::OrdinaryCredit => (0, amount, 0, 0),
        ZusdValueEffectKindV1::AuthorizedMintCredit => (0, amount, amount, 0),
        ZusdValueEffectKindV1::AuthorizedBurnDebit => (amount, 0, 0, amount),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn direct_row_decode_shape_rejects_amount_above_zusd_domain(
    ) -> Result<(), zenodex_zrpf_protocol_v3::ZrpfErrorV3> {
        let result = ZusdValueFlowRowV1::from_wire(ZusdValueFlowRowWireV1 {
            row_version: ZUSD_VALUE_FLOW_ROW_VERSION_V1,
            operation_id: CommitmentV3::new([1; 32])?,
            action_index: 0,
            leg_index: 0,
            operation_kind: ZusdValueOperationKindV1::DepositCollateral,
            effect_kind: ZusdValueEffectKindV1::OrdinaryDebit,
            asset_id: CommitmentV3::new([2; 32])?,
            account_scope_id: CommitmentV3::new([3; 32])?,
            debit_atoms: MAX_ZUSD_AMOUNT_ATOMS_V1 + 1,
            credit_atoms: 0,
            authorized_mint_atoms: 0,
            authorized_burn_atoms: 0,
            authority_scope_id: None,
        });
        assert_eq!(
            result,
            Err(ZusdValueFlowErrorV1::AmountOutOfRange {
                action_index: 0,
                field: "row_amount",
            })
        );
        Ok(())
    }
}
