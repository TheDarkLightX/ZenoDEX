use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use zenodex_zrpf_protocol_v3::{CommitmentV3, MAX_VALUE_TRANSFER_ACTION_INDEX_V2};

use crate::hash::operation_id_v1;
use crate::ZusdValueFlowErrorV1;

pub const ZUSD_VALUE_OPERATION_VERSION_V1: u16 = 1;
pub const MAX_ZUSD_VALUE_FLOW_OPERATIONS_V1: usize = 128;
pub const MAX_ZUSD_AMOUNT_ATOMS_V1: u128 = 1_000_000_000_000_000_000_000_000_000_000;
pub const ZUSD_BPS_SCALE_V1: u16 = 10_000;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ZusdValueOperationKindV1 {
    DepositCollateral,
    WithdrawCollateral,
    MintZusd,
    RepayBurn,
    StabilityPoolDeposit,
    StabilityPoolWithdraw,
    RedeemZusd,
    Liquidate,
}

impl ZusdValueOperationKindV1 {
    pub const fn tag(self) -> u8 {
        match self {
            Self::DepositCollateral => 1,
            Self::WithdrawCollateral => 2,
            Self::MintZusd => 3,
            Self::RepayBurn => 4,
            Self::StabilityPoolDeposit => 5,
            Self::StabilityPoolWithdraw => 6,
            Self::RedeemZusd => 7,
            Self::Liquidate => 8,
        }
    }

    fn from_tag(tag: u8) -> Result<Self, ZusdValueFlowErrorV1> {
        match tag {
            1 => Ok(Self::DepositCollateral),
            2 => Ok(Self::WithdrawCollateral),
            3 => Ok(Self::MintZusd),
            4 => Ok(Self::RepayBurn),
            5 => Ok(Self::StabilityPoolDeposit),
            6 => Ok(Self::StabilityPoolWithdraw),
            7 => Ok(Self::RedeemZusd),
            8 => Ok(Self::Liquidate),
            _ => Err(ZusdValueFlowErrorV1::InvalidDerivedCommitment(
                "operation_kind",
            )),
        }
    }
}

impl Serialize for ZusdValueOperationKindV1 {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        serializer.serialize_u8(self.tag())
    }
}

impl<'de> Deserialize<'de> for ZusdValueOperationKindV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let tag = u8::deserialize(deserializer)?;
        Self::from_tag(tag).map_err(de::Error::custom)
    }
}

/// Untrusted operation input. `ZusdValueOperationV1::new` closes its shape.
///
/// Variant order is part of the V1 Postcard ABI and must not be reordered.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub enum ZusdValueOperationInputV1 {
    DepositCollateral {
        action_index: u32,
        depositor_scope_id: CommitmentV3,
        vault_scope_id: CommitmentV3,
        collateral_atoms: u128,
    },
    WithdrawCollateral {
        action_index: u32,
        recipient_scope_id: CommitmentV3,
        vault_scope_id: CommitmentV3,
        collateral_atoms: u128,
    },
    MintZusd {
        action_index: u32,
        recipient_scope_id: CommitmentV3,
        vault_scope_id: CommitmentV3,
        principal_atoms: u128,
        fee_bps: u16,
    },
    RepayBurn {
        action_index: u32,
        payer_scope_id: CommitmentV3,
        vault_scope_id: CommitmentV3,
        zusd_atoms: u128,
    },
    StabilityPoolDeposit {
        action_index: u32,
        depositor_scope_id: CommitmentV3,
        zusd_atoms: u128,
    },
    StabilityPoolWithdraw {
        action_index: u32,
        recipient_scope_id: CommitmentV3,
        zusd_atoms: u128,
    },
    RedeemZusd {
        action_index: u32,
        redeemer_scope_id: CommitmentV3,
        vault_scope_id: CommitmentV3,
        zusd_atoms: u128,
        oracle_price_e8: u128,
        redemption_fee_bps: u16,
        proposed_oracle_binding_hash: CommitmentV3,
    },
    Liquidate {
        action_index: u32,
        vault_scope_id: CommitmentV3,
        liquidator_scope_id: CommitmentV3,
        debt_zusd_atoms: u128,
        collateral_atoms: u128,
        gas_comp_fixed_collateral_atoms: u128,
        gas_comp_bps: u16,
        proposed_oracle_binding_hash: CommitmentV3,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ZusdValueOperationV1 {
    operation_version: u16,
    input: ZusdValueOperationInputV1,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ZusdValueOperationWireV1 {
    operation_version: u16,
    input: ZusdValueOperationInputV1,
}

impl ZusdValueOperationV1 {
    pub fn new(input: ZusdValueOperationInputV1) -> Result<Self, ZusdValueFlowErrorV1> {
        Self::from_parts(ZUSD_VALUE_OPERATION_VERSION_V1, input)
    }

    fn from_parts(
        operation_version: u16,
        input: ZusdValueOperationInputV1,
    ) -> Result<Self, ZusdValueFlowErrorV1> {
        let operation = Self {
            operation_version,
            input,
        };
        operation.validate_self_consistency()?;
        Ok(operation)
    }

    pub fn validate_self_consistency(&self) -> Result<(), ZusdValueFlowErrorV1> {
        if self.operation_version != ZUSD_VALUE_OPERATION_VERSION_V1 {
            return Err(ZusdValueFlowErrorV1::InvalidOperationVersion(
                self.operation_version,
            ));
        }
        require_action_index(self.action_index())?;
        validate_operation_input(&self.input)
    }

    pub const fn action_index(&self) -> u32 {
        action_index(&self.input)
    }

    pub const fn kind(&self) -> ZusdValueOperationKindV1 {
        operation_kind(&self.input)
    }

    pub const fn input(&self) -> &ZusdValueOperationInputV1 {
        &self.input
    }

    /// Returns a deterministic proposal-local operation identity.
    ///
    /// This identity authenticates no source transition and is not a global
    /// economic-action nullifier. A future authority-bearing adapter must bind
    /// the operation to its verified application, domain, source, and state.
    pub fn canonical_id(&self) -> Result<CommitmentV3, ZusdValueFlowErrorV1> {
        self.validate_self_consistency()?;
        operation_id_v1(self)
    }
}

impl<'de> Deserialize<'de> for ZusdValueOperationV1 {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ZusdValueOperationWireV1::deserialize(deserializer)?;
        Self::from_parts(wire.operation_version, wire.input).map_err(de::Error::custom)
    }
}

const fn action_index(input: &ZusdValueOperationInputV1) -> u32 {
    match input {
        ZusdValueOperationInputV1::DepositCollateral { action_index, .. }
        | ZusdValueOperationInputV1::WithdrawCollateral { action_index, .. }
        | ZusdValueOperationInputV1::MintZusd { action_index, .. }
        | ZusdValueOperationInputV1::RepayBurn { action_index, .. }
        | ZusdValueOperationInputV1::StabilityPoolDeposit { action_index, .. }
        | ZusdValueOperationInputV1::StabilityPoolWithdraw { action_index, .. }
        | ZusdValueOperationInputV1::RedeemZusd { action_index, .. }
        | ZusdValueOperationInputV1::Liquidate { action_index, .. } => *action_index,
    }
}

const fn operation_kind(input: &ZusdValueOperationInputV1) -> ZusdValueOperationKindV1 {
    match input {
        ZusdValueOperationInputV1::DepositCollateral { .. } => {
            ZusdValueOperationKindV1::DepositCollateral
        }
        ZusdValueOperationInputV1::WithdrawCollateral { .. } => {
            ZusdValueOperationKindV1::WithdrawCollateral
        }
        ZusdValueOperationInputV1::MintZusd { .. } => ZusdValueOperationKindV1::MintZusd,
        ZusdValueOperationInputV1::RepayBurn { .. } => ZusdValueOperationKindV1::RepayBurn,
        ZusdValueOperationInputV1::StabilityPoolDeposit { .. } => {
            ZusdValueOperationKindV1::StabilityPoolDeposit
        }
        ZusdValueOperationInputV1::StabilityPoolWithdraw { .. } => {
            ZusdValueOperationKindV1::StabilityPoolWithdraw
        }
        ZusdValueOperationInputV1::RedeemZusd { .. } => ZusdValueOperationKindV1::RedeemZusd,
        ZusdValueOperationInputV1::Liquidate { .. } => ZusdValueOperationKindV1::Liquidate,
    }
}

fn validate_operation_input(input: &ZusdValueOperationInputV1) -> Result<(), ZusdValueFlowErrorV1> {
    let action_index = action_index(input);
    match input {
        ZusdValueOperationInputV1::DepositCollateral {
            depositor_scope_id,
            vault_scope_id,
            collateral_atoms,
            ..
        } => {
            require_distinct_scopes(action_index, *depositor_scope_id, *vault_scope_id)?;
            require_positive_amount(action_index, "collateral_atoms", *collateral_atoms)
        }
        ZusdValueOperationInputV1::WithdrawCollateral {
            recipient_scope_id,
            vault_scope_id,
            collateral_atoms,
            ..
        } => {
            require_distinct_scopes(action_index, *recipient_scope_id, *vault_scope_id)?;
            require_positive_amount(action_index, "collateral_atoms", *collateral_atoms)
        }
        ZusdValueOperationInputV1::MintZusd {
            recipient_scope_id,
            vault_scope_id,
            principal_atoms,
            fee_bps,
            ..
        } => {
            require_distinct_scopes(action_index, *recipient_scope_id, *vault_scope_id)?;
            require_positive_amount(action_index, "principal_atoms", *principal_atoms)?;
            require_bps(action_index, *fee_bps)
        }
        ZusdValueOperationInputV1::RepayBurn {
            payer_scope_id,
            vault_scope_id,
            zusd_atoms,
            ..
        } => {
            require_distinct_scopes(action_index, *payer_scope_id, *vault_scope_id)?;
            require_positive_amount(action_index, "zusd_atoms", *zusd_atoms)
        }
        ZusdValueOperationInputV1::StabilityPoolDeposit { zusd_atoms, .. }
        | ZusdValueOperationInputV1::StabilityPoolWithdraw { zusd_atoms, .. } => {
            require_positive_amount(action_index, "zusd_atoms", *zusd_atoms)
        }
        ZusdValueOperationInputV1::RedeemZusd {
            redeemer_scope_id,
            vault_scope_id,
            zusd_atoms,
            oracle_price_e8,
            redemption_fee_bps,
            ..
        } => {
            require_distinct_scopes(action_index, *redeemer_scope_id, *vault_scope_id)?;
            require_positive_amount(action_index, "zusd_atoms", *zusd_atoms)?;
            require_oracle_price(action_index, *oracle_price_e8)?;
            require_bps(action_index, *redemption_fee_bps)
        }
        ZusdValueOperationInputV1::Liquidate {
            vault_scope_id,
            liquidator_scope_id,
            debt_zusd_atoms,
            collateral_atoms,
            gas_comp_fixed_collateral_atoms,
            gas_comp_bps,
            ..
        } => {
            require_distinct_scopes(action_index, *vault_scope_id, *liquidator_scope_id)?;
            require_positive_amount(action_index, "debt_zusd_atoms", *debt_zusd_atoms)?;
            require_positive_amount(action_index, "collateral_atoms", *collateral_atoms)?;
            require_bounded_amount(
                action_index,
                "gas_comp_fixed_collateral_atoms",
                *gas_comp_fixed_collateral_atoms,
            )?;
            require_bps(action_index, *gas_comp_bps)
        }
    }
}

fn require_action_index(action_index: u32) -> Result<(), ZusdValueFlowErrorV1> {
    if action_index > MAX_VALUE_TRANSFER_ACTION_INDEX_V2 {
        return Err(ZusdValueFlowErrorV1::ActionIndexOutOfRange {
            actual: action_index,
            maximum: MAX_VALUE_TRANSFER_ACTION_INDEX_V2,
        });
    }
    Ok(())
}

fn require_distinct_scopes(
    action_index: u32,
    left: CommitmentV3,
    right: CommitmentV3,
) -> Result<(), ZusdValueFlowErrorV1> {
    if left == right {
        return Err(ZusdValueFlowErrorV1::ScopeAlias { action_index });
    }
    Ok(())
}

fn require_positive_amount(
    action_index: u32,
    field: &'static str,
    amount: u128,
) -> Result<(), ZusdValueFlowErrorV1> {
    if amount == 0 {
        return Err(ZusdValueFlowErrorV1::ZeroAmount { action_index });
    }
    require_bounded_amount(action_index, field, amount)
}

fn require_bounded_amount(
    action_index: u32,
    field: &'static str,
    amount: u128,
) -> Result<(), ZusdValueFlowErrorV1> {
    if amount > MAX_ZUSD_AMOUNT_ATOMS_V1 {
        return Err(ZusdValueFlowErrorV1::AmountOutOfRange {
            action_index,
            field,
        });
    }
    Ok(())
}

fn require_oracle_price(
    action_index: u32,
    oracle_price_e8: u128,
) -> Result<(), ZusdValueFlowErrorV1> {
    if oracle_price_e8 == 0 {
        return Err(ZusdValueFlowErrorV1::ZeroOraclePrice { action_index });
    }
    require_bounded_amount(action_index, "oracle_price_e8", oracle_price_e8)
}

fn require_bps(action_index: u32, bps: u16) -> Result<(), ZusdValueFlowErrorV1> {
    if bps > ZUSD_BPS_SCALE_V1 {
        return Err(ZusdValueFlowErrorV1::BasisPointsOutOfRange {
            action_index,
            actual: bps,
        });
    }
    Ok(())
}
