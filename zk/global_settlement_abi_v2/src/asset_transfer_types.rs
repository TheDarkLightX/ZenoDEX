use std::collections::BTreeMap;

use serde::{Deserialize, Deserializer, Serialize};

use crate::canonical::{
    canonical_bytes_v2, hash_economic_command_body_v2, hash_global_v2, validate_schema_v2,
    validate_token_v2, AbiErrorV2, AbiResultV2, RootV2, ValidateCanonicalV2,
};
use crate::effects::{GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2};
use crate::proof::{EconomicCommandOccurrenceV2, LaneModuleTransitionJournalV2};
use crate::resource_limits::{
    validate_asset_state_asset_count_v2, validate_asset_state_balance_row_count_v2,
    validate_rootable_asset_state_canonical_bytes_v2,
};
use crate::state::{AssetSupplyV2, EconomicAmountV2};

pub const ASSET_TRANSFER_MODULE_SCHEMA_V2: &str = "zenodex/asset-transfer-module/v2";
pub const ASSET_TRANSFER_COMMAND_KIND_V2: &str = "asset_transfer";
pub const ACCOUNT_CUSTODY_DOMAIN_V2: &str = "accounts";
pub const ASSET_ATOM_DECIMALS_V2: u8 = 8;
pub const ASSET_LANE_PRODUCTION_AUTHORITY_V2: &str = "NONE";

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "snake_case")]
pub enum AssetClassV2 {
    TauNativeCoin,
    CanonicalZusd,
    LpShare,
    ZdexProtocolToken,
    SealedBidPaymentOrInventory,
    RegisteredOrdinaryToken,
}

pub fn require_asset_class_namespace_v2(asset: &str, asset_class: AssetClassV2) -> AbiResultV2<()> {
    let expected = match asset {
        "TAU" => Some(AssetClassV2::TauNativeCoin),
        "ZDEX" => Some(AssetClassV2::ZdexProtocolToken),
        "zUSD" => Some(AssetClassV2::CanonicalZusd),
        value if value.starts_with("LP-") => Some(AssetClassV2::LpShare),
        _ => None,
    };
    if expected.is_some_and(|value| value != asset_class) {
        return Err(AbiErrorV2::InvalidBinding("protected asset class"));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetTransferRejectCodeV2 {
    MISSING_OCCURRENCE,
    OCCURRENCE_BINDING_MISMATCH,
    RELEASE_MISMATCH,
    UNKNOWN_COMMAND,
    OCCURRENCE_COMMAND_MISMATCH,
    UNKNOWN_ASSET,
    DISABLED_ASSET,
    UNREGISTERED_ASSET,
    ASSET_ORIGIN_MISMATCH,
    NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
    UNAUTHORIZED_SUBJECT,
    SELF_TRANSFER,
    ZERO_AMOUNT,
    FEE_LIMIT_EXCEEDED,
    EFFECT_DELTA_OVERFLOW,
    INSUFFICIENT_BALANCE,
    BALANCE_OVERFLOW,
}

impl AssetTransferRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MISSING_OCCURRENCE => "MISSING_OCCURRENCE",
            Self::OCCURRENCE_BINDING_MISMATCH => "OCCURRENCE_BINDING_MISMATCH",
            Self::RELEASE_MISMATCH => "RELEASE_MISMATCH",
            Self::UNKNOWN_COMMAND => "UNKNOWN_COMMAND",
            Self::OCCURRENCE_COMMAND_MISMATCH => "OCCURRENCE_COMMAND_MISMATCH",
            Self::UNKNOWN_ASSET => "UNKNOWN_ASSET",
            Self::DISABLED_ASSET => "DISABLED_ASSET",
            Self::UNREGISTERED_ASSET => "UNREGISTERED_ASSET",
            Self::ASSET_ORIGIN_MISMATCH => "ASSET_ORIGIN_MISMATCH",
            Self::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED => "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED",
            Self::UNAUTHORIZED_SUBJECT => "UNAUTHORIZED_SUBJECT",
            Self::SELF_TRANSFER => "SELF_TRANSFER",
            Self::ZERO_AMOUNT => "ZERO_AMOUNT",
            Self::FEE_LIMIT_EXCEEDED => "FEE_LIMIT_EXCEEDED",
            Self::EFFECT_DELTA_OVERFLOW => "EFFECT_DELTA_OVERFLOW",
            Self::INSUFFICIENT_BALANCE => "INSUFFICIENT_BALANCE",
            Self::BALANCE_OVERFLOW => "BALANCE_OVERFLOW",
        }
    }
}

pub const ALL_ASSET_TRANSFER_REJECT_CODES_V2: [AssetTransferRejectCodeV2; 17] = [
    AssetTransferRejectCodeV2::MISSING_OCCURRENCE,
    AssetTransferRejectCodeV2::OCCURRENCE_BINDING_MISMATCH,
    AssetTransferRejectCodeV2::RELEASE_MISMATCH,
    AssetTransferRejectCodeV2::UNKNOWN_COMMAND,
    AssetTransferRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH,
    AssetTransferRejectCodeV2::UNKNOWN_ASSET,
    AssetTransferRejectCodeV2::DISABLED_ASSET,
    AssetTransferRejectCodeV2::UNREGISTERED_ASSET,
    AssetTransferRejectCodeV2::ASSET_ORIGIN_MISMATCH,
    AssetTransferRejectCodeV2::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED,
    AssetTransferRejectCodeV2::UNAUTHORIZED_SUBJECT,
    AssetTransferRejectCodeV2::SELF_TRANSFER,
    AssetTransferRejectCodeV2::ZERO_AMOUNT,
    AssetTransferRejectCodeV2::FEE_LIMIT_EXCEEDED,
    AssetTransferRejectCodeV2::EFFECT_DELTA_OVERFLOW,
    AssetTransferRejectCodeV2::INSUFFICIENT_BALANCE,
    AssetTransferRejectCodeV2::BALANCE_OVERFLOW,
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferPolicyV2 {
    pub asset: String,
    pub fee_owner: String,
    pub transfer_fee_atoms: u128,
    pub enabled: bool,
    pub asset_class: AssetClassV2,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub asset_origin_root: Option<RootV2>,
    pub atom_decimals: u8,
}

impl AssetTransferPolicyV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.asset, "asset transfer policy asset")?;
        validate_token_v2(&self.fee_owner, "asset transfer policy fee owner")?;
        if let Some(origin) = &self.asset_origin_root {
            origin.validate("asset transfer policy origin root", false)?;
        }
        if self.atom_decimals != ASSET_ATOM_DECIMALS_V2 {
            return Err(AbiErrorV2::InvalidBinding("asset transfer atom decimals"));
        }
        require_asset_class_namespace_v2(&self.asset, self.asset_class)
    }
}

impl ValidateCanonicalV2 for AssetTransferPolicyV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferStateV2 {
    pub schema: String,
    pub module_release_id: RootV2,
    pub policies: Vec<AssetTransferPolicyV2>,
    pub balances: Vec<EconomicAmountV2>,
    pub supplies: Vec<AssetSupplyV2>,
}

impl AssetTransferStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_asset_state_asset_count_v2(self.policies.len(), "asset transfer policies")?;
        validate_asset_state_asset_count_v2(self.supplies.len(), "asset transfer supplies")?;
        validate_asset_state_balance_row_count_v2(self.balances.len(), "asset transfer balances")?;
        validate_schema_v2(
            &self.schema,
            ASSET_TRANSFER_MODULE_SCHEMA_V2,
            "asset transfer state",
        )?;
        self.module_release_id
            .validate("asset transfer module release id", false)?;
        for policy in &self.policies {
            policy.validate()?;
        }
        if self
            .policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("asset transfer policies"));
        }
        if self.supplies.len() != self.policies.len()
            || self
                .supplies
                .iter()
                .zip(&self.policies)
                .any(|(supply, policy)| supply.asset != policy.asset)
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset transfer policy supply coverage",
            ));
        }
        for supply in &self.supplies {
            supply.validate()?;
        }
        self.validate_balances()?;
        validate_rootable_asset_state_canonical_bytes_v2(
            canonical_bytes_v2(self)?.len(),
            "asset transfer state canonical encoding bytes",
        )
    }

    fn validate_balances(&self) -> AbiResultV2<()> {
        let mut totals = BTreeMap::<&str, u128>::new();
        for balance in &self.balances {
            balance.validate()?;
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V2 || balance.amount_atoms == 0 {
                return Err(AbiErrorV2::InvalidBinding("asset transfer balance"));
            }
        }
        if self
            .balances
            .windows(2)
            .any(|pair| pair[0].key() >= pair[1].key())
        {
            return Err(AbiErrorV2::InvalidOrder("asset transfer balances"));
        }
        for balance in &self.balances {
            let total = totals
                .get(balance.asset.as_str())
                .copied()
                .unwrap_or(0)
                .checked_add(balance.amount_atoms)
                .ok_or(AbiErrorV2::Conservation(
                    "asset transfer account total overflow",
                ))?;
            totals.insert(balance.asset.as_str(), total);
        }
        for supply in &self.supplies {
            if totals.remove(supply.asset.as_str()).unwrap_or(0) > supply.amount_atoms {
                return Err(AbiErrorV2::Conservation(
                    "asset transfer account balances exceed supply",
                ));
            }
        }
        if !totals.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "asset transfer unknown balance asset",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("asset-transfer-state-v2", self)
    }

    pub fn balance_atoms(&self, owner: &str, asset: &str) -> u128 {
        self.balances
            .iter()
            .find(|row| row.owner == owner && row.asset == asset)
            .map(|row| row.amount_atoms)
            .unwrap_or(0)
    }

    pub fn supply_atoms(&self, asset: &str) -> AbiResultV2<u128> {
        self.supplies
            .iter()
            .find(|row| row.asset == asset)
            .map(|row| row.amount_atoms)
            .ok_or(AbiErrorV2::InvalidBinding("asset transfer unknown supply"))
    }
}

impl ValidateCanonicalV2 for AssetTransferStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferContextV2 {
    pub writer_epoch: u64,
    pub module_release_id: RootV2,
    pub global_pre_state_root: RootV2,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub occurrence: Option<EconomicCommandOccurrenceV2>,
}

impl AssetTransferContextV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.module_release_id
            .validate("asset transfer context module release", false)?;
        self.global_pre_state_root
            .validate("asset transfer context global pre-state root", false)?;
        if let Some(occurrence) = &self.occurrence {
            occurrence.validate()?;
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for AssetTransferContextV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferCommandV2 {
    pub command_kind: String,
    pub asset: String,
    pub sender: String,
    pub recipient: String,
    pub amount_atoms: u128,
    pub max_fee_atoms: u128,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub asset_origin_root: Option<RootV2>,
}

impl AssetTransferCommandV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.command_kind, "asset transfer command kind")?;
        validate_token_v2(&self.asset, "asset transfer command asset")?;
        validate_token_v2(&self.sender, "asset transfer command sender")?;
        validate_token_v2(&self.recipient, "asset transfer command recipient")?;
        if let Some(origin) = &self.asset_origin_root {
            origin.validate("asset transfer command origin root", false)?;
        }
        Ok(())
    }

    pub fn command_body_hash(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_economic_command_body_v2(&self.command_kind, self)
    }
}

impl ValidateCanonicalV2 for AssetTransferCommandV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferAcceptedV2 {
    pub post_state: AssetTransferStateV2,
    pub effects: GlobalEconomicEffectPlanV2,
    pub module_journal: LaneModuleTransitionJournalV2,
    pub production_authority: String,
}

impl AssetTransferAcceptedV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
        if self.production_authority != ASSET_LANE_PRODUCTION_AUTHORITY_V2 {
            return Err(AbiErrorV2::InvalidBinding(
                "asset transfer production authority",
            ));
        }
        let expected_lane_write = LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: self.module_journal.pre_lane_root.clone(),
            post_root: self.module_journal.post_lane_root.clone(),
        };
        if self.effects.is_empty()
            || self.module_journal.lane_id != LaneIdV2::ASSET_TRANSFER
            || self.module_journal.module_release_id != self.post_state.module_release_id
            || self.module_journal.post_lane_root != self.post_state.state_root()?
            || self.module_journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.effects.occurrence_consumptions
                != vec![self.module_journal.command_occurrence_id.clone()]
            || self.effects.lane_writes != vec![expected_lane_write]
            || !self.module_journal.private_port_root.is_zero()
            || !self.module_journal.terminal_obligations_root.is_zero()
            || !self.module_journal.oracle_occurrence_plan_root.is_zero()
        {
            return Err(AbiErrorV2::InvalidBinding(
                "asset transfer accepted bindings",
            ));
        }
        Ok(())
    }

    pub fn receipt_root(&self) -> &RootV2 {
        &self.module_journal.receipt_root
    }
}

impl ValidateCanonicalV2 for AssetTransferAcceptedV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferRejectedV2 {
    pub code: AssetTransferRejectCodeV2,
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
    pub effects: GlobalEconomicEffectPlanV2,
}

impl AssetTransferRejectedV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.pre_state_root
            .validate("asset transfer rejected pre-state", false)?;
        self.post_state_root
            .validate("asset transfer rejected post-state", false)?;
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "asset transfer rejection is not a no-op",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for AssetTransferRejectedV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssetTransferResultV2 {
    Accepted(Box<AssetTransferAcceptedV2>),
    Rejected(Box<AssetTransferRejectedV2>),
}
