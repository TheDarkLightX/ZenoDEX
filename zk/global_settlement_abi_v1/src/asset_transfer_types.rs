use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::canonical::{
    hash_economic_command_body_v1, hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1,
    RootV1, MAX_ASSET_BALANCE_ROWS_V1, MAX_ASSET_POLICY_ROWS_V1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::proof::LaneModuleTransitionJournalV1;
use crate::release::LaneIdV1;
use crate::state::{AssetSupplyV1, EconomicAmountV1};

pub const ASSET_TRANSFER_MODULE_SCHEMA_V1: &str = "zenodex/asset-transfer-module/v1";
pub const ASSET_TRANSFER_COMMAND_KIND_V1: &str = "asset_transfer";
pub const ACCOUNT_CUSTODY_DOMAIN_V1: &str = "accounts";

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetTransferRejectCodeV1 {
    RELEASE_MISMATCH,
    UNKNOWN_COMMAND,
    UNKNOWN_ASSET,
    DISABLED_ASSET,
    UNAUTHORIZED_SUBJECT,
    SELF_TRANSFER,
    ZERO_AMOUNT,
    FEE_LIMIT_EXCEEDED,
    EFFECT_DELTA_OVERFLOW,
    INSUFFICIENT_BALANCE,
    BALANCE_OVERFLOW,
    POST_STATE_RESOURCE_BOUND_EXCEEDED,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferPolicyV1 {
    pub asset: String,
    pub fee_owner: String,
    pub transfer_fee_atoms: u128,
    pub enabled: bool,
}

impl AssetTransferPolicyV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "asset transfer policy asset")?;
        validate_token_v1(&self.fee_owner, "asset transfer policy fee owner")
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferStateV1 {
    pub schema: String,
    pub module_release_id: RootV1,
    pub policies: Vec<AssetTransferPolicyV1>,
    pub balances: Vec<EconomicAmountV1>,
    pub supplies: Vec<AssetSupplyV1>,
}

impl AssetTransferStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ASSET_TRANSFER_MODULE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.module_release_id
            .validate("asset transfer module release id", false)?;
        if self.policies.len() > MAX_ASSET_POLICY_ROWS_V1
            || self.supplies.len() > MAX_ASSET_POLICY_ROWS_V1
        {
            return Err(AbiErrorV1::InvalidBounds(
                "asset transfer policy or supply rows",
            ));
        }
        if self.balances.len() > MAX_ASSET_BALANCE_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds("asset transfer balance rows"));
        }
        self.validate_policy_supply_coverage()?;
        self.validate_balances()
    }

    fn validate_policy_supply_coverage(&self) -> AbiResultV1<()> {
        for policy in &self.policies {
            policy.validate()?;
        }
        if self
            .policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV1::InvalidOrder("asset transfer policies"));
        }
        if self.supplies.len() != self.policies.len()
            || self
                .supplies
                .iter()
                .zip(&self.policies)
                .any(|(supply, policy)| supply.asset != policy.asset)
        {
            return Err(AbiErrorV1::InvalidBinding(
                "asset transfer policy supply coverage",
            ));
        }
        for supply in &self.supplies {
            validate_token_v1(&supply.asset, "asset transfer supply asset")?;
        }
        Ok(())
    }

    fn validate_balances(&self) -> AbiResultV1<()> {
        let mut totals = BTreeMap::<&str, u128>::new();
        let mut previous_key: Option<(String, String, String)> = None;
        for balance in &self.balances {
            validate_token_v1(&balance.owner, "asset transfer balance owner")?;
            validate_token_v1(&balance.asset, "asset transfer balance asset")?;
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1 || balance.amount_atoms == 0 {
                return Err(AbiErrorV1::InvalidBinding("asset transfer balance"));
            }
            let key = (
                balance.asset.clone(),
                balance.owner.clone(),
                balance.custody_domain.clone(),
            );
            if previous_key
                .as_ref()
                .is_some_and(|previous| previous >= &key)
            {
                return Err(AbiErrorV1::InvalidOrder("asset transfer balances"));
            }
            previous_key = Some(key);
            let total = totals
                .get(balance.asset.as_str())
                .copied()
                .unwrap_or(0)
                .checked_add(balance.amount_atoms)
                .ok_or(AbiErrorV1::Conservation(
                    "asset transfer account total overflow",
                ))?;
            totals.insert(balance.asset.as_str(), total);
        }
        for supply in &self.supplies {
            if totals.remove(supply.asset.as_str()).unwrap_or(0) > supply.amount_atoms {
                return Err(AbiErrorV1::Conservation(
                    "asset transfer account balances exceed supply",
                ));
            }
        }
        if !totals.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "asset transfer unknown balance asset",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("asset-transfer-state-v1", self)
    }

    pub fn balance_atoms(&self, owner: &str, asset: &str) -> u128 {
        self.balances
            .iter()
            .find(|row| row.owner == owner && row.asset == asset)
            .map(|row| row.amount_atoms)
            .unwrap_or(0)
    }

    pub fn supply_atoms(&self, asset: &str) -> AbiResultV1<u128> {
        self.supplies
            .iter()
            .find(|row| row.asset == asset)
            .map(|row| row.amount_atoms)
            .ok_or(AbiErrorV1::InvalidBinding("asset transfer unknown supply"))
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferContextV1 {
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub subject_id: String,
    pub grant_root: RootV1,
}

impl AssetTransferContextV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "asset transfer context chain")?;
        self.deployment_root
            .validate("asset transfer context deployment", false)?;
        self.profile_root
            .validate("asset transfer context profile", false)?;
        self.module_release_id
            .validate("asset transfer context module release", false)?;
        self.command_occurrence_id
            .validate("asset transfer context occurrence", false)?;
        validate_token_v1(&self.subject_id, "asset transfer context subject")?;
        self.grant_root
            .validate("asset transfer context grant", false)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferCommandV1 {
    pub command_kind: String,
    pub asset: String,
    pub sender: String,
    pub recipient: String,
    pub amount_atoms: u128,
    pub max_fee_atoms: u128,
}

impl AssetTransferCommandV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.command_kind, "asset transfer command kind")?;
        validate_token_v1(&self.asset, "asset transfer command asset")?;
        validate_token_v1(&self.sender, "asset transfer command sender")?;
        validate_token_v1(&self.recipient, "asset transfer command recipient")
    }

    pub fn command_body_hash(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_economic_command_body_v1(&self.command_kind, self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferAcceptedV1 {
    pub post_state: AssetTransferStateV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub module_journal: LaneModuleTransitionJournalV1,
}

impl AssetTransferAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
        if self.module_journal.lane_id != LaneIdV1::ASSET_TRANSFER
            || self.module_journal.module_release_id != self.post_state.module_release_id
            || self.module_journal.post_lane_root != self.post_state.state_root()?
            || self.module_journal.effect_plan_root != self.effects.effect_plan_root()?
        {
            return Err(AbiErrorV1::InvalidBinding(
                "asset transfer accepted module journal",
            ));
        }
        Ok(())
    }

    pub fn receipt_root(&self) -> &RootV1 {
        &self.module_journal.receipt_root
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetTransferRejectedV1 {
    pub code: AssetTransferRejectCodeV1,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssetTransferResultV1 {
    Accepted(Box<AssetTransferAcceptedV1>),
    Rejected(Box<AssetTransferRejectedV1>),
}
