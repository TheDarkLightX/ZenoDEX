use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::asset_transfer_types::ACCOUNT_CUSTODY_DOMAIN_V1;
use crate::canonical::{
    hash_economic_command_body_v1, hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1,
    RootV1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::proof::LaneModuleTransitionJournalV1;
use crate::release::LaneIdV1;
use crate::state::{AssetSupplyV1, EconomicAmountV1};

pub const MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1: &str =
    "zenodex/managed-asset-lifecycle-module/v1";
pub const MANAGED_ASSET_ISSUE_COMMAND_KIND_V1: &str = "managed_asset_issue";
pub const MANAGED_ASSET_BURN_COMMAND_KIND_V1: &str = "managed_asset_burn";

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ManagedAssetClassV1 {
    #[serde(rename = "tau_native_coin")]
    TAU_NATIVE_COIN,
    #[serde(rename = "canonical_zusd")]
    CANONICAL_ZUSD,
    #[serde(rename = "lp_share")]
    LP_SHARE,
    #[serde(rename = "zdex_protocol_token")]
    ZDEX_PROTOCOL_TOKEN,
    #[serde(rename = "sealed_bid_payment_or_inventory")]
    SEALED_BID_PAYMENT_OR_INVENTORY,
    #[serde(rename = "registered_ordinary_token")]
    REGISTERED_ORDINARY_TOKEN,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ManagedAssetLifecycleRejectCodeV1 {
    RELEASE_MISMATCH,
    UNKNOWN_COMMAND,
    UNKNOWN_ASSET,
    DISABLED_ASSET,
    GENERIC_AUTHORITY_FORBIDDEN,
    ISSUE_DISABLED,
    BURN_DISABLED,
    UNAUTHORIZED_SUBJECT,
    AUTHORITY_PROFILE_MISMATCH,
    ZERO_AMOUNT,
    EFFECT_DELTA_OVERFLOW,
    INSUFFICIENT_BALANCE,
    BALANCE_OVERFLOW,
    SUPPLY_OVERFLOW,
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecyclePolicyV1 {
    pub asset: String,
    pub asset_class: ManagedAssetClassV1,
    pub issue_authority_subject: Option<String>,
    pub issue_policy_root: Option<RootV1>,
    pub burn_policy_root: Option<RootV1>,
    pub enabled: bool,
}

impl ManagedAssetLifecyclePolicyV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.asset, "managed asset lifecycle policy asset")?;
        if self.issue_authority_subject.is_some() != self.issue_policy_root.is_some() {
            return Err(AbiErrorV1::InvalidBinding(
                "managed asset issue authority pair",
            ));
        }
        if let Some(subject) = &self.issue_authority_subject {
            validate_token_v1(subject, "managed asset issue authority subject")?;
        }
        if let Some(root) = &self.issue_policy_root {
            root.validate("managed asset issue policy root", false)?;
        }
        if let Some(root) = &self.burn_policy_root {
            root.validate("managed asset burn policy root", false)?;
        }
        if self.asset_class != ManagedAssetClassV1::REGISTERED_ORDINARY_TOKEN
            && (self.issue_policy_root.is_some() || self.burn_policy_root.is_some())
        {
            return Err(AbiErrorV1::InvalidBinding(
                "generic authority on protocol-managed asset",
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleStateV1 {
    pub schema: String,
    pub module_release_id: RootV1,
    pub policies: Vec<ManagedAssetLifecyclePolicyV1>,
    pub balances: Vec<EconomicAmountV1>,
    pub supplies: Vec<AssetSupplyV1>,
}

impl ManagedAssetLifecycleStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.module_release_id
            .validate("managed asset module release id", false)?;
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
            return Err(AbiErrorV1::InvalidOrder("managed asset policies"));
        }
        if self.supplies.len() != self.policies.len()
            || self
                .supplies
                .iter()
                .zip(&self.policies)
                .any(|(supply, policy)| supply.asset != policy.asset)
        {
            return Err(AbiErrorV1::InvalidBinding(
                "managed asset policy supply coverage",
            ));
        }
        for supply in &self.supplies {
            validate_token_v1(&supply.asset, "managed asset supply asset")?;
        }
        Ok(())
    }

    fn validate_balances(&self) -> AbiResultV1<()> {
        let mut totals = BTreeMap::<&str, u128>::new();
        let mut previous_key: Option<(String, String, String)> = None;
        for balance in &self.balances {
            validate_token_v1(&balance.owner, "managed asset balance owner")?;
            validate_token_v1(&balance.asset, "managed asset balance asset")?;
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1 || balance.amount_atoms == 0 {
                return Err(AbiErrorV1::InvalidBinding("managed asset balance"));
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
                return Err(AbiErrorV1::InvalidOrder("managed asset balances"));
            }
            previous_key = Some(key);
            let total = totals
                .get(balance.asset.as_str())
                .copied()
                .unwrap_or(0)
                .checked_add(balance.amount_atoms)
                .ok_or(AbiErrorV1::Conservation(
                    "managed asset account total overflow",
                ))?;
            totals.insert(balance.asset.as_str(), total);
        }
        for (supply, policy) in self.supplies.iter().zip(&self.policies) {
            let account_total = totals.remove(supply.asset.as_str()).unwrap_or(0);
            if account_total > supply.amount_atoms {
                return Err(AbiErrorV1::Conservation(
                    "managed asset account balances exceed supply",
                ));
            }
            if policy.asset_class == ManagedAssetClassV1::REGISTERED_ORDINARY_TOKEN
                && account_total != supply.amount_atoms
            {
                return Err(AbiErrorV1::Conservation(
                    "registered ordinary token account supply closure",
                ));
            }
        }
        if !totals.is_empty() {
            return Err(AbiErrorV1::InvalidBinding(
                "managed asset unknown balance asset",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("managed-asset-lifecycle-state-v1", self)
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
            .ok_or(AbiErrorV1::InvalidBinding("managed asset unknown supply"))
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleContextV1 {
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub subject_id: String,
    pub grant_root: RootV1,
}

impl ManagedAssetLifecycleContextV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.chain_id, "managed asset context chain")?;
        self.deployment_root
            .validate("managed asset context deployment", false)?;
        self.profile_root
            .validate("managed asset context profile", false)?;
        self.module_release_id
            .validate("managed asset context module release", false)?;
        self.command_occurrence_id
            .validate("managed asset context occurrence", false)?;
        validate_token_v1(&self.subject_id, "managed asset context subject")?;
        self.grant_root
            .validate("managed asset context grant", false)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleCommandV1 {
    pub command_kind: String,
    pub asset: String,
    pub account_owner: String,
    pub amount_atoms: u128,
}

impl ManagedAssetLifecycleCommandV1 {
    pub(crate) fn validate(&self) -> AbiResultV1<()> {
        validate_token_v1(&self.command_kind, "managed asset command kind")?;
        validate_token_v1(&self.asset, "managed asset command asset")?;
        validate_token_v1(&self.account_owner, "managed asset command account owner")
    }

    pub fn command_body_hash(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_economic_command_body_v1(&self.command_kind, self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleAcceptedV1 {
    pub post_state: ManagedAssetLifecycleStateV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub module_journal: LaneModuleTransitionJournalV1,
}

impl ManagedAssetLifecycleAcceptedV1 {
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
                "managed asset accepted module journal",
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
pub struct ManagedAssetLifecycleRejectedV1 {
    pub code: ManagedAssetLifecycleRejectCodeV1,
    pub pre_state_root: RootV1,
    pub post_state_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ManagedAssetLifecycleResultV1 {
    Accepted(Box<ManagedAssetLifecycleAcceptedV1>),
    Rejected(Box<ManagedAssetLifecycleRejectedV1>),
}
