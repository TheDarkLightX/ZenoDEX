//! Closed canonical values for the managed issue/self-burn V2 SHADOW mirror.
//!
//! These values carry no authenticated policy snapshot or production authority.

use std::collections::BTreeMap;

use serde::{Deserialize, Deserializer, Serialize};

use crate::asset_transfer_types::{
    require_asset_class_namespace_v2, AssetClassV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_ATOM_DECIMALS_V2,
};
use crate::canonical::{
    hash_economic_command_body_v2, hash_global_v2, validate_schema_v2, validate_token_v2,
    AbiErrorV2, AbiResultV2, RootV2, ValidateCanonicalV2,
};
use crate::effects::{GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2};
use crate::proof::{EconomicCommandOccurrenceV2, LaneModuleTransitionJournalV2};
use crate::state::{AssetSupplyV2, EconomicAmountV2};

pub const MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2: &str =
    "zenodex/managed-asset-lifecycle-module/v2";
pub const MANAGED_ASSET_ISSUE_COMMAND_KIND_V2: &str = "managed_asset_issue";
pub const MANAGED_ASSET_BURN_COMMAND_KIND_V2: &str = "managed_asset_burn";
pub const MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2: &str = "NONE";

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ManagedAssetLifecycleRejectCodeV2 {
    MISSING_OCCURRENCE,
    OCCURRENCE_BINDING_MISMATCH,
    RELEASE_MISMATCH,
    UNKNOWN_COMMAND,
    OCCURRENCE_COMMAND_MISMATCH,
    UNKNOWN_ASSET,
    DISABLED_ASSET,
    ASSET_CLASS_MISMATCH,
    /// Retained in the closed Python/Rust parity registry. Exact V2
    /// constructors and canonical decoding require eight decimals before
    /// transition dispatch, so this code is currently constructor-unreachable.
    ASSET_DECIMALS_MISMATCH,
    UNREGISTERED_ASSET,
    ASSET_ORIGIN_MISMATCH,
    GENERIC_AUTHORITY_FORBIDDEN,
    ISSUE_DISABLED,
    BURN_DISABLED,
    UNAUTHORIZED_SUBJECT,
    AUTHORIZATION_ROOT_MISMATCH,
    ZERO_AMOUNT,
    EFFECT_DELTA_OVERFLOW,
    INSUFFICIENT_BALANCE,
    /// Retained in the closed Python/Rust parity registry. Valid state enforces
    /// account balance at most supply, and issue updates supply first, so this
    /// code is currently invariant-unreachable.
    BALANCE_OVERFLOW,
    SUPPLY_OVERFLOW,
}

impl ManagedAssetLifecycleRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::MISSING_OCCURRENCE => "MISSING_OCCURRENCE",
            Self::OCCURRENCE_BINDING_MISMATCH => "OCCURRENCE_BINDING_MISMATCH",
            Self::RELEASE_MISMATCH => "RELEASE_MISMATCH",
            Self::UNKNOWN_COMMAND => "UNKNOWN_COMMAND",
            Self::OCCURRENCE_COMMAND_MISMATCH => "OCCURRENCE_COMMAND_MISMATCH",
            Self::UNKNOWN_ASSET => "UNKNOWN_ASSET",
            Self::DISABLED_ASSET => "DISABLED_ASSET",
            Self::ASSET_CLASS_MISMATCH => "ASSET_CLASS_MISMATCH",
            Self::ASSET_DECIMALS_MISMATCH => "ASSET_DECIMALS_MISMATCH",
            Self::UNREGISTERED_ASSET => "UNREGISTERED_ASSET",
            Self::ASSET_ORIGIN_MISMATCH => "ASSET_ORIGIN_MISMATCH",
            Self::GENERIC_AUTHORITY_FORBIDDEN => "GENERIC_AUTHORITY_FORBIDDEN",
            Self::ISSUE_DISABLED => "ISSUE_DISABLED",
            Self::BURN_DISABLED => "BURN_DISABLED",
            Self::UNAUTHORIZED_SUBJECT => "UNAUTHORIZED_SUBJECT",
            Self::AUTHORIZATION_ROOT_MISMATCH => "AUTHORIZATION_ROOT_MISMATCH",
            Self::ZERO_AMOUNT => "ZERO_AMOUNT",
            Self::EFFECT_DELTA_OVERFLOW => "EFFECT_DELTA_OVERFLOW",
            Self::INSUFFICIENT_BALANCE => "INSUFFICIENT_BALANCE",
            Self::BALANCE_OVERFLOW => "BALANCE_OVERFLOW",
            Self::SUPPLY_OVERFLOW => "SUPPLY_OVERFLOW",
        }
    }
}

pub const ALL_MANAGED_ASSET_LIFECYCLE_REJECT_CODES_V2: [ManagedAssetLifecycleRejectCodeV2; 21] = [
    ManagedAssetLifecycleRejectCodeV2::MISSING_OCCURRENCE,
    ManagedAssetLifecycleRejectCodeV2::OCCURRENCE_BINDING_MISMATCH,
    ManagedAssetLifecycleRejectCodeV2::RELEASE_MISMATCH,
    ManagedAssetLifecycleRejectCodeV2::UNKNOWN_COMMAND,
    ManagedAssetLifecycleRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH,
    ManagedAssetLifecycleRejectCodeV2::UNKNOWN_ASSET,
    ManagedAssetLifecycleRejectCodeV2::DISABLED_ASSET,
    ManagedAssetLifecycleRejectCodeV2::ASSET_CLASS_MISMATCH,
    ManagedAssetLifecycleRejectCodeV2::ASSET_DECIMALS_MISMATCH,
    ManagedAssetLifecycleRejectCodeV2::UNREGISTERED_ASSET,
    ManagedAssetLifecycleRejectCodeV2::ASSET_ORIGIN_MISMATCH,
    ManagedAssetLifecycleRejectCodeV2::GENERIC_AUTHORITY_FORBIDDEN,
    ManagedAssetLifecycleRejectCodeV2::ISSUE_DISABLED,
    ManagedAssetLifecycleRejectCodeV2::BURN_DISABLED,
    ManagedAssetLifecycleRejectCodeV2::UNAUTHORIZED_SUBJECT,
    ManagedAssetLifecycleRejectCodeV2::AUTHORIZATION_ROOT_MISMATCH,
    ManagedAssetLifecycleRejectCodeV2::ZERO_AMOUNT,
    ManagedAssetLifecycleRejectCodeV2::EFFECT_DELTA_OVERFLOW,
    ManagedAssetLifecycleRejectCodeV2::INSUFFICIENT_BALANCE,
    ManagedAssetLifecycleRejectCodeV2::BALANCE_OVERFLOW,
    ManagedAssetLifecycleRejectCodeV2::SUPPLY_OVERFLOW,
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecyclePolicyV2 {
    pub asset: String,
    pub asset_class: AssetClassV2,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub asset_origin_root: Option<RootV2>,
    pub atom_decimals: u8,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub issue_authority_subject: Option<String>,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub issue_authorization_root: Option<RootV2>,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub burn_authorization_root: Option<RootV2>,
    pub enabled: bool,
}

impl ManagedAssetLifecyclePolicyV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.asset, "managed asset policy asset")?;
        if let Some(root) = &self.asset_origin_root {
            root.validate("managed asset origin root", false)?;
        }
        if self.atom_decimals != ASSET_ATOM_DECIMALS_V2 {
            return Err(AbiErrorV2::InvalidBinding("managed asset atom decimals"));
        }
        if self.issue_authority_subject.is_some() != self.issue_authorization_root.is_some() {
            return Err(AbiErrorV2::InvalidBinding(
                "managed asset issue authority pair",
            ));
        }
        if let Some(subject) = &self.issue_authority_subject {
            validate_token_v2(subject, "managed asset issue authority subject")?;
        }
        if let Some(root) = &self.issue_authorization_root {
            root.validate("managed asset issue authorization root", false)?;
        }
        if let Some(root) = &self.burn_authorization_root {
            root.validate("managed asset burn authorization root", false)?;
        }
        require_asset_class_namespace_v2(&self.asset, self.asset_class)?;
        if self.asset_class != AssetClassV2::RegisteredOrdinaryToken
            && (self.issue_authorization_root.is_some() || self.burn_authorization_root.is_some())
        {
            return Err(AbiErrorV2::InvalidBinding(
                "generic authority on protocol-managed asset",
            ));
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for ManagedAssetLifecyclePolicyV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleStateV2 {
    pub schema: String,
    pub module_release_id: RootV2,
    pub policies: Vec<ManagedAssetLifecyclePolicyV2>,
    pub balances: Vec<EconomicAmountV2>,
    pub supplies: Vec<AssetSupplyV2>,
}

impl ManagedAssetLifecycleStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_schema_v2(
            &self.schema,
            MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2,
            "managed asset lifecycle state",
        )?;
        self.module_release_id
            .validate("managed asset module release id", false)?;
        for policy in &self.policies {
            policy.validate()?;
        }
        if self
            .policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("managed asset policies"));
        }
        if self.supplies.len() != self.policies.len()
            || self
                .supplies
                .iter()
                .zip(&self.policies)
                .any(|(supply, policy)| supply.asset != policy.asset)
        {
            return Err(AbiErrorV2::InvalidBinding(
                "managed asset policy supply coverage",
            ));
        }
        for supply in &self.supplies {
            supply.validate()?;
        }
        self.validate_balances()
    }

    fn validate_balances(&self) -> AbiResultV2<()> {
        let mut totals = BTreeMap::<&str, u128>::new();
        for balance in &self.balances {
            balance.validate()?;
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V2 || balance.amount_atoms == 0 {
                return Err(AbiErrorV2::InvalidBinding("managed asset balance"));
            }
        }
        if self
            .balances
            .windows(2)
            .any(|pair| pair[0].key() >= pair[1].key())
        {
            return Err(AbiErrorV2::InvalidOrder("managed asset balances"));
        }
        for balance in &self.balances {
            let total = totals
                .get(balance.asset.as_str())
                .copied()
                .unwrap_or(0)
                .checked_add(balance.amount_atoms)
                .ok_or(AbiErrorV2::Conservation(
                    "managed asset account total overflow",
                ))?;
            totals.insert(balance.asset.as_str(), total);
        }
        for supply in &self.supplies {
            if totals.remove(supply.asset.as_str()).unwrap_or(0) > supply.amount_atoms {
                return Err(AbiErrorV2::Conservation(
                    "managed asset account balances exceed supply",
                ));
            }
        }
        if !totals.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "managed asset unknown balance asset",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("managed-asset-lifecycle-state-v2", self)
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
            .ok_or(AbiErrorV2::InvalidBinding("managed asset unknown supply"))
    }
}

impl ValidateCanonicalV2 for ManagedAssetLifecycleStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleContextV2 {
    pub writer_epoch: u64,
    pub module_release_id: RootV2,
    pub global_pre_state_root: RootV2,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub occurrence: Option<EconomicCommandOccurrenceV2>,
}

impl ManagedAssetLifecycleContextV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.module_release_id
            .validate("managed asset context module release", false)?;
        self.global_pre_state_root
            .validate("managed asset context global pre-state root", false)?;
        if let Some(occurrence) = &self.occurrence {
            occurrence.validate()?;
        }
        Ok(())
    }
}

impl ValidateCanonicalV2 for ManagedAssetLifecycleContextV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleCommandV2 {
    pub command_kind: String,
    pub asset: String,
    pub asset_class: AssetClassV2,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub asset_origin_root: Option<RootV2>,
    pub atom_decimals: u8,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub authorization_root: Option<RootV2>,
    pub account_owner: String,
    pub amount_atoms: u128,
}

impl ManagedAssetLifecycleCommandV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_token_v2(&self.command_kind, "managed asset command kind")?;
        validate_token_v2(&self.asset, "managed asset command asset")?;
        if let Some(root) = &self.asset_origin_root {
            root.validate("managed asset command origin", false)?;
        }
        if self.atom_decimals != ASSET_ATOM_DECIMALS_V2 {
            return Err(AbiErrorV2::InvalidBinding("managed asset command decimals"));
        }
        if let Some(root) = &self.authorization_root {
            root.validate("managed asset command authorization root", false)?;
        }
        validate_token_v2(&self.account_owner, "managed asset command account owner")
    }

    pub fn command_body_hash(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_economic_command_body_v2(&self.command_kind, self)
    }
}

impl ValidateCanonicalV2 for ManagedAssetLifecycleCommandV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleAcceptedV2 {
    pub post_state: ManagedAssetLifecycleStateV2,
    pub effects: GlobalEconomicEffectPlanV2,
    pub module_journal: LaneModuleTransitionJournalV2,
}

impl ManagedAssetLifecycleAcceptedV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
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
                "managed asset accepted bindings",
            ));
        }
        Ok(())
    }

    pub fn receipt_root(&self) -> &RootV2 {
        &self.module_journal.receipt_root
    }

    pub const fn production_authority(&self) -> &'static str {
        MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2
    }
}

impl ValidateCanonicalV2 for ManagedAssetLifecycleAcceptedV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleRejectedV2 {
    pub code: ManagedAssetLifecycleRejectCodeV2,
    pub pre_state_root: RootV2,
    pub post_state_root: RootV2,
    pub effects: GlobalEconomicEffectPlanV2,
}

impl ManagedAssetLifecycleRejectedV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.pre_state_root
            .validate("managed asset rejected pre-state", false)?;
        self.post_state_root
            .validate("managed asset rejected post-state", false)?;
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "managed asset rejection is not a no-op",
            ));
        }
        Ok(())
    }

    pub fn terminal_obligations_root(&self) -> RootV2 {
        RootV2::zero()
    }

    pub fn oracle_occurrence_plan_root(&self) -> RootV2 {
        RootV2::zero()
    }

    pub const fn production_authority(&self) -> &'static str {
        MANAGED_ASSET_LIFECYCLE_PRODUCTION_AUTHORITY_V2
    }
}

impl ValidateCanonicalV2 for ManagedAssetLifecycleRejectedV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum ManagedAssetLifecycleResultV2 {
    Accepted(Box<ManagedAssetLifecycleAcceptedV2>),
    Rejected(Box<ManagedAssetLifecycleRejectedV2>),
}
