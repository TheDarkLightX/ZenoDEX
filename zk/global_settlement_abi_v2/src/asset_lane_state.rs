//! Aggregate ASSET_TRANSFER lane state for the V2 SHADOW coordinator mirror.
//!
//! Public Rust construction is untrusted. Validation establishes closed table
//! coverage, exact account-to-supply equality, resource ceilings, and canonical
//! ordering. Registry membership authentication remains a SHADOW premise.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Deserializer, Serialize};

use crate::asset_origin_registry::{
    validate_asset_transfer_policy_origin_v2, validate_managed_asset_policy_origin_v2,
};
use crate::asset_origin_registry_types::{
    AssetOriginRegistryStateV2, MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2,
};
use crate::asset_transfer_types::{
    AssetTransferContextV2, AssetTransferPolicyV2, AssetTransferStateV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_LANE_PRODUCTION_AUTHORITY_V2, ASSET_TRANSFER_MODULE_SCHEMA_V2,
};
use crate::canonical::{
    canonical_bytes_v2, hash_global_v2, validate_schema_v2, validate_token_v2, AbiErrorV2,
    AbiResultV2, RootV2, ValidateCanonicalV2,
};
use crate::managed_asset_lifecycle_types::{
    ManagedAssetLifecycleContextV2, ManagedAssetLifecyclePolicyV2, ManagedAssetLifecycleStateV2,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2,
};
use crate::proof::EconomicCommandOccurrenceV2;
use crate::state::{AssetSupplyV2, EconomicAmountV2};

pub const ASSET_LANE_STATE_SCHEMA_V2: &str = "zenodex/asset-lane-state/v2";
pub const ASSET_LANE_PROFILE_AUTHENTICATION_V2: &str = "SHADOW";
pub const MAX_ASSET_LANE_ASSETS_V2: usize = MAX_ASSET_ORIGIN_REGISTRY_ASSETS_V2;
pub const MAX_ASSET_LANE_BALANCE_ROWS_V2: usize = 4_096;
pub const MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2: usize = 1_048_576;

fn deserialize_required_option<'de, D, T>(deserializer: D) -> Result<Option<T>, D::Error>
where
    D: Deserializer<'de>,
    T: Deserialize<'de>,
{
    Option::<T>::deserialize(deserializer)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneStateV2 {
    pub schema: String,
    pub module_release_id: RootV2,
    pub origin_registry: AssetOriginRegistryStateV2,
    pub transfer_policies: Vec<AssetTransferPolicyV2>,
    pub managed_policies: Vec<ManagedAssetLifecyclePolicyV2>,
    pub balances: Vec<EconomicAmountV2>,
    pub supplies: Vec<AssetSupplyV2>,
}

impl AssetLaneStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        validate_schema_v2(&self.schema, ASSET_LANE_STATE_SCHEMA_V2, "asset lane state")?;
        self.module_release_id
            .validate("asset lane module release", false)?;
        self.validate_resource_bounds()?;
        self.origin_registry.validate()?;
        if self.origin_registry.module_release_id != self.module_release_id {
            return Err(AbiErrorV2::InvalidBinding("asset lane registry release"));
        }
        self.validate_tables()?;
        self.validate_asset_coverage()?;
        self.validate_owned_supply()?;
        if canonical_bytes_v2(self)?.len() > MAX_ASSET_LANE_STATE_CANONICAL_BYTES_V2 {
            return Err(AbiErrorV2::InvalidBounds(
                "asset lane state canonical encoding bytes",
            ));
        }
        Ok(())
    }

    fn validate_resource_bounds(&self) -> AbiResultV2<()> {
        let counts = [
            (
                "asset lane origin registry assets",
                self.origin_registry.assets.len(),
                MAX_ASSET_LANE_ASSETS_V2,
            ),
            (
                "asset lane transfer policies",
                self.transfer_policies.len(),
                MAX_ASSET_LANE_ASSETS_V2,
            ),
            (
                "asset lane managed policies",
                self.managed_policies.len(),
                MAX_ASSET_LANE_ASSETS_V2,
            ),
            (
                "asset lane balances",
                self.balances.len(),
                MAX_ASSET_LANE_BALANCE_ROWS_V2,
            ),
            (
                "asset lane supplies",
                self.supplies.len(),
                MAX_ASSET_LANE_ASSETS_V2,
            ),
        ];
        for (field, count, limit) in counts {
            if count > limit {
                return Err(AbiErrorV2::InvalidBounds(field));
            }
        }
        Ok(())
    }

    fn validate_tables(&self) -> AbiResultV2<()> {
        for policy in &self.transfer_policies {
            policy.validate()?;
        }
        if self
            .transfer_policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("asset lane transfer policies"));
        }
        for policy in &self.managed_policies {
            policy.validate()?;
        }
        if self
            .managed_policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("asset lane managed policies"));
        }
        for balance in &self.balances {
            balance.validate()?;
        }
        if self
            .balances
            .windows(2)
            .any(|pair| pair[0].key() >= pair[1].key())
        {
            return Err(AbiErrorV2::InvalidOrder("asset lane balances"));
        }
        for supply in &self.supplies {
            supply.validate()?;
        }
        if self
            .supplies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder("asset lane supplies"));
        }
        Ok(())
    }

    fn validate_asset_coverage(&self) -> AbiResultV2<()> {
        let transfer_assets = self
            .transfer_policies
            .iter()
            .map(|policy| policy.asset.as_str())
            .collect::<Vec<_>>();
        let registry_assets = self
            .origin_registry
            .assets
            .iter()
            .map(|row| row.asset.as_str())
            .collect::<Vec<_>>();
        let supply_assets = self
            .supplies
            .iter()
            .map(|row| row.asset.as_str())
            .collect::<Vec<_>>();
        if transfer_assets != registry_assets || transfer_assets != supply_assets {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane registry transfer supply coverage",
            ));
        }
        let managed_assets = self
            .managed_policies
            .iter()
            .map(|policy| policy.asset.as_str())
            .collect::<Vec<_>>();
        let registered_managed_assets = self
            .origin_registry
            .assets
            .iter()
            .filter(|row| !row.issue_policy_root.is_zero())
            .map(|row| row.asset.as_str())
            .collect::<Vec<_>>();
        if managed_assets != registered_managed_assets {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane managed registry coverage",
            ));
        }
        for managed in &self.managed_policies {
            let transfer = self
                .transfer_policies
                .iter()
                .find(|policy| policy.asset == managed.asset)
                .ok_or(AbiErrorV2::InvalidBinding(
                    "asset lane managed transfer identity",
                ))?;
            if managed.asset_class != transfer.asset_class
                || managed.asset_origin_root != transfer.asset_origin_root
                || managed.atom_decimals != transfer.atom_decimals
            {
                return Err(AbiErrorV2::InvalidBinding(
                    "asset lane transfer managed identity",
                ));
            }
        }
        Ok(())
    }

    fn validate_owned_supply(&self) -> AbiResultV2<()> {
        let asset_set = self
            .transfer_policies
            .iter()
            .map(|policy| policy.asset.as_str())
            .collect::<BTreeSet<_>>();
        let mut totals = BTreeMap::<&str, u128>::new();
        for balance in &self.balances {
            if balance.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V2
                || balance.amount_atoms == 0
                || !asset_set.contains(balance.asset.as_str())
            {
                return Err(AbiErrorV2::InvalidBinding("asset lane balance"));
            }
            let total = totals
                .get(balance.asset.as_str())
                .copied()
                .unwrap_or(0)
                .checked_add(balance.amount_atoms)
                .ok_or(AbiErrorV2::Conservation(
                    "asset lane account total overflow",
                ))?;
            totals.insert(balance.asset.as_str(), total);
        }
        for supply in &self.supplies {
            if totals.remove(supply.asset.as_str()).unwrap_or(0) != supply.amount_atoms {
                return Err(AbiErrorV2::Conservation(
                    "asset lane owned account total differs from supply",
                ));
            }
        }
        Ok(())
    }

    pub fn policy_origin_bindings_hold(&self) -> bool {
        self.transfer_policies.iter().all(|policy| {
            validate_asset_transfer_policy_origin_v2(&self.origin_registry, policy).is_ok()
        }) && self.managed_policies.iter().all(|policy| {
            validate_managed_asset_policy_origin_v2(&self.origin_registry, policy).is_ok()
        })
    }

    pub fn state_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("asset-lane-state-v2", self)
    }

    pub fn balance_atoms(&self, owner: &str, asset: &str) -> AbiResultV2<u128> {
        validate_token_v2(owner, "asset lane balance owner")?;
        validate_token_v2(asset, "asset lane balance asset")?;
        Ok(self
            .balances
            .iter()
            .find(|row| row.owner == owner && row.asset == asset)
            .map(|row| row.amount_atoms)
            .unwrap_or(0))
    }

    pub fn supply_atoms(&self, asset: &str) -> AbiResultV2<u128> {
        validate_token_v2(asset, "asset lane supply asset")?;
        self.supplies
            .iter()
            .find(|row| row.asset == asset)
            .map(|row| row.amount_atoms)
            .ok_or(AbiErrorV2::InvalidBinding("asset lane unknown supply"))
    }

    pub fn transfer_leaf_state(&self) -> AssetTransferStateV2 {
        AssetTransferStateV2 {
            schema: ASSET_TRANSFER_MODULE_SCHEMA_V2.to_owned(),
            module_release_id: self.module_release_id.clone(),
            policies: self.transfer_policies.clone(),
            balances: self.balances.clone(),
            supplies: self.supplies.clone(),
        }
    }

    pub fn managed_leaf_state(&self) -> ManagedAssetLifecycleStateV2 {
        let managed_assets = self
            .managed_policies
            .iter()
            .map(|policy| policy.asset.as_str())
            .collect::<BTreeSet<_>>();
        ManagedAssetLifecycleStateV2 {
            schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2.to_owned(),
            module_release_id: self.module_release_id.clone(),
            policies: self.managed_policies.clone(),
            balances: self
                .balances
                .iter()
                .filter(|row| managed_assets.contains(row.asset.as_str()))
                .cloned()
                .collect(),
            supplies: self
                .supplies
                .iter()
                .filter(|row| managed_assets.contains(row.asset.as_str()))
                .cloned()
                .collect(),
        }
    }

    pub const fn production_authority(&self) -> &'static str {
        ASSET_LANE_PRODUCTION_AUTHORITY_V2
    }

    pub const fn profile_authentication(&self) -> &'static str {
        ASSET_LANE_PROFILE_AUTHENTICATION_V2
    }
}

impl ValidateCanonicalV2 for AssetLaneStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneContextV2 {
    pub writer_epoch: u64,
    pub module_release_id: RootV2,
    pub global_pre_state_root: RootV2,
    #[serde(deserialize_with = "deserialize_required_option")]
    pub occurrence: Option<EconomicCommandOccurrenceV2>,
}

impl AssetLaneContextV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.module_release_id
            .validate("asset lane context release", false)?;
        self.global_pre_state_root
            .validate("asset lane global pre-state", false)?;
        if let Some(occurrence) = &self.occurrence {
            occurrence.validate()?;
        }
        Ok(())
    }

    pub fn transfer_context(&self) -> AssetTransferContextV2 {
        AssetTransferContextV2 {
            writer_epoch: self.writer_epoch,
            module_release_id: self.module_release_id.clone(),
            global_pre_state_root: self.global_pre_state_root.clone(),
            occurrence: self.occurrence.clone(),
        }
    }

    pub fn managed_context(&self) -> ManagedAssetLifecycleContextV2 {
        ManagedAssetLifecycleContextV2 {
            writer_epoch: self.writer_epoch,
            module_release_id: self.module_release_id.clone(),
            global_pre_state_root: self.global_pre_state_root.clone(),
            occurrence: self.occurrence.clone(),
        }
    }
}

impl ValidateCanonicalV2 for AssetLaneContextV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}
