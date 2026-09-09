//! Custody-complete ASSET_TRANSFER lane state for the V2 successor core.
//!
//! The transfer leaf owns account balances and the supply registry. This state
//! adds non-account physical custody without duplicating any leaf-owned field.
//! Validation proves exact registry coverage and physical holdings equal to
//! supply. The value remains advisory and grants no verifier or publication
//! authority.

use std::collections::{BTreeMap, BTreeSet};

use serde::{Deserialize, Serialize};

use crate::asset_lane_state::ASSET_LANE_PROFILE_AUTHENTICATION_V2;
use crate::asset_origin_registry::{
    validate_asset_transfer_policy_origin_v2, validate_managed_asset_policy_origin_v2,
};
use crate::asset_origin_registry_types::AssetOriginRegistryStateV2;
use crate::asset_transfer_types::{
    AssetTransferPolicyV2, AssetTransferStateV2, ACCOUNT_CUSTODY_DOMAIN_V2,
    ASSET_LANE_PRODUCTION_AUTHORITY_V2,
};
use crate::canonical::{
    canonical_bytes_v2, hash_global_v2, validate_schema_v2, AbiErrorV2, AbiResultV2, RootV2,
    ValidateCanonicalV2,
};
use crate::managed_asset_lifecycle_types::{
    ManagedAssetLifecyclePolicyV2, ManagedAssetLifecycleStateV2,
    MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2,
};
use crate::resource_limits::{
    validate_asset_state_asset_count_v2, validate_asset_state_balance_row_count_v2,
    validate_rootable_asset_state_canonical_bytes_v2, MAX_BALANCE_ROWS_PER_ASSET_STATE_V2,
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2,
};
use crate::state::{AssetSupplyV2, EconomicAmountV2};

pub const ASSET_LANE_CUSTODY_STATE_SCHEMA_V2: &str = "zenodex/asset-lane-custody-state/v2";
pub const MAX_ASSET_LANE_CUSTODY_ROWS_V2: usize = MAX_BALANCE_ROWS_PER_ASSET_STATE_V2;
pub const MAX_ASSET_LANE_CUSTODY_STATE_CANONICAL_BYTES_V2: usize =
    MAX_ROOTABLE_ASSET_STATE_CANONICAL_BYTES_V2;

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneCustodyStateV2 {
    pub schema: String,
    pub transfer_state: AssetTransferStateV2,
    pub origin_registry: AssetOriginRegistryStateV2,
    pub managed_policies: Vec<ManagedAssetLifecyclePolicyV2>,
    pub custody: Vec<EconomicAmountV2>,
}

impl AssetLaneCustodyStateV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        self.validate_resource_bounds()?;
        validate_schema_v2(
            &self.schema,
            ASSET_LANE_CUSTODY_STATE_SCHEMA_V2,
            "asset lane custody state",
        )?;
        self.transfer_state.validate()?;
        self.origin_registry.validate()?;
        if self.origin_registry.module_release_id != self.transfer_state.module_release_id {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody registry release",
            ));
        }
        self.validate_managed_policies()?;
        self.validate_asset_coverage()?;
        self.validate_custody_rows()?;
        self.validate_physical_conservation()?;
        validate_rootable_asset_state_canonical_bytes_v2(
            canonical_bytes_v2(self)?.len(),
            "asset lane custody state canonical encoding bytes",
        )
    }

    fn validate_resource_bounds(&self) -> AbiResultV2<()> {
        validate_asset_state_asset_count_v2(
            self.managed_policies.len(),
            "asset lane custody managed policies",
        )?;
        validate_asset_state_balance_row_count_v2(self.custody.len(), "asset lane custody rows")
    }

    fn validate_managed_policies(&self) -> AbiResultV2<()> {
        for policy in &self.managed_policies {
            policy.validate()?;
        }
        if self
            .managed_policies
            .windows(2)
            .any(|pair| pair[0].asset >= pair[1].asset)
        {
            return Err(AbiErrorV2::InvalidOrder(
                "asset lane custody managed policies",
            ));
        }
        Ok(())
    }

    fn validate_asset_coverage(&self) -> AbiResultV2<()> {
        let registry_assets = self
            .origin_registry
            .assets
            .iter()
            .map(|record| record.asset.as_str())
            .collect::<Vec<_>>();
        let transfer_assets = self
            .transfer_state
            .policies
            .iter()
            .map(|policy| policy.asset.as_str())
            .collect::<Vec<_>>();
        let supply_assets = self
            .transfer_state
            .supplies
            .iter()
            .map(|supply| supply.asset.as_str())
            .collect::<Vec<_>>();
        if registry_assets != transfer_assets || registry_assets != supply_assets {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody registry transfer supply coverage",
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
            .filter(|record| !record.issue_policy_root.is_zero())
            .map(|record| record.asset.as_str())
            .collect::<Vec<_>>();
        if managed_assets != registered_managed_assets {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody managed registry coverage",
            ));
        }
        self.validate_managed_identity()
    }

    fn validate_managed_identity(&self) -> AbiResultV2<()> {
        for managed in &self.managed_policies {
            let transfer = self.transfer_policy(&managed.asset)?;
            if managed.asset_class != transfer.asset_class
                || managed.asset_origin_root != transfer.asset_origin_root
                || managed.atom_decimals != transfer.atom_decimals
            {
                return Err(AbiErrorV2::InvalidBinding(
                    "asset lane custody managed identity",
                ));
            }
        }
        Ok(())
    }

    fn validate_custody_rows(&self) -> AbiResultV2<()> {
        let registered_assets = self
            .origin_registry
            .assets
            .iter()
            .map(|record| record.asset.as_str())
            .collect::<BTreeSet<_>>();
        for row in &self.custody {
            row.validate_canonical_v2()?;
            if row.amount_atoms == 0
                || row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V2
                || !registered_assets.contains(row.asset.as_str())
            {
                return Err(AbiErrorV2::InvalidBinding("asset lane custody row"));
            }
        }
        if self
            .custody
            .windows(2)
            .any(|pair| pair[0].key() >= pair[1].key())
        {
            return Err(AbiErrorV2::InvalidOrder("asset lane custody rows"));
        }
        Ok(())
    }

    fn validate_physical_conservation(&self) -> AbiResultV2<()> {
        let mut physical = BTreeMap::<&str, u128>::new();
        for row in self.transfer_state.balances.iter().chain(&self.custody) {
            let total = physical
                .get(row.asset.as_str())
                .copied()
                .unwrap_or(0)
                .checked_add(row.amount_atoms)
                .ok_or(AbiErrorV2::Conservation(
                    "asset lane physical total overflow",
                ))?;
            physical.insert(row.asset.as_str(), total);
        }
        for supply in &self.transfer_state.supplies {
            if physical.remove(supply.asset.as_str()).unwrap_or(0) != supply.amount_atoms {
                return Err(AbiErrorV2::Conservation(
                    "asset lane physical total differs from supply",
                ));
            }
        }
        if !physical.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane custody unknown physical asset",
            ));
        }
        Ok(())
    }

    fn transfer_policy(&self, asset: &str) -> AbiResultV2<&AssetTransferPolicyV2> {
        self.transfer_state
            .policies
            .iter()
            .find(|policy| policy.asset == asset)
            .ok_or(AbiErrorV2::InvalidBinding(
                "asset lane custody managed transfer identity",
            ))
    }

    pub fn policy_origin_bindings_hold(&self) -> bool {
        self.transfer_state.policies.iter().all(|policy| {
            validate_asset_transfer_policy_origin_v2(&self.origin_registry, policy).is_ok()
        }) && self.managed_policies.iter().all(|policy| {
            validate_managed_asset_policy_origin_v2(&self.origin_registry, policy).is_ok()
        })
    }

    pub fn state_root(&self) -> AbiResultV2<RootV2> {
        self.validate()?;
        hash_global_v2("asset-lane-custody-state-v2", self)
    }

    pub fn module_release_id(&self) -> &RootV2 {
        &self.transfer_state.module_release_id
    }

    pub fn transfer_policies(&self) -> &[AssetTransferPolicyV2] {
        &self.transfer_state.policies
    }

    pub fn balances(&self) -> &[EconomicAmountV2] {
        &self.transfer_state.balances
    }

    pub fn supplies(&self) -> &[AssetSupplyV2] {
        &self.transfer_state.supplies
    }

    pub fn supply_atoms(&self, asset: &str) -> AbiResultV2<u128> {
        self.transfer_state.supply_atoms(asset)
    }

    pub fn transfer_leaf_state(&self) -> AssetTransferStateV2 {
        self.transfer_state.clone()
    }

    pub fn managed_leaf_state(&self) -> ManagedAssetLifecycleStateV2 {
        let managed_assets = self
            .managed_policies
            .iter()
            .map(|policy| policy.asset.as_str())
            .collect::<BTreeSet<_>>();
        ManagedAssetLifecycleStateV2 {
            schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V2.to_owned(),
            module_release_id: self.transfer_state.module_release_id.clone(),
            policies: self.managed_policies.clone(),
            balances: self
                .transfer_state
                .balances
                .iter()
                .filter(|row| managed_assets.contains(row.asset.as_str()))
                .cloned()
                .collect(),
            supplies: self
                .transfer_state
                .supplies
                .iter()
                .filter(|row| managed_assets.contains(row.asset.as_str()))
                .cloned()
                .collect(),
        }
    }

    pub(crate) fn account_total_atoms(&self, asset: &str) -> AbiResultV2<u128> {
        checked_total_atoms(
            self.transfer_state
                .balances
                .iter()
                .filter(|row| row.asset == asset),
            "asset lane account total overflow",
        )
    }

    pub(crate) fn custody_total_atoms(&self, asset: &str) -> AbiResultV2<u128> {
        checked_total_atoms(
            self.custody.iter().filter(|row| row.asset == asset),
            "asset lane custody total overflow",
        )
    }

    pub(crate) fn physical_total_atoms(&self, asset: &str) -> AbiResultV2<u128> {
        self.account_total_atoms(asset)?
            .checked_add(self.custody_total_atoms(asset)?)
            .ok_or(AbiErrorV2::Conservation(
                "asset lane physical total overflow",
            ))
    }

    pub const fn production_authority(&self) -> &'static str {
        ASSET_LANE_PRODUCTION_AUTHORITY_V2
    }

    pub const fn profile_authentication(&self) -> &'static str {
        ASSET_LANE_PROFILE_AUTHENTICATION_V2
    }
}

fn checked_total_atoms<'a>(
    mut rows: impl Iterator<Item = &'a EconomicAmountV2>,
    overflow: &'static str,
) -> AbiResultV2<u128> {
    rows.try_fold(0_u128, |total, row| {
        total
            .checked_add(row.amount_atoms)
            .ok_or(AbiErrorV2::Conservation(overflow))
    })
}

impl ValidateCanonicalV2 for AssetLaneCustodyStateV2 {
    fn validate_canonical_v2(&self) -> AbiResultV2<()> {
        self.validate()
    }
}
