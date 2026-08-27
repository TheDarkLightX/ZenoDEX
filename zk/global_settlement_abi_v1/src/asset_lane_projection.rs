use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::asset_transfer_types::{AssetTransferStateV1, ACCOUNT_CUSTODY_DOMAIN_V1};
use crate::canonical::{
    hash_global_v1, validate_token_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1,
    MAX_ASSET_BALANCE_ROWS_V1, MAX_ASSET_CUSTODY_ROWS_V1, MAX_ASSET_POLICY_ROWS_V1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::managed_asset_lifecycle_types::ManagedAssetLifecycleStateV1;
use crate::proof::LaneCompositionJournalV1;
use crate::state::{AssetSupplyV1, EconomicAmountV1};

pub const ASSET_LANE_STATE_PROJECTION_SCHEMA_V1: &str = "zenodex/asset-lane-state-projection/v1";
pub const ASSET_LANE_PRIVATE_PORT_SCHEMA_V1: &str = "zenodex/asset-lane-private-port/v1";
pub const ASSET_LANE_COORDINATOR_SCHEMA_V1: &str = "zenodex/asset-lane-coordinator/v1";

fn amount_key(row: &EconomicAmountV1) -> (&str, &str, &str) {
    (&row.asset, &row.owner, &row.custody_domain)
}

fn validate_amounts(
    rows: &[EconomicAmountV1],
    field: &'static str,
    accounts: bool,
) -> AbiResultV1<()> {
    let mut previous = None;
    for row in rows {
        validate_token_v1(&row.owner, field)?;
        validate_token_v1(&row.asset, field)?;
        validate_token_v1(&row.custody_domain, field)?;
        if row.amount_atoms == 0
            || (accounts && row.custody_domain != ACCOUNT_CUSTODY_DOMAIN_V1)
            || (!accounts && row.custody_domain == ACCOUNT_CUSTODY_DOMAIN_V1)
        {
            return Err(AbiErrorV1::InvalidBinding(field));
        }
        let key = amount_key(row);
        if previous.is_some_and(|prior| prior >= key) {
            return Err(AbiErrorV1::InvalidOrder(field));
        }
        previous = Some(key);
    }
    Ok(())
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneModuleCompatibilityV1 {
    pub module_release_id: RootV1,
    pub module_schema: String,
}

impl AssetLaneModuleCompatibilityV1 {
    fn validate(&self) -> AbiResultV1<()> {
        self.module_release_id
            .validate("asset lane compatible module release", false)?;
        validate_token_v1(&self.module_schema, "asset lane compatible module schema")
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneStateProjectionV1 {
    pub schema: String,
    pub asset_policy_registry_root: RootV1,
    pub fee_policy_registry_root: RootV1,
    pub balances: Vec<EconomicAmountV1>,
    pub custody: Vec<EconomicAmountV1>,
    pub supplies: Vec<AssetSupplyV1>,
}

impl AssetLaneStateProjectionV1 {
    pub(crate) fn validate_resource_bounds(&self) -> AbiResultV1<()> {
        if self.balances.len() > MAX_ASSET_BALANCE_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds("asset lane balance rows"));
        }
        if self.custody.len() > MAX_ASSET_CUSTODY_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "asset lane declared accounting-location rows",
            ));
        }
        if self.supplies.len() > MAX_ASSET_POLICY_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds("asset lane supply rows"));
        }
        Ok(())
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.validate_resource_bounds()?;
        if self.schema != ASSET_LANE_STATE_PROJECTION_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.asset_policy_registry_root
            .validate("asset lane asset policy registry root", false)?;
        self.fee_policy_registry_root
            .validate("asset lane fee policy registry root", false)?;
        validate_amounts(&self.balances, "asset lane balances", true)?;
        validate_amounts(&self.custody, "asset lane custody", false)?;

        let mut total_by_asset = BTreeMap::<&str, u128>::new();
        let mut previous_asset: Option<&str> = None;
        for supply in &self.supplies {
            validate_token_v1(&supply.asset, "asset lane supply asset")?;
            if previous_asset.is_some_and(|previous| previous >= supply.asset.as_str()) {
                return Err(AbiErrorV1::InvalidOrder("asset lane supplies"));
            }
            previous_asset = Some(&supply.asset);
            total_by_asset.insert(&supply.asset, 0);
        }
        for row in self.balances.iter().chain(&self.custody) {
            let total = total_by_asset
                .get(row.asset.as_str())
                .copied()
                .ok_or(AbiErrorV1::InvalidBinding(
                    "asset lane holding references unnamed supply",
                ))?
                .checked_add(row.amount_atoms)
                .ok_or(AbiErrorV1::Conservation(
                    "asset lane holding total overflow",
                ))?;
            total_by_asset.insert(&row.asset, total);
        }
        for supply in &self.supplies {
            if total_by_asset.remove(supply.asset.as_str()).unwrap_or(0) != supply.amount_atoms {
                return Err(AbiErrorV1::Conservation(
                    "asset lane owned and custodied total",
                ));
            }
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("asset-lane-state-projection-v1", self)
    }

    pub fn supply_atoms(&self, asset: &str) -> AbiResultV1<u128> {
        self.supplies
            .iter()
            .find(|row| row.asset == asset)
            .map(|row| row.amount_atoms)
            .ok_or(AbiErrorV1::InvalidBinding("asset lane unknown supply"))
    }

    pub fn owned_and_custodied_atoms(&self, asset: &str) -> AbiResultV1<u128> {
        self.balances
            .iter()
            .chain(&self.custody)
            .filter(|row| row.asset == asset)
            .try_fold(0_u128, |total, row| {
                total
                    .checked_add(row.amount_atoms)
                    .ok_or(AbiErrorV1::Conservation(
                        "asset lane owned and custodied overflow",
                    ))
            })
    }
}

pub fn project_asset_transfer_state_v1(
    state: &AssetTransferStateV1,
    asset_policy_registry_root: &RootV1,
    fee_policy_registry_root: &RootV1,
    custody: Vec<EconomicAmountV1>,
) -> AbiResultV1<AssetLaneStateProjectionV1> {
    state.validate()?;
    let projection = AssetLaneStateProjectionV1 {
        schema: ASSET_LANE_STATE_PROJECTION_SCHEMA_V1.to_owned(),
        asset_policy_registry_root: asset_policy_registry_root.clone(),
        fee_policy_registry_root: fee_policy_registry_root.clone(),
        balances: state.balances.clone(),
        custody,
        supplies: state.supplies.clone(),
    };
    projection.validate()?;
    Ok(projection)
}

pub fn project_managed_asset_lifecycle_state_v1(
    state: &ManagedAssetLifecycleStateV1,
    asset_policy_registry_root: &RootV1,
    fee_policy_registry_root: &RootV1,
    custody: Vec<EconomicAmountV1>,
) -> AbiResultV1<AssetLaneStateProjectionV1> {
    state.validate()?;
    let projection = AssetLaneStateProjectionV1 {
        schema: ASSET_LANE_STATE_PROJECTION_SCHEMA_V1.to_owned(),
        asset_policy_registry_root: asset_policy_registry_root.clone(),
        fee_policy_registry_root: fee_policy_registry_root.clone(),
        balances: state.balances.clone(),
        custody,
        supplies: state.supplies.clone(),
    };
    projection.validate()?;
    Ok(projection)
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLanePrivatePortV1 {
    pub schema: String,
    pub producer_module_schema: String,
    pub module_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub pre_state: AssetLaneStateProjectionV1,
    pub post_state: AssetLaneStateProjectionV1,
    pub module_effect_plan_root: RootV1,
    pub terminal_obligations_root: RootV1,
}

impl AssetLanePrivatePortV1 {
    pub(crate) fn validate_resource_bounds(&self) -> AbiResultV1<()> {
        self.pre_state.validate_resource_bounds()?;
        self.post_state.validate_resource_bounds()
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        self.validate_resource_bounds()?;
        if self.schema != ASSET_LANE_PRIVATE_PORT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        validate_token_v1(&self.producer_module_schema, "asset lane producer schema")?;
        self.module_release_id
            .validate("asset lane port module release", false)?;
        self.command_occurrence_id
            .validate("asset lane port occurrence", false)?;
        self.pre_state.validate()?;
        self.post_state.validate()?;
        self.module_effect_plan_root
            .validate("asset lane port effect plan", false)?;
        self.terminal_obligations_root
            .validate("asset lane port terminal obligations", true)
    }

    pub fn port_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("asset-lane-private-port-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneCoordinatorContextV1 {
    pub schema: String,
    pub chain_id: String,
    pub deployment_root: RootV1,
    pub profile_root: RootV1,
    pub writer_epoch: u64,
    pub coordinator_release_id: RootV1,
    pub command_occurrence_id: RootV1,
    pub asset_policy_registry_root: RootV1,
    pub fee_policy_registry_root: RootV1,
    pub compatible_modules: Vec<AssetLaneModuleCompatibilityV1>,
}

impl AssetLaneCoordinatorContextV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != ASSET_LANE_COORDINATOR_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        validate_token_v1(&self.chain_id, "asset lane coordinator chain")?;
        for root in [
            &self.deployment_root,
            &self.profile_root,
            &self.coordinator_release_id,
            &self.command_occurrence_id,
            &self.asset_policy_registry_root,
            &self.fee_policy_registry_root,
        ] {
            root.validate("asset lane coordinator required root", false)?;
        }
        if self.compatible_modules.is_empty() {
            return Err(AbiErrorV1::InvalidBounds("asset lane compatible modules"));
        }
        for module in &self.compatible_modules {
            module.validate()?;
        }
        if self
            .compatible_modules
            .windows(2)
            .any(|pair| pair[0].module_release_id >= pair[1].module_release_id)
        {
            return Err(AbiErrorV1::InvalidOrder("asset lane compatible modules"));
        }
        Ok(())
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetLaneCoordinatorRejectCodeV1 {
    CHAIN_MISMATCH,
    DEPLOYMENT_MISMATCH,
    PROFILE_MISMATCH,
    WRITER_EPOCH_MISMATCH,
    WRONG_LANE,
    MODULE_NOT_REGISTERED,
    MODULE_SCHEMA_MISMATCH,
    MODULE_RELEASE_MISMATCH,
    OCCURRENCE_MISMATCH,
    PRIVATE_PORT_UNBOUND,
    PRIVATE_PORT_ROOT_MISMATCH,
    EFFECT_PLAN_MISMATCH,
    TERMINAL_OBLIGATION_MISMATCH,
    POLICY_ROOT_MISMATCH,
    OCCURRENCE_EFFECT_MISMATCH,
    LANE_WRITE_SHAPE_MISMATCH,
    EFFECT_KIND_FORBIDDEN,
    CONSERVATION_COVERAGE_MISMATCH,
    CONSERVATION_STATE_MISMATCH,
    STATE_EFFECT_MISMATCH,
    EXTERNAL_OUTBOX_FORBIDDEN,
}

impl AssetLaneCoordinatorRejectCodeV1 {
    pub const fn binding_label(self) -> &'static str {
        match self {
            Self::CHAIN_MISMATCH => "asset lane coordinator CHAIN_MISMATCH",
            Self::DEPLOYMENT_MISMATCH => "asset lane coordinator DEPLOYMENT_MISMATCH",
            Self::PROFILE_MISMATCH => "asset lane coordinator PROFILE_MISMATCH",
            Self::WRITER_EPOCH_MISMATCH => "asset lane coordinator WRITER_EPOCH_MISMATCH",
            Self::WRONG_LANE => "asset lane coordinator WRONG_LANE",
            Self::MODULE_NOT_REGISTERED => "asset lane coordinator MODULE_NOT_REGISTERED",
            Self::MODULE_SCHEMA_MISMATCH => "asset lane coordinator MODULE_SCHEMA_MISMATCH",
            Self::MODULE_RELEASE_MISMATCH => "asset lane coordinator MODULE_RELEASE_MISMATCH",
            Self::OCCURRENCE_MISMATCH => "asset lane coordinator OCCURRENCE_MISMATCH",
            Self::PRIVATE_PORT_UNBOUND => "asset lane coordinator PRIVATE_PORT_UNBOUND",
            Self::PRIVATE_PORT_ROOT_MISMATCH => "asset lane coordinator PRIVATE_PORT_ROOT_MISMATCH",
            Self::EFFECT_PLAN_MISMATCH => "asset lane coordinator EFFECT_PLAN_MISMATCH",
            Self::TERMINAL_OBLIGATION_MISMATCH => {
                "asset lane coordinator TERMINAL_OBLIGATION_MISMATCH"
            }
            Self::POLICY_ROOT_MISMATCH => "asset lane coordinator POLICY_ROOT_MISMATCH",
            Self::OCCURRENCE_EFFECT_MISMATCH => "asset lane coordinator OCCURRENCE_EFFECT_MISMATCH",
            Self::LANE_WRITE_SHAPE_MISMATCH => "asset lane coordinator LANE_WRITE_SHAPE_MISMATCH",
            Self::EFFECT_KIND_FORBIDDEN => "asset lane coordinator EFFECT_KIND_FORBIDDEN",
            Self::CONSERVATION_COVERAGE_MISMATCH => {
                "asset lane coordinator CONSERVATION_COVERAGE_MISMATCH"
            }
            Self::CONSERVATION_STATE_MISMATCH => {
                "asset lane coordinator CONSERVATION_STATE_MISMATCH"
            }
            Self::STATE_EFFECT_MISMATCH => "asset lane coordinator STATE_EFFECT_MISMATCH",
            Self::EXTERNAL_OUTBOX_FORBIDDEN => "asset lane coordinator EXTERNAL_OUTBOX_FORBIDDEN",
        }
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneCompositionAcceptedV1 {
    pub post_state: AssetLaneStateProjectionV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub lane_journal: LaneCompositionJournalV1,
}

impl AssetLaneCompositionAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.post_state.validate()?;
        self.effects.validate()?;
        self.lane_journal.validate()?;
        if self.effects.is_empty()
            || self.lane_journal.post_lane_root != self.post_state.state_root()?
            || self.lane_journal.effect_plan_root != self.effects.effect_plan_root()?
        {
            return Err(AbiErrorV1::InvalidBinding("asset lane acceptance"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AssetLaneCompositionRejectedV1 {
    pub code: AssetLaneCoordinatorRejectCodeV1,
    pub pre_lane_root: RootV1,
    pub post_lane_root: RootV1,
    pub effects: GlobalEconomicEffectPlanV1,
}

impl AssetLaneCompositionRejectedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.pre_lane_root
            .validate("asset lane rejected pre root", false)?;
        self.post_lane_root
            .validate("asset lane rejected post root", false)?;
        self.effects.validate()?;
        if self.pre_lane_root != self.post_lane_root || !self.effects.is_empty() {
            return Err(AbiErrorV1::InvalidBinding("asset lane rejection no-op"));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
pub enum AssetLaneCompositionResultV1 {
    Accepted(Box<AssetLaneCompositionAcceptedV1>),
    Rejected(Box<AssetLaneCompositionRejectedV1>),
}

pub(crate) fn empty_asset_lane_effects_v1() -> GlobalEconomicEffectPlanV1 {
    GlobalEconomicEffectPlanV1 {
        schema: GLOBAL_SETTLEMENT_ABI_V1.to_owned(),
        rows: Vec::new(),
        asset_conservation: Vec::new(),
        fee_conservation: Vec::new(),
        lane_writes: Vec::new(),
        occurrence_consumptions: Vec::new(),
        external_outbox_enqueue: Vec::new(),
    }
}
