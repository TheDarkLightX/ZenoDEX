//! Closed coordinator outcomes for the V2 aggregate asset lane.
//!
//! Accepted values can only be constructed inside this crate after all
//! aggregate bindings have been checked. They carry SHADOW evidence and grant
//! no runtime, settlement, release, RISC0, or production authority.

use serde::{Deserialize, Serialize};

use crate::asset_lane_state::{AssetLaneStateV2, ASSET_LANE_PROFILE_AUTHENTICATION_V2};
use crate::asset_transfer_types::{
    AssetTransferCommandV2, AssetTransferRejectCodeV2, ASSET_LANE_PRODUCTION_AUTHORITY_V2,
};
use crate::canonical::{AbiErrorV2, AbiResultV2, RootV2};
use crate::effects::{GlobalEconomicEffectPlanV2, LaneIdV2, LaneWriteV2};
use crate::managed_asset_lifecycle_types::{
    ManagedAssetLifecycleCommandV2, ManagedAssetLifecycleRejectCodeV2,
};
use crate::proof::LaneModuleTransitionJournalV2;

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetLaneRouteV2 {
    TRANSFER,
    MANAGED_LIFECYCLE,
    COORDINATOR,
}

impl AssetLaneRouteV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::TRANSFER => "TRANSFER",
            Self::MANAGED_LIFECYCLE => "MANAGED_LIFECYCLE",
            Self::COORDINATOR => "COORDINATOR",
        }
    }
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum AssetLaneCoordinatorRejectCodeV2 {
    REGISTRY_BINDING_MISMATCH,
    CANDIDATE_BINDING_MISMATCH,
    PROJECTION_MISMATCH,
}

impl AssetLaneCoordinatorRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::REGISTRY_BINDING_MISMATCH => "REGISTRY_BINDING_MISMATCH",
            Self::CANDIDATE_BINDING_MISMATCH => "CANDIDATE_BINDING_MISMATCH",
            Self::PROJECTION_MISMATCH => "PROJECTION_MISMATCH",
        }
    }
}

pub const ALL_ASSET_LANE_COORDINATOR_REJECT_CODES_V2: [AssetLaneCoordinatorRejectCodeV2; 3] = [
    AssetLaneCoordinatorRejectCodeV2::REGISTRY_BINDING_MISMATCH,
    AssetLaneCoordinatorRejectCodeV2::CANDIDATE_BINDING_MISMATCH,
    AssetLaneCoordinatorRejectCodeV2::PROJECTION_MISMATCH,
];

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AssetLaneCommandV2 {
    Transfer(AssetTransferCommandV2),
    ManagedLifecycle(ManagedAssetLifecycleCommandV2),
}

impl AssetLaneCommandV2 {
    pub fn validate(&self) -> AbiResultV2<()> {
        match self {
            Self::Transfer(command) => command.validate(),
            Self::ManagedLifecycle(command) => command.validate(),
        }
    }

    pub const fn route(&self) -> AssetLaneRouteV2 {
        match self {
            Self::Transfer(_) => AssetLaneRouteV2::TRANSFER,
            Self::ManagedLifecycle(_) => AssetLaneRouteV2::MANAGED_LIFECYCLE,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum AssetLaneRejectCodeV2 {
    Coordinator(AssetLaneCoordinatorRejectCodeV2),
    Transfer(AssetTransferRejectCodeV2),
    ManagedLifecycle(ManagedAssetLifecycleRejectCodeV2),
}

impl AssetLaneRejectCodeV2 {
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Coordinator(code) => code.as_str(),
            Self::Transfer(code) => asset_transfer_reject_code_str(code),
            Self::ManagedLifecycle(code) => code.as_str(),
        }
    }
}

const fn asset_transfer_reject_code_str(code: AssetTransferRejectCodeV2) -> &'static str {
    match code {
        AssetTransferRejectCodeV2::MISSING_OCCURRENCE => "MISSING_OCCURRENCE",
        AssetTransferRejectCodeV2::OCCURRENCE_BINDING_MISMATCH => "OCCURRENCE_BINDING_MISMATCH",
        AssetTransferRejectCodeV2::RELEASE_MISMATCH => "RELEASE_MISMATCH",
        AssetTransferRejectCodeV2::UNKNOWN_COMMAND => "UNKNOWN_COMMAND",
        AssetTransferRejectCodeV2::OCCURRENCE_COMMAND_MISMATCH => "OCCURRENCE_COMMAND_MISMATCH",
        AssetTransferRejectCodeV2::UNKNOWN_ASSET => "UNKNOWN_ASSET",
        AssetTransferRejectCodeV2::DISABLED_ASSET => "DISABLED_ASSET",
        AssetTransferRejectCodeV2::UNREGISTERED_ASSET => "UNREGISTERED_ASSET",
        AssetTransferRejectCodeV2::ASSET_ORIGIN_MISMATCH => "ASSET_ORIGIN_MISMATCH",
        AssetTransferRejectCodeV2::NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED => {
            "NATIVE_ASSET_ACCOUNTING_UNIMPLEMENTED"
        }
        AssetTransferRejectCodeV2::UNAUTHORIZED_SUBJECT => "UNAUTHORIZED_SUBJECT",
        AssetTransferRejectCodeV2::SELF_TRANSFER => "SELF_TRANSFER",
        AssetTransferRejectCodeV2::ZERO_AMOUNT => "ZERO_AMOUNT",
        AssetTransferRejectCodeV2::FEE_LIMIT_EXCEEDED => "FEE_LIMIT_EXCEEDED",
        AssetTransferRejectCodeV2::EFFECT_DELTA_OVERFLOW => "EFFECT_DELTA_OVERFLOW",
        AssetTransferRejectCodeV2::INSUFFICIENT_BALANCE => "INSUFFICIENT_BALANCE",
        AssetTransferRejectCodeV2::BALANCE_OVERFLOW => "BALANCE_OVERFLOW",
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssetLaneAcceptedV2 {
    route: AssetLaneRouteV2,
    source_leaf_journal_root: RootV2,
    post_state: AssetLaneStateV2,
    effects: GlobalEconomicEffectPlanV2,
    module_journal: LaneModuleTransitionJournalV2,
}

impl AssetLaneAcceptedV2 {
    pub(crate) fn new(
        route: AssetLaneRouteV2,
        source_leaf_journal_root: RootV2,
        post_state: AssetLaneStateV2,
        effects: GlobalEconomicEffectPlanV2,
        module_journal: LaneModuleTransitionJournalV2,
    ) -> AbiResultV2<Self> {
        let accepted = Self {
            route,
            source_leaf_journal_root,
            post_state,
            effects,
            module_journal,
        };
        accepted.validate()?;
        Ok(accepted)
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        if self.route == AssetLaneRouteV2::COORDINATOR {
            return Err(AbiErrorV2::InvalidBinding("asset lane accepted route"));
        }
        self.source_leaf_journal_root
            .validate("asset lane source leaf journal", false)?;
        self.post_state.validate()?;
        self.effects.validate()?;
        self.module_journal.validate()?;
        let expected_write = LaneWriteV2 {
            lane_id: LaneIdV2::ASSET_TRANSFER,
            pre_root: self.module_journal.pre_lane_root.clone(),
            post_root: self.post_state.state_root()?,
        };
        if self.module_journal.lane_id != LaneIdV2::ASSET_TRANSFER
            || self.module_journal.post_lane_root != self.post_state.state_root()?
            || self.module_journal.module_release_id != self.post_state.module_release_id
            || self.effects.lane_writes != vec![expected_write]
            || self.module_journal.effect_plan_root != self.effects.effect_plan_root()?
            || self.effects.occurrence_consumptions
                != vec![self.module_journal.command_occurrence_id.clone()]
            || !self.effects.external_outbox_enqueue.is_empty()
            || !self.module_journal.private_port_root.is_zero()
            || !self.module_journal.terminal_obligations_root.is_zero()
            || !self.module_journal.oracle_occurrence_plan_root.is_zero()
            || !self.post_state.policy_origin_bindings_hold()
        {
            return Err(AbiErrorV2::InvalidBinding("asset lane accepted bindings"));
        }
        Ok(())
    }

    pub const fn route(&self) -> AssetLaneRouteV2 {
        self.route
    }

    pub fn source_leaf_journal_root(&self) -> &RootV2 {
        &self.source_leaf_journal_root
    }

    pub fn post_state(&self) -> &AssetLaneStateV2 {
        &self.post_state
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV2 {
        &self.effects
    }

    pub fn module_journal(&self) -> &LaneModuleTransitionJournalV2 {
        &self.module_journal
    }

    pub fn receipt_root(&self) -> &RootV2 {
        &self.module_journal.receipt_root
    }

    pub const fn production_authority(&self) -> &'static str {
        ASSET_LANE_PRODUCTION_AUTHORITY_V2
    }

    pub const fn profile_authentication(&self) -> &'static str {
        ASSET_LANE_PROFILE_AUTHENTICATION_V2
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AssetLaneRejectedV2 {
    route: AssetLaneRouteV2,
    code: AssetLaneRejectCodeV2,
    pre_state_root: RootV2,
    post_state_root: RootV2,
    effects: GlobalEconomicEffectPlanV2,
}

impl AssetLaneRejectedV2 {
    pub(crate) fn new(
        route: AssetLaneRouteV2,
        code: AssetLaneRejectCodeV2,
        pre_state_root: RootV2,
    ) -> AbiResultV2<Self> {
        let rejected = Self {
            route,
            code,
            post_state_root: pre_state_root.clone(),
            pre_state_root,
            effects: GlobalEconomicEffectPlanV2::empty(),
        };
        rejected.validate()?;
        Ok(rejected)
    }

    pub fn validate(&self) -> AbiResultV2<()> {
        self.pre_state_root
            .validate("asset lane rejected pre root", false)?;
        self.post_state_root
            .validate("asset lane rejected post root", false)?;
        self.effects.validate()?;
        if self.pre_state_root != self.post_state_root || !self.effects.is_empty() {
            return Err(AbiErrorV2::InvalidBinding(
                "asset lane rejection is not a no-op",
            ));
        }
        Ok(())
    }

    pub const fn route(&self) -> AssetLaneRouteV2 {
        self.route
    }

    pub const fn code(&self) -> AssetLaneRejectCodeV2 {
        self.code
    }

    pub fn pre_state_root(&self) -> &RootV2 {
        &self.pre_state_root
    }

    pub fn post_state_root(&self) -> &RootV2 {
        &self.post_state_root
    }

    pub fn effects(&self) -> &GlobalEconomicEffectPlanV2 {
        &self.effects
    }

    pub const fn production_authority(&self) -> &'static str {
        ASSET_LANE_PRODUCTION_AUTHORITY_V2
    }

    pub const fn profile_authentication(&self) -> &'static str {
        ASSET_LANE_PROFILE_AUTHENTICATION_V2
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
#[must_use]
pub enum AssetLaneResultV2 {
    Accepted(Box<AssetLaneAcceptedV2>),
    Rejected(Box<AssetLaneRejectedV2>),
}
