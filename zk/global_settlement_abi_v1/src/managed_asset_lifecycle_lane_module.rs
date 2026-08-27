use serde::{Deserialize, Serialize};

use crate::asset_lane_projection::{
    project_managed_asset_lifecycle_state_v1, AssetLanePrivatePortV1,
    ASSET_LANE_PRIVATE_PORT_SCHEMA_V1,
};
use crate::canonical::{
    hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, MAX_ASSET_CUSTODY_ROWS_V1, ZERO_ROOT_V1,
};
use crate::effects::GlobalEconomicEffectPlanV1;
use crate::managed_asset_lifecycle::transition_managed_asset_lifecycle_v1;
use crate::managed_asset_lifecycle_types::{
    ManagedAssetLifecycleAcceptedV1, ManagedAssetLifecycleCommandV1,
    ManagedAssetLifecycleContextV1, ManagedAssetLifecycleRejectedV1, ManagedAssetLifecycleResultV1,
    ManagedAssetLifecycleStateV1, MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1,
};
use crate::proof::LaneModuleTransitionJournalV1;
use crate::state::EconomicAmountV1;

pub const MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1: &str =
    "zenodex/managed-asset-lifecycle-lane-module-input/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleLaneModuleInputV1 {
    pub schema: String,
    pub context: ManagedAssetLifecycleContextV1,
    pub pre_state: ManagedAssetLifecycleStateV1,
    pub command: ManagedAssetLifecycleCommandV1,
    pub asset_policy_registry_root: RootV1,
    pub fee_policy_registry_root: RootV1,
    pub custody: Vec<EconomicAmountV1>,
}

impl ManagedAssetLifecycleLaneModuleInputV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != MANAGED_ASSET_LIFECYCLE_LANE_MODULE_INPUT_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        self.context.validate()?;
        self.pre_state.validate()?;
        self.command.validate()?;
        self.asset_policy_registry_root
            .validate("managed asset lane module asset policy registry", false)?;
        self.fee_policy_registry_root
            .validate("managed asset lane module fee policy registry", false)?;
        if self.custody.len() > MAX_ASSET_CUSTODY_ROWS_V1 {
            return Err(AbiErrorV1::InvalidBounds(
                "managed asset lane module custody rows",
            ));
        }
        project_managed_asset_lifecycle_state_v1(
            &self.pre_state,
            &self.asset_policy_registry_root,
            &self.fee_policy_registry_root,
            self.custody.clone(),
        )?;
        Ok(())
    }

    pub fn statement_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("managed-asset-lifecycle-lane-module-statement-v1", self)
    }
}

#[derive(Serialize)]
struct ManagedAssetLifecycleLaneModuleReceiptBodyV1<'a> {
    statement_root: &'a RootV1,
    pre_state_root: &'a RootV1,
    post_state_root: &'a RootV1,
    effect_plan_root: &'a RootV1,
    private_port_root: &'a RootV1,
    terminal_obligations_root: &'a RootV1,
}

fn receipt_root(
    statement_root: &RootV1,
    module_journal: &LaneModuleTransitionJournalV1,
    private_port: &AssetLanePrivatePortV1,
    effects: &GlobalEconomicEffectPlanV1,
) -> AbiResultV1<RootV1> {
    let effect_plan_root = effects.effect_plan_root()?;
    let private_port_root = private_port.port_root()?;
    hash_global_v1(
        "managed-asset-lifecycle-lane-module-receipt-v1",
        &ManagedAssetLifecycleLaneModuleReceiptBodyV1 {
            statement_root,
            pre_state_root: &module_journal.pre_lane_root,
            post_state_root: &module_journal.post_lane_root,
            effect_plan_root: &effect_plan_root,
            private_port_root: &private_port_root,
            terminal_obligations_root: &private_port.terminal_obligations_root,
        },
    )
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ManagedAssetLifecycleLaneModuleAcceptedV1 {
    pub statement_root: RootV1,
    pub post_state: ManagedAssetLifecycleStateV1,
    pub effects: GlobalEconomicEffectPlanV1,
    pub module_journal: LaneModuleTransitionJournalV1,
    pub private_port: AssetLanePrivatePortV1,
}

impl ManagedAssetLifecycleLaneModuleAcceptedV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.statement_root
            .validate("managed asset lane module statement", false)?;
        ManagedAssetLifecycleAcceptedV1 {
            post_state: self.post_state.clone(),
            effects: self.effects.clone(),
            module_journal: self.module_journal.clone(),
        }
        .validate()?;
        self.private_port.validate()?;
        if self.private_port.producer_module_schema != MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1
            || self.private_port.module_release_id != self.module_journal.module_release_id
            || self.private_port.command_occurrence_id != self.module_journal.command_occurrence_id
            || self.private_port.module_effect_plan_root != self.effects.effect_plan_root()?
            || self.module_journal.private_port_root != self.private_port.port_root()?
            || self.module_journal.terminal_obligations_root
                != self.private_port.terminal_obligations_root
            || self.private_port.post_state.balances != self.post_state.balances
            || self.private_port.post_state.supplies != self.post_state.supplies
        {
            return Err(AbiErrorV1::InvalidBinding(
                "managed asset lane module accepted output",
            ));
        }
        if self.module_journal.receipt_root
            != receipt_root(
                &self.statement_root,
                &self.module_journal,
                &self.private_port,
                &self.effects,
            )?
        {
            return Err(AbiErrorV1::InvalidBinding(
                "managed asset lane module receipt root",
            ));
        }
        Ok(())
    }

    pub fn receipt_root(&self) -> &RootV1 {
        &self.module_journal.receipt_root
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ManagedAssetLifecycleLaneModuleResultV1 {
    Accepted(Box<ManagedAssetLifecycleLaneModuleAcceptedV1>),
    Rejected(Box<ManagedAssetLifecycleRejectedV1>),
}

fn private_port(
    module_input: &ManagedAssetLifecycleLaneModuleInputV1,
    base_accepted: &ManagedAssetLifecycleAcceptedV1,
) -> AbiResultV1<AssetLanePrivatePortV1> {
    let project = project_managed_asset_lifecycle_state_v1;
    let pre_state = project(
        &module_input.pre_state,
        &module_input.asset_policy_registry_root,
        &module_input.fee_policy_registry_root,
        module_input.custody.clone(),
    )?;
    let post_state = project(
        &base_accepted.post_state,
        &module_input.asset_policy_registry_root,
        &module_input.fee_policy_registry_root,
        module_input.custody.clone(),
    )?;
    let port = AssetLanePrivatePortV1 {
        schema: ASSET_LANE_PRIVATE_PORT_SCHEMA_V1.to_owned(),
        producer_module_schema: MANAGED_ASSET_LIFECYCLE_MODULE_SCHEMA_V1.to_owned(),
        module_release_id: module_input.context.module_release_id.clone(),
        command_occurrence_id: module_input.context.command_occurrence_id.clone(),
        pre_state,
        post_state,
        module_effect_plan_root: base_accepted.effects.effect_plan_root()?,
        terminal_obligations_root: RootV1::parse(
            ZERO_ROOT_V1,
            "managed asset lane module terminal root",
            true,
        )?,
    };
    port.validate()?;
    Ok(port)
}

fn bound_journal(
    base_accepted: &ManagedAssetLifecycleAcceptedV1,
    private_port: &AssetLanePrivatePortV1,
    bound_receipt_root: RootV1,
) -> AbiResultV1<LaneModuleTransitionJournalV1> {
    let base = &base_accepted.module_journal;
    Ok(LaneModuleTransitionJournalV1 {
        schema: base.schema.clone(),
        chain_id: base.chain_id.clone(),
        deployment_root: base.deployment_root.clone(),
        profile_root: base.profile_root.clone(),
        writer_epoch: base.writer_epoch,
        lane_id: base.lane_id,
        module_release_id: base.module_release_id.clone(),
        command_occurrence_id: base.command_occurrence_id.clone(),
        pre_lane_root: base.pre_lane_root.clone(),
        post_lane_root: base.post_lane_root.clone(),
        effect_plan_root: base.effect_plan_root.clone(),
        private_port_root: private_port.port_root()?,
        receipt_root: bound_receipt_root,
        terminal_obligations_root: base.terminal_obligations_root.clone(),
    })
}

#[must_use = "the result owns the only candidate effects and bound module journal"]
pub fn transition_managed_asset_lifecycle_lane_module_v1(
    module_input: &ManagedAssetLifecycleLaneModuleInputV1,
) -> AbiResultV1<ManagedAssetLifecycleLaneModuleResultV1> {
    module_input.validate()?;
    let base_result = transition_managed_asset_lifecycle_v1(
        &module_input.context,
        &module_input.pre_state,
        &module_input.command,
    )?;
    let base_accepted = match base_result {
        ManagedAssetLifecycleResultV1::Accepted(accepted) => *accepted,
        ManagedAssetLifecycleResultV1::Rejected(rejected) => {
            return Ok(ManagedAssetLifecycleLaneModuleResultV1::Rejected(rejected));
        }
    };
    let private_port = private_port(module_input, &base_accepted)?;
    let statement_root = module_input.statement_root()?;
    let bound_receipt_root = receipt_root(
        &statement_root,
        &base_accepted.module_journal,
        &private_port,
        &base_accepted.effects,
    )?;
    let module_journal = bound_journal(&base_accepted, &private_port, bound_receipt_root)?;
    let accepted = ManagedAssetLifecycleLaneModuleAcceptedV1 {
        statement_root,
        post_state: base_accepted.post_state,
        effects: base_accepted.effects,
        module_journal,
        private_port,
    };
    accepted.validate()?;
    Ok(ManagedAssetLifecycleLaneModuleResultV1::Accepted(Box::new(
        accepted,
    )))
}

pub(crate) fn recompute_managed_asset_lifecycle_lane_module_accepted_v1(
    module_input: &ManagedAssetLifecycleLaneModuleInputV1,
    accepted: &ManagedAssetLifecycleLaneModuleAcceptedV1,
) -> AbiResultV1<ManagedAssetLifecycleLaneModuleAcceptedV1> {
    accepted.validate()?;
    match transition_managed_asset_lifecycle_lane_module_v1(module_input)? {
        ManagedAssetLifecycleLaneModuleResultV1::Accepted(expected)
            if expected.as_ref() == accepted =>
        {
            Ok(*expected)
        }
        ManagedAssetLifecycleLaneModuleResultV1::Accepted(_) => Err(AbiErrorV1::InvalidBinding(
            "managed lifecycle supplied acceptance differs from recomputation",
        )),
        ManagedAssetLifecycleLaneModuleResultV1::Rejected(_) => Err(AbiErrorV1::InvalidBinding(
            "managed lifecycle supplied acceptance recomputes to rejection",
        )),
    }
}
