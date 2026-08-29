use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    GlobalEconomicEffectPlanV1, LaneTransitionRejectCodeV1, LaneTransitionRejectedV1,
};
use crate::lane_capability_registry::{
    lane_capability_registry_root_v1, resolve_lane_capability_v1, LaneCapabilityDispositionV1,
    LANE_CAPABILITY_REGISTRY_V1,
};
use crate::release::LaneIdV1;

pub const CURRENT_PROFILE_LANE_COMMAND_SCHEMA_V1: &str = "zenodex/current-profile-lane-command/v1";

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CurrentProfileLaneStateV1 {
    pub lane_id: LaneIdV1,
    pub lane_state_root: RootV1,
}

impl CurrentProfileLaneStateV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.lane_state_root
            .validate("current-profile lane state root", false)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct CurrentProfileLaneCommandV1 {
    pub lane_id: LaneIdV1,
    pub capability_id: String,
    pub command_body_hash: RootV1,
}

impl CurrentProfileLaneCommandV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        resolve_lane_capability_v1(self.lane_id, &self.capability_id)?;
        self.command_body_hash
            .validate("current-profile command body hash", false)
    }

    pub fn command_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        #[derive(Serialize)]
        struct CommandCommitmentV1<'a> {
            schema: &'static str,
            registry_root: RootV1,
            lane_id: LaneIdV1,
            capability_id: &'a str,
            command_body_hash: &'a RootV1,
        }
        hash_global_v1(
            "current-profile-lane-command-v1",
            &CommandCommitmentV1 {
                schema: CURRENT_PROFILE_LANE_COMMAND_SCHEMA_V1,
                registry_root: lane_capability_registry_root_v1()?,
                lane_id: self.lane_id,
                capability_id: &self.capability_id,
                command_body_hash: &self.command_body_hash,
            },
        )
    }
}

fn empty_effects_v1() -> GlobalEconomicEffectPlanV1 {
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

fn lane_disposition_v1(lane_id: LaneIdV1) -> LaneCapabilityDispositionV1 {
    LANE_CAPABILITY_REGISTRY_V1
        .iter()
        .find(|row| row.lane_id == lane_id)
        .expect("closed lane registry must contain every LaneIdV1")
        .disposition
}

#[must_use = "a current-profile capability must remain an observed rejection"]
pub fn transition_current_profile_lane_v1(
    pre_state: &CurrentProfileLaneStateV1,
    command: &CurrentProfileLaneCommandV1,
) -> AbiResultV1<LaneTransitionRejectedV1> {
    pre_state.validate()?;
    command.validate()?;
    let code = if pre_state.lane_id != command.lane_id {
        LaneTransitionRejectCodeV1::INVALID_CONTEXT
    } else if lane_disposition_v1(command.lane_id)
        == LaneCapabilityDispositionV1::DISABLED_PENDING_COMPLETE_PROFILE
    {
        LaneTransitionRejectCodeV1::DISABLED_FEATURE
    } else {
        LaneTransitionRejectCodeV1::POLICY_REJECT
    };
    let rejected = LaneTransitionRejectedV1 {
        code,
        pre_state_root: pre_state.lane_state_root.clone(),
        post_state_root: pre_state.lane_state_root.clone(),
        effects: empty_effects_v1(),
    };
    rejected.validate()?;
    Ok(rejected)
}
