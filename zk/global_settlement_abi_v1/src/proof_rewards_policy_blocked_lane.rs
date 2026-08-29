use serde::{Deserialize, Serialize};

use crate::canonical::{hash_global_v1, AbiErrorV1, AbiResultV1, RootV1, GLOBAL_SETTLEMENT_ABI_V1};
use crate::effects::{
    GlobalEconomicEffectPlanV1, LaneTransitionRejectCodeV1, LaneTransitionRejectedV1,
};

pub const PROOF_REWARDS_POLICY_BLOCKED_STATE_SCHEMA_V1: &str =
    "zenodex/proof-rewards-policy-blocked-state/v1";

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[allow(non_camel_case_types)]
pub enum ProofRewardsCapabilityV1 {
    #[serde(rename = "reward_reserve")]
    REWARD_RESERVE,
    #[serde(rename = "verified_result_binding")]
    VERIFIED_RESULT_BINDING,
    #[serde(rename = "claimant_binding")]
    CLAIMANT_BINDING,
    #[serde(rename = "claim_nullifier")]
    CLAIM_NULLIFIER,
    #[serde(rename = "reward_payout")]
    REWARD_PAYOUT,
    #[serde(rename = "task_terminal_state")]
    TASK_TERMINAL_STATE,
}

pub const PROOF_REWARDS_POLICY_BLOCKED_COMMANDS_V1: [ProofRewardsCapabilityV1; 6] = [
    ProofRewardsCapabilityV1::REWARD_RESERVE,
    ProofRewardsCapabilityV1::VERIFIED_RESULT_BINDING,
    ProofRewardsCapabilityV1::CLAIMANT_BINDING,
    ProofRewardsCapabilityV1::CLAIM_NULLIFIER,
    ProofRewardsCapabilityV1::REWARD_PAYOUT,
    ProofRewardsCapabilityV1::TASK_TERMINAL_STATE,
];

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ProofRewardsPolicyBlockedCommandV1 {
    pub capability: ProofRewardsCapabilityV1,
    pub command_body_hash: RootV1,
}

impl ProofRewardsPolicyBlockedCommandV1 {
    pub fn validate(&self) -> AbiResultV1<()> {
        self.command_body_hash
            .validate("proof reward command body hash", false)
    }

    pub fn command_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("proof-rewards-policy-blocked-command-v1", self)
    }
}

#[derive(Clone, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct ProofRewardsPolicyBlockedStateV1 {
    pub schema: String,
    pub reward_reserves: Vec<String>,
    pub tasks: Vec<String>,
    pub claim_nullifiers: Vec<String>,
    pub terminal_obligations: Vec<String>,
}

impl ProofRewardsPolicyBlockedStateV1 {
    pub fn new() -> Self {
        Self {
            schema: PROOF_REWARDS_POLICY_BLOCKED_STATE_SCHEMA_V1.to_owned(),
            reward_reserves: Vec::new(),
            tasks: Vec::new(),
            claim_nullifiers: Vec::new(),
            terminal_obligations: Vec::new(),
        }
    }

    pub fn validate(&self) -> AbiResultV1<()> {
        if self.schema != PROOF_REWARDS_POLICY_BLOCKED_STATE_SCHEMA_V1 {
            return Err(AbiErrorV1::InvalidSchema);
        }
        if !self.reward_reserves.is_empty()
            || !self.tasks.is_empty()
            || !self.claim_nullifiers.is_empty()
            || !self.terminal_obligations.is_empty()
        {
            return Err(AbiErrorV1::InvalidBinding(
                "policy-blocked proof reward lane must remain empty",
            ));
        }
        Ok(())
    }

    pub fn state_root(&self) -> AbiResultV1<RootV1> {
        self.validate()?;
        hash_global_v1("proof-rewards-policy-blocked-state-v1", self)
    }
}

impl Default for ProofRewardsPolicyBlockedStateV1 {
    fn default() -> Self {
        Self::new()
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

#[must_use = "a policy-blocked reward command must remain an observed rejection"]
pub fn transition_proof_rewards_policy_blocked_v1(
    pre_state: &ProofRewardsPolicyBlockedStateV1,
    command: &ProofRewardsPolicyBlockedCommandV1,
) -> AbiResultV1<LaneTransitionRejectedV1> {
    pre_state.validate()?;
    command.validate()?;
    let pre_state_root = pre_state.state_root()?;
    let rejected = LaneTransitionRejectedV1 {
        code: LaneTransitionRejectCodeV1::POLICY_REJECT,
        pre_state_root: pre_state_root.clone(),
        post_state_root: pre_state_root,
        effects: empty_effects_v1(),
    };
    rejected.validate()?;
    Ok(rejected)
}
