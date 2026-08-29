use serde_json::json;
use zenodex_global_settlement_abi_v1::{
    transition_proof_rewards_policy_blocked_v1, LaneTransitionRejectCodeV1,
    ProofRewardsCapabilityV1, ProofRewardsPolicyBlockedCommandV1, ProofRewardsPolicyBlockedStateV1,
    RootV1, PROOF_REWARDS_POLICY_BLOCKED_COMMANDS_V1, PROOF_REWARDS_POLICY_BLOCKED_STATE_SCHEMA_V1,
};

fn root(value: u64) -> RootV1 {
    RootV1::parse(
        format!("0x{value:064x}"),
        "proof reward policy-block test root",
        false,
    )
    .unwrap()
}

fn command(capability: ProofRewardsCapabilityV1) -> ProofRewardsPolicyBlockedCommandV1 {
    ProofRewardsPolicyBlockedCommandV1 {
        capability,
        command_body_hash: root(7),
    }
}

#[test]
fn every_proof_reward_capability_rejects_until_policy_is_selected() {
    // Arrange
    let state = ProofRewardsPolicyBlockedStateV1::new();

    // Act / Assert
    assert_eq!(PROOF_REWARDS_POLICY_BLOCKED_COMMANDS_V1.len(), 6);
    for capability in PROOF_REWARDS_POLICY_BLOCKED_COMMANDS_V1 {
        let rejected =
            transition_proof_rewards_policy_blocked_v1(&state, &command(capability)).unwrap();
        rejected.validate().unwrap();
        assert_eq!(rejected.code, LaneTransitionRejectCodeV1::POLICY_REJECT);
        assert_eq!(rejected.pre_state_root, state.state_root().unwrap());
        assert_eq!(rejected.post_state_root, state.state_root().unwrap());
        assert!(rejected.effects.is_empty());
    }
}

#[test]
fn blocked_state_and_command_roots_match_python_vectors() {
    // Arrange
    let state = ProofRewardsPolicyBlockedStateV1::new();
    let command = command(ProofRewardsCapabilityV1::REWARD_PAYOUT);

    // Act / Assert
    assert_eq!(
        state.state_root().unwrap().as_str(),
        "0xd322bac2dd8f9fa0a67c4036b87f41ba7dc9f1d849dada1cc65e5463c67fdf74"
    );
    assert_eq!(
        command.command_root().unwrap().as_str(),
        "0x85fcd86af1779c56743379a9cbfa28ae4b28bd5ce260de83a235f3701985e9b2"
    );
}

#[test]
fn nonempty_state_and_unknown_capability_fail_closed() {
    // Arrange
    let nonempty = json!({
        "schema": PROOF_REWARDS_POLICY_BLOCKED_STATE_SCHEMA_V1,
        "reward_reserves": ["caller-selected-reserve"],
        "tasks": [],
        "claim_nullifiers": [],
        "terminal_obligations": []
    });
    let unknown = json!({
        "capability": "caller_selected_reward",
        "command_body_hash": root(7)
    });

    // Act
    let decoded: ProofRewardsPolicyBlockedStateV1 = serde_json::from_value(nonempty).unwrap();

    // Assert
    assert!(decoded.validate().is_err());
    assert!(serde_json::from_value::<ProofRewardsPolicyBlockedCommandV1>(unknown).is_err());
}
