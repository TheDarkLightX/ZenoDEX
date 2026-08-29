from __future__ import annotations

import pytest

from src.core.global_settlement_types_v1 import (
    GlobalEconomicEffectPlanV1,
    LaneTransitionRejectCodeV1,
    LaneTransitionRejectedV1,
)
from src.core.m6_safe_mount_types_v1 import (
    M6_RESEARCH_DISABLED_COMMANDS_V1,
    GlobalCommandKindV1,
)
from src.core.proof_rewards_policy_blocked_lane_v1 import (
    PROOF_REWARDS_POLICY_BLOCKED_COMMANDS_V1,
    ProofRewardsCapabilityV1,
    ProofRewardsPolicyBlockedCommandV1,
    ProofRewardsPolicyBlockedStateV1,
    transition_proof_rewards_policy_blocked_v1,
)


def _root(value: int) -> str:
    return f"0x{value:064x}"


def _command(capability: ProofRewardsCapabilityV1) -> ProofRewardsPolicyBlockedCommandV1:
    return ProofRewardsPolicyBlockedCommandV1(capability, _root(7))


def test_every_proof_reward_capability_rejects_until_policy_is_selected() -> None:
    # Arrange
    state = ProofRewardsPolicyBlockedStateV1()

    # Act
    results = tuple(
        transition_proof_rewards_policy_blocked_v1(state, _command(capability))
        for capability in ProofRewardsCapabilityV1
    )

    # Assert
    assert PROOF_REWARDS_POLICY_BLOCKED_COMMANDS_V1 == tuple(ProofRewardsCapabilityV1)
    assert len(results) == 6
    assert all(type(result) is LaneTransitionRejectedV1 for result in results)
    assert all(result.code is LaneTransitionRejectCodeV1.POLICY_REJECT for result in results)
    assert all(result.pre_state_root == state.state_root for result in results)
    assert all(result.post_state_root == state.state_root for result in results)
    assert all(result.effects == GlobalEconomicEffectPlanV1.empty() for result in results)


def test_policy_blocked_state_contains_no_caller_selected_reward_semantics() -> None:
    # Arrange / Act
    state = ProofRewardsPolicyBlockedStateV1()

    # Assert
    assert state.reward_reserves == ()
    assert state.tasks == ()
    assert state.claim_nullifiers == ()
    assert state.terminal_obligations == ()


def test_proof_reward_blocked_roots_are_python_rust_parity_vectors() -> None:
    # Arrange
    state = ProofRewardsPolicyBlockedStateV1()
    command = _command(ProofRewardsCapabilityV1.REWARD_PAYOUT)

    # Act / Assert
    assert state.state_root == (
        "0xd322bac2dd8f9fa0a67c4036b87f41ba7dc9f1d849dada1cc65e5463c67fdf74"
    )
    assert command.command_root == (
        "0x85fcd86af1779c56743379a9cbfa28ae4b28bd5ce260de83a235f3701985e9b2"
    )


def test_exact_owned_types_are_required_before_policy_rejection() -> None:
    # Arrange
    state = ProofRewardsPolicyBlockedStateV1()
    command = _command(ProofRewardsCapabilityV1.CLAIM_NULLIFIER)

    class StateSubclass(ProofRewardsPolicyBlockedStateV1):
        pass

    class CommandSubclass(ProofRewardsPolicyBlockedCommandV1):
        pass

    # Act / Assert
    with pytest.raises(TypeError, match="state must be the exact typed value"):
        transition_proof_rewards_policy_blocked_v1(StateSubclass(), command)
    with pytest.raises(TypeError, match="command must be the exact typed value"):
        transition_proof_rewards_policy_blocked_v1(
            state,
            CommandSubclass(command.capability, command.command_body_hash),
        )


def test_legacy_m6_reward_command_remains_disabled() -> None:
    # Arrange / Act / Assert
    assert GlobalCommandKindV1.ZRPF_PROVER_REWARD in M6_RESEARCH_DISABLED_COMMANDS_V1
