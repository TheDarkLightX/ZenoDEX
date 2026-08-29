"""Fail-closed PROOF_REWARDS core while governed policy UP-09 is unresolved.

The legacy reward path permits caller- or environment-selected reward
semantics.  This current-profile core contains no reserve, task, nullifier, or
terminal obligation and rejects every one of the six normative capabilities
as ``POLICY_REJECT``.  No rejection consumes an occurrence or emits an effect.

This is research-only closure evidence, not an implemented payout policy or a
mounted release.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Final

from .global_settlement_types_v1 import (
    LaneTransitionRejectCodeV1,
    LaneTransitionRejectedV1,
    _require_root,
    hash_global_v1,
)

PROOF_REWARDS_POLICY_BLOCKED_STATE_SCHEMA_V1: Final = (
    "zenodex/proof-rewards-policy-blocked-state/v1"
)


class ProofRewardsCapabilityV1(str, Enum):
    REWARD_RESERVE = "reward_reserve"
    VERIFIED_RESULT_BINDING = "verified_result_binding"
    CLAIMANT_BINDING = "claimant_binding"
    CLAIM_NULLIFIER = "claim_nullifier"
    REWARD_PAYOUT = "reward_payout"
    TASK_TERMINAL_STATE = "task_terminal_state"


PROOF_REWARDS_POLICY_BLOCKED_COMMANDS_V1: Final = tuple(ProofRewardsCapabilityV1)


@dataclass(frozen=True, slots=True)
class ProofRewardsPolicyBlockedCommandV1:
    capability: ProofRewardsCapabilityV1
    command_body_hash: str

    def __post_init__(self) -> None:
        if type(self.capability) is not ProofRewardsCapabilityV1:
            raise TypeError("proof reward capability must be the exact closed enum")
        if type(self.command_body_hash) is not str:
            raise TypeError("proof reward command body hash must be exact text")
        _require_root(self.command_body_hash, name="proof reward command body hash")

    @property
    def command_root(self) -> str:
        return hash_global_v1("proof-rewards-policy-blocked-command-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "capability": self.capability,
            "command_body_hash": self.command_body_hash,
        }


@dataclass(frozen=True, slots=True)
class ProofRewardsPolicyBlockedStateV1:
    reward_reserves: tuple[()] = ()
    tasks: tuple[()] = ()
    claim_nullifiers: tuple[()] = ()
    terminal_obligations: tuple[()] = ()

    def __post_init__(self) -> None:
        for field_name in (
            "reward_reserves",
            "tasks",
            "claim_nullifiers",
            "terminal_obligations",
        ):
            value = getattr(self, field_name)
            if type(value) is not tuple or value != ():
                raise ValueError(
                    f"policy-blocked proof reward {field_name} must be the exact empty tuple"
                )

    @property
    def state_root(self) -> str:
        return hash_global_v1("proof-rewards-policy-blocked-state-v1", self.to_canonical())

    def to_canonical(self) -> dict[str, object]:
        return {
            "schema": PROOF_REWARDS_POLICY_BLOCKED_STATE_SCHEMA_V1,
            "reward_reserves": self.reward_reserves,
            "tasks": self.tasks,
            "claim_nullifiers": self.claim_nullifiers,
            "terminal_obligations": self.terminal_obligations,
        }


def transition_proof_rewards_policy_blocked_v1(
    pre_state: ProofRewardsPolicyBlockedStateV1,
    command: ProofRewardsPolicyBlockedCommandV1,
) -> LaneTransitionRejectedV1:
    """Reject one exact capability attempt until UP-09 selects its policy."""

    if type(pre_state) is not ProofRewardsPolicyBlockedStateV1:
        raise TypeError("proof reward policy-blocked state must be the exact typed value")
    if type(command) is not ProofRewardsPolicyBlockedCommandV1:
        raise TypeError("proof reward policy-blocked command must be the exact typed value")
    pre_state.__post_init__()
    command.__post_init__()
    return LaneTransitionRejectedV1.reject(
        LaneTransitionRejectCodeV1.POLICY_REJECT,
        pre_state.state_root,
    )


__all__ = [
    "PROOF_REWARDS_POLICY_BLOCKED_COMMANDS_V1",
    "PROOF_REWARDS_POLICY_BLOCKED_STATE_SCHEMA_V1",
    "ProofRewardsCapabilityV1",
    "ProofRewardsPolicyBlockedCommandV1",
    "ProofRewardsPolicyBlockedStateV1",
    "transition_proof_rewards_policy_blocked_v1",
]
