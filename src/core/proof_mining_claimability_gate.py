from __future__ import annotations

from dataclasses import dataclass
from types import MappingProxyType
from typing import Any, Mapping

REJECT_DISABLED = "Disabled"
REJECT_RECIPIENT_IS_REWARD_POOL = "RecipientIsRewardPool"
REJECT_WINNER_MISMATCH = "WinnerMismatch"
REJECT_PROPOSAL_HASH_MISMATCH = "ProposalHashMismatch"
REJECT_NEGATIVE_POOL_BALANCE = "NegativePoolBalance"
REJECT_RUNTIME_POOL_PUBKEY_MISMATCH = "RuntimePoolPubkeyMismatch"
REJECT_RUNTIME_POOL_BALANCE_DRIFT = "RuntimePoolBalanceDrift"
REJECT_MANAGER_REJECTED = "ManagerRejected"
REJECT_OK = "Ok"

REJECT_CODE_TO_ERROR = {
    REJECT_DISABLED: "proof mining disabled (set TAU_DEX_PROOF_MINING_POOL_PUBKEY)",
    REJECT_RECIPIENT_IS_REWARD_POOL: "proof mining reward pool cannot receive its own payout",
    REJECT_WINNER_MISMATCH: "proof mining winner.miner_id mismatch",
    REJECT_PROPOSAL_HASH_MISMATCH: "proof mining claim proposal_hash mismatch",
    REJECT_NEGATIVE_POOL_BALANCE: "reward pool chain balance must be non-negative",
    REJECT_RUNTIME_POOL_PUBKEY_MISMATCH: "proof mining reward pool pubkey mismatch",
    REJECT_RUNTIME_POOL_BALANCE_DRIFT: "proof mining reward pool balance drift",
    REJECT_MANAGER_REJECTED: "proof mining manager rejected",
}


@dataclass(frozen=True)
class ProofMiningClaimabilityGateOutcome:
    enabled: bool
    claimable: bool
    reject_code: str
    reward_amount: int
    reward_pool_before: int
    reward_pool_after: int
    checks: Mapping[str, bool]

    def __post_init__(self) -> None:
        object.__setattr__(self, "checks", MappingProxyType(dict(self.checks)))


@dataclass(frozen=True, slots=True)
class ProofMiningRecipientGateOutcome:
    admitted: bool
    reject_code: str


def _require_bool(value: Any, *, name: str) -> bool:
    if type(value) is not bool:
        raise TypeError(f"{name} must be a bool")
    return value


def evaluate_proof_mining_recipient_gate(
    *,
    recipient_distinct_from_reward_pool: bool,
) -> ProofMiningRecipientGateOutcome:
    """Reject the alias that would turn a payout into balance creation."""

    distinct = _require_bool(
        recipient_distinct_from_reward_pool,
        name="recipient_distinct_from_reward_pool",
    )
    return ProofMiningRecipientGateOutcome(
        admitted=distinct,
        reject_code=REJECT_OK if distinct else REJECT_RECIPIENT_IS_REWARD_POOL,
    )


def _require_non_negative_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    if int(value) < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def evaluate_proof_mining_claimability_gate(
    *,
    reward_pool_configured: bool,
    winner_matches_sender: bool,
    recipient_distinct_from_reward_pool: bool,
    proposal_hash_matches_context: bool,
    reward_pool_balance_non_negative: bool,
    runtime_state_present: bool,
    reward_pool_pubkey_matches_state: bool,
    reward_pool_balance_matches_state: bool,
    manager_ok: bool,
    reward_amount: int,
    reward_pool_before: int,
    reward_pool_after: int,
) -> ProofMiningClaimabilityGateOutcome:
    configured = _require_bool(
        reward_pool_configured,
        name="reward_pool_configured",
    )
    winner_match = _require_bool(
        winner_matches_sender,
        name="winner_matches_sender",
    )
    recipient_distinct = evaluate_proof_mining_recipient_gate(
        recipient_distinct_from_reward_pool=recipient_distinct_from_reward_pool,
    ).admitted
    proposal_match = _require_bool(
        proposal_hash_matches_context,
        name="proposal_hash_matches_context",
    )
    pool_balance_non_negative = _require_bool(
        reward_pool_balance_non_negative,
        name="reward_pool_balance_non_negative",
    )
    runtime_present_input = _require_bool(
        runtime_state_present,
        name="runtime_state_present",
    )
    runtime_pubkey_match_input = _require_bool(
        reward_pool_pubkey_matches_state,
        name="reward_pool_pubkey_matches_state",
    )
    runtime_balance_match_input = _require_bool(
        reward_pool_balance_matches_state,
        name="reward_pool_balance_matches_state",
    )
    manager_accepted = _require_bool(manager_ok, name="manager_ok")
    payout = _require_non_negative_int(reward_amount, name="reward_amount")
    reward_before = _require_non_negative_int(reward_pool_before, name="reward_pool_before")
    reward_after = _require_non_negative_int(reward_pool_after, name="reward_pool_after")
    if reward_after > reward_before:
        raise ValueError("reward_pool_after must not exceed reward_pool_before")
    if payout != reward_before - reward_after:
        raise ValueError("reward_amount must equal reward_pool_before - reward_pool_after")

    runtime_present = runtime_present_input
    runtime_pubkey_match = runtime_present and runtime_pubkey_match_input
    runtime_balance_match = (
        runtime_present and runtime_pubkey_match and runtime_balance_match_input
    )
    checks: dict[str, bool] = {
        "reward_pool_configured": configured,
        "winner_matches_sender": winner_match,
        "recipient_distinct_from_reward_pool": recipient_distinct,
        "proposal_hash_matches_context": proposal_match,
        "reward_pool_balance_non_negative": pool_balance_non_negative,
        "runtime_state_present": runtime_present,
        "reward_pool_pubkey_matches_state": runtime_pubkey_match,
        "reward_pool_balance_matches_state": runtime_balance_match,
        "runtime_apply_ok": manager_accepted,
    }
    if not checks["reward_pool_configured"]:
        reject_code = REJECT_DISABLED
    elif not checks["recipient_distinct_from_reward_pool"]:
        reject_code = REJECT_RECIPIENT_IS_REWARD_POOL
    elif not checks["winner_matches_sender"]:
        reject_code = REJECT_WINNER_MISMATCH
    elif not checks["proposal_hash_matches_context"]:
        reject_code = REJECT_PROPOSAL_HASH_MISMATCH
    elif not checks["reward_pool_balance_non_negative"]:
        reject_code = REJECT_NEGATIVE_POOL_BALANCE
    elif checks["runtime_state_present"] and not checks["reward_pool_pubkey_matches_state"]:
        reject_code = REJECT_RUNTIME_POOL_PUBKEY_MISMATCH
    elif checks["runtime_state_present"] and not checks["reward_pool_balance_matches_state"]:
        reject_code = REJECT_RUNTIME_POOL_BALANCE_DRIFT
    elif not checks["runtime_apply_ok"]:
        reject_code = REJECT_MANAGER_REJECTED
    else:
        reject_code = REJECT_OK

    return ProofMiningClaimabilityGateOutcome(
        enabled=bool(checks["reward_pool_configured"]),
        claimable=bool(reject_code == REJECT_OK),
        reject_code=reject_code,
        reward_amount=payout,
        reward_pool_before=reward_before,
        reward_pool_after=reward_after,
        checks=checks,
    )
