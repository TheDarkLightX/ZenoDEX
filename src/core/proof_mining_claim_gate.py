from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

PROOF_MINING_BASE_REWARD_MAX = 128
PROOF_MINING_EPOCH_MAX = 7
PROOF_MINING_PROPOSAL_SLOT_MAX = 7
PROOF_MINING_PROVER_ID_MAX = 3
PROOF_MINING_POOL_BALANCE_MAX = 1000
PROOF_MINING_CLAIM_GATE_FLAG_NAMES = (
    "proof_ok",
    "binding_ok",
    "policy_ok",
    "nonce_ok",
    "unclaimed_ok",
)


@dataclass(frozen=True)
class ProofMiningClaimGateOutcome:
    reward_amount: int
    reward_pool_after: int
    flags_ok: bool
    budget_ok: bool
    admissible: bool
    checks: Mapping[str, bool]


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _require_flag_int(value: Any, *, name: str) -> int:
    flag = _require_int(value, name=name)
    if flag not in (0, 1):
        raise ValueError(f"{name} must be 0 or 1")
    return int(flag)


def schedule_proof_mining_reward_amount(*, base_reward: int, epoch: int) -> int:
    base = _require_int(base_reward, name="base_reward")
    ep = _require_int(epoch, name="epoch")
    if base < 1 or base > PROOF_MINING_BASE_REWARD_MAX:
        raise ValueError("base_reward out of range")
    if ep < 0 or ep > PROOF_MINING_EPOCH_MAX:
        raise ValueError("epoch out of range")
    shifted = int(base) >> int(ep)
    if shifted > 0:
        return int(shifted)
    return 1


def evaluate_proof_mining_claim_gate(
    *,
    base_reward: int,
    epoch: int,
    reward_pool_before: int,
    proof_ok: int,
    binding_ok: int,
    policy_ok: int,
    nonce_ok: int,
    unclaimed_ok: int,
) -> ProofMiningClaimGateOutcome:
    reward_pool = _require_int(reward_pool_before, name="reward_pool_before")
    if reward_pool < 0 or reward_pool > PROOF_MINING_POOL_BALANCE_MAX:
        raise ValueError("reward_pool_before out of range")
    flags = {
        "proof_ok": _require_flag_int(proof_ok, name="proof_ok"),
        "binding_ok": _require_flag_int(binding_ok, name="binding_ok"),
        "policy_ok": _require_flag_int(policy_ok, name="policy_ok"),
        "nonce_ok": _require_flag_int(nonce_ok, name="nonce_ok"),
        "unclaimed_ok": _require_flag_int(unclaimed_ok, name="unclaimed_ok"),
    }
    reward_amount = schedule_proof_mining_reward_amount(base_reward=base_reward, epoch=epoch)
    flags_ok = all(value == 1 for value in flags.values())
    budget_ok = bool(reward_pool >= reward_amount)
    reward_pool_after = int(reward_pool) - int(reward_amount)
    checks = {
        "flags_ok": bool(flags_ok),
        "budget_ok": bool(budget_ok),
        "admissible": bool(flags_ok and budget_ok),
    }
    return ProofMiningClaimGateOutcome(
        reward_amount=int(reward_amount),
        reward_pool_after=int(reward_pool_after),
        flags_ok=bool(flags_ok),
        budget_ok=bool(budget_ok),
        admissible=bool(flags_ok and budget_ok),
        checks=checks,
    )
