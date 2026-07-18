"""Pure, identity-bound planning for proof-mining treasury payouts.

The proof-mining manager owns reward calculation and replay protection. This
module owns the custody-side contract that the reward pool and recipient are
distinct principals and that one canonical effect exists per principal.
"""

from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import TypeAlias, TypeGuard

from ..state.canonical import canonical_hex_fixed_allow_0x


class ProofMiningPayoutRejectCode(str, Enum):
    INVALID_PARTICIPANT = "InvalidParticipant"
    INVALID_AMOUNT = "InvalidAmount"
    INVALID_BALANCE = "InvalidBalance"
    SELF_PAYMENT = "SelfPayment"
    INSUFFICIENT_POOL = "InsufficientPool"


_REJECT_MESSAGES = {
    ProofMiningPayoutRejectCode.INVALID_PARTICIPANT: (
        "proof mining payout participants must be canonical 48-byte pubkeys"
    ),
    ProofMiningPayoutRejectCode.INVALID_AMOUNT: "proof mining reward amount must be a positive int",
    ProofMiningPayoutRejectCode.INVALID_BALANCE: "proof mining payout balances must be non-negative ints",
    ProofMiningPayoutRejectCode.SELF_PAYMENT: "proof mining reward recipient must differ from reward pool",
    ProofMiningPayoutRejectCode.INSUFFICIENT_POOL: "reward pool insufficient native balance",
}


@dataclass(frozen=True)
class ProofMiningPayoutRejected:
    code: ProofMiningPayoutRejectCode

    @property
    def message(self) -> str:
        return _REJECT_MESSAGES[self.code]


@dataclass(frozen=True, order=True)
class NativeBalanceEffect:
    pubkey: str
    delta_base_units: int


@dataclass(frozen=True)
class ProofMiningPayoutPlan:
    reward_pool_pubkey: str
    recipient_pubkey: str
    reward_amount_base_units: int
    reward_pool_balance_before_base_units: int
    reward_pool_balance_after_base_units: int
    recipient_balance_before_base_units: int
    recipient_balance_after_base_units: int
    effects: tuple[NativeBalanceEffect, NativeBalanceEffect]


ProofMiningPayoutDecision: TypeAlias = ProofMiningPayoutPlan | ProofMiningPayoutRejected


def _is_canonical_pubkey(value: object) -> TypeGuard[str]:
    if not isinstance(value, str):
        return False
    try:
        canonical = canonical_hex_fixed_allow_0x(value, nbytes=48, name="participant")
    except (TypeError, ValueError):
        return False
    return value == canonical


def _is_nonnegative_int(value: object) -> TypeGuard[int]:
    return isinstance(value, int) and not isinstance(value, bool) and value >= 0


def plan_proof_mining_payout(
    *,
    reward_pool_pubkey: object,
    recipient_pubkey: object,
    reward_amount_base_units: object,
    reward_pool_balance_base_units: object,
    recipient_balance_base_units: object,
) -> ProofMiningPayoutDecision:
    """Return a canonical conserved payout plan or a typed semantic rejection."""
    if not _is_canonical_pubkey(reward_pool_pubkey) or not _is_canonical_pubkey(recipient_pubkey):
        return ProofMiningPayoutRejected(ProofMiningPayoutRejectCode.INVALID_PARTICIPANT)
    pool_pubkey = reward_pool_pubkey
    recipient = recipient_pubkey
    if pool_pubkey == recipient:
        return ProofMiningPayoutRejected(ProofMiningPayoutRejectCode.SELF_PAYMENT)
    if (
        not isinstance(reward_amount_base_units, int)
        or isinstance(reward_amount_base_units, bool)
        or reward_amount_base_units <= 0
    ):
        return ProofMiningPayoutRejected(ProofMiningPayoutRejectCode.INVALID_AMOUNT)
    if not _is_nonnegative_int(reward_pool_balance_base_units) or not _is_nonnegative_int(
        recipient_balance_base_units
    ):
        return ProofMiningPayoutRejected(ProofMiningPayoutRejectCode.INVALID_BALANCE)

    reward_amount = reward_amount_base_units
    pool_balance_before = reward_pool_balance_base_units
    recipient_balance_before = recipient_balance_base_units
    if reward_amount > pool_balance_before:
        return ProofMiningPayoutRejected(ProofMiningPayoutRejectCode.INSUFFICIENT_POOL)

    pool_balance_after = pool_balance_before - reward_amount
    recipient_balance_after = recipient_balance_before + reward_amount
    pool_effect = NativeBalanceEffect(pubkey=pool_pubkey, delta_base_units=-reward_amount)
    recipient_effect = NativeBalanceEffect(pubkey=recipient, delta_base_units=reward_amount)
    effects = (
        (pool_effect, recipient_effect)
        if pool_pubkey < recipient
        else (recipient_effect, pool_effect)
    )
    return ProofMiningPayoutPlan(
        reward_pool_pubkey=pool_pubkey,
        recipient_pubkey=recipient,
        reward_amount_base_units=reward_amount,
        reward_pool_balance_before_base_units=pool_balance_before,
        reward_pool_balance_after_base_units=pool_balance_after,
        recipient_balance_before_base_units=recipient_balance_before,
        recipient_balance_after_base_units=recipient_balance_after,
        effects=effects,
    )
