"""Public request objects for batch-clearing entry points."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional

from ..state.balances import BalanceTable, PubKey
from ..state.intents import Intent
from ..state.lp import LPTable
from ..state.pools import PoolState
from .domain_limits import is_strict_int
from .protocol_fee_policy import canonical_protocol_fee_policy


@dataclass(frozen=True)
class ComputeSettlementRequest:
    """Input shape for deterministic multi-pool settlement computation."""

    intents: List[Intent]
    pools: Dict[str, PoolState]
    balances: BalanceTable
    lp_balances: Optional[LPTable] = None
    swap_ordering: str = "greedy_ab_refined"
    protocol_fee_share_bps: int = 0
    protocol_fee_recipient_pubkey: Optional[PubKey] = None
    swap_tiebreak_seed: bytes | None = None


@dataclass(frozen=True)
class ClearBatchSinglePoolRequest:
    """Input shape for deterministic single-pool batch clearing."""

    intents: List[Intent]
    pool_state: PoolState
    balances: BalanceTable
    lp_balances: LPTable
    swap_ordering: str = "greedy_ab_refined"
    protocol_fee_share_bps: int = 0
    protocol_fee_recipient_pubkey: Optional[PubKey] = None
    swap_tiebreak_seed: bytes | None = None


def validate_settlement_request_policy(
    *,
    swap_ordering: str,
    ordering_choices: frozenset[str],
    protocol_fee_share_bps: int,
    protocol_fee_recipient_pubkey: Optional[PubKey],
) -> None:
    if swap_ordering not in ordering_choices:
        raise ValueError(f"unsupported swap_ordering: {swap_ordering!r}")
    if not is_strict_int(protocol_fee_share_bps) or not (0 <= protocol_fee_share_bps <= 10000):
        raise ValueError("protocol_fee_share_bps must be an int in [0, 10000]")

    policy = canonical_protocol_fee_policy(
        share_bps=protocol_fee_share_bps,
        recipient_pubkey=protocol_fee_recipient_pubkey,
    )
    if protocol_fee_recipient_pubkey != policy.recipient_pubkey:
        raise ValueError(
            "protocol_fee_recipient_pubkey must use canonical lowercase "
            "0x-prefixed wire form"
        )


def validate_swap_tiebreak_seed(seed: bytes | None) -> None:
    if seed is not None and type(seed) is not bytes:
        raise TypeError("swap_tiebreak_seed must be exact bytes or None")
