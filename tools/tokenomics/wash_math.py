"""Tokenomics math helpers for bounded mechanism search (internal tooling).

These utilities are intended for *analysis* and test generation, not for
consensus-critical runtime execution.
"""

from __future__ import annotations

from dataclasses import dataclass


_BPS_DENOM = 10_000


def _require_int(name: str, v: int) -> None:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be an int")


def ceil_div_nonneg(n: int, d: int) -> int:
    _require_int("n", n)
    _require_int("d", d)
    if n < 0:
        raise ValueError("n must be non-negative")
    if d <= 0:
        raise ValueError("d must be positive")
    return (n + d - 1) // d


def compute_fee_total_ceil(*, gross_in: int, fee_bps: int) -> int:
    """fee_total = ceil(gross_in * fee_bps / 10_000)."""
    _require_int("gross_in", gross_in)
    _require_int("fee_bps", fee_bps)
    if gross_in < 0:
        raise ValueError("gross_in must be non-negative")
    if not (0 <= fee_bps <= _BPS_DENOM):
        raise ValueError("fee_bps out of range")
    return ceil_div_nonneg(gross_in * fee_bps, _BPS_DENOM)


def compute_protocol_fee_floor(*, fee_total: int, protocol_fee_share_bps: int) -> int:
    """protocol_fee = floor(fee_total * protocol_fee_share_bps / 10_000)."""
    _require_int("fee_total", fee_total)
    _require_int("protocol_fee_share_bps", protocol_fee_share_bps)
    if fee_total < 0:
        raise ValueError("fee_total must be non-negative")
    if not (0 <= protocol_fee_share_bps <= _BPS_DENOM):
        raise ValueError("protocol_fee_share_bps out of range")
    return (fee_total * protocol_fee_share_bps) // _BPS_DENOM


@dataclass(frozen=True)
class MinGrossInForProtocolFeeResult:
    gross_in_min: int
    fee_total: int
    protocol_fee: int


def min_gross_in_for_protocol_fee_floor(
    *,
    target_protocol_fee: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
) -> MinGrossInForProtocolFeeResult:
    """Find the minimal gross_in such that protocol_fee >= target_protocol_fee.

    Uses exact integer inversion of:
      fee_total    = ceil(gross_in * fee_bps / 10_000)
      protocol_fee = floor(fee_total * protocol_fee_share_bps / 10_000)

    If protocol_fee_share_bps == 0:
      - target 0 => gross_in_min = 0 (fee_total=0, protocol_fee=0)
      - target>0 => impossible (raises ValueError)
    """
    _require_int("target_protocol_fee", target_protocol_fee)
    _require_int("fee_bps", fee_bps)
    _require_int("protocol_fee_share_bps", protocol_fee_share_bps)
    if target_protocol_fee < 0:
        raise ValueError("target_protocol_fee must be non-negative")
    if not (0 <= fee_bps <= _BPS_DENOM):
        raise ValueError("fee_bps out of range")
    if not (0 <= protocol_fee_share_bps <= _BPS_DENOM):
        raise ValueError("protocol_fee_share_bps out of range")

    if target_protocol_fee == 0:
        # gross_in=0 yields fee_total=0 => protocol_fee=0
        return MinGrossInForProtocolFeeResult(gross_in_min=0, fee_total=0, protocol_fee=0)

    if fee_bps == 0:
        raise ValueError("impossible: fee_bps=0 cannot yield positive protocol fees")
    if protocol_fee_share_bps == 0:
        raise ValueError("impossible: protocol_fee_share_bps=0 cannot yield positive protocol fees")

    # Smallest fee_total such that floor(fee_total * p / 10_000) >= target.
    fee_total_min = ceil_div_nonneg(target_protocol_fee * _BPS_DENOM, protocol_fee_share_bps)
    if fee_total_min <= 0:
        fee_total_min = 1

    # Smallest gross_in such that ceil(gross_in * fee_bps / 10_000) >= fee_total_min.
    #
    # ceil(x) >= k  <->  x > k-1  <->  gross_in > (k-1)*10_000/fee_bps
    gross_in_min = ((fee_total_min - 1) * _BPS_DENOM) // fee_bps + 1
    if gross_in_min < 0:
        gross_in_min = 0

    fee_total = compute_fee_total_ceil(gross_in=gross_in_min, fee_bps=fee_bps)
    protocol_fee = compute_protocol_fee_floor(fee_total=fee_total, protocol_fee_share_bps=protocol_fee_share_bps)
    if protocol_fee < target_protocol_fee:
        # Defensive: should not happen; indicates a math bug.
        raise RuntimeError("inversion failed to meet target protocol fee")

    return MinGrossInForProtocolFeeResult(gross_in_min=gross_in_min, fee_total=fee_total, protocol_fee=protocol_fee)


def sybil_profit_per_identity_fee_gated(
    *,
    reward_amount: int,
    min_usage_protocol_fee: int,
    fee_bps: int,
    protocol_fee_share_bps: int,
) -> int:
    """Worst-case (max) profit per identity under a fee-gated usage requirement.

    Model:
    - Eligibility requires usage_score >= min_usage_protocol_fee, where usage_score
      is protocol fees paid (quote-equivalent).
    - Attacker can wash trade and recapture LP fees (worst-case: attacker owns 100% LP),
      so irrecoverable cost is protocol_fee only.
    - Attacker chooses the smallest gross_in that meets the protocol-fee threshold.

    Returns: profit = reward_amount - protocol_fee_min (can be negative).
    """
    _require_int("reward_amount", reward_amount)
    _require_int("min_usage_protocol_fee", min_usage_protocol_fee)
    if reward_amount < 0:
        raise ValueError("reward_amount must be non-negative")
    if min_usage_protocol_fee < 0:
        raise ValueError("min_usage_protocol_fee must be non-negative")

    try:
        res = min_gross_in_for_protocol_fee_floor(
            target_protocol_fee=min_usage_protocol_fee,
            fee_bps=fee_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
    except ValueError:
        # If the fee threshold is unattainable under the given fee parameters,
        # the identity cannot claim the reward, so profit is 0 by definition.
        return 0
    return int(reward_amount) - int(res.protocol_fee)
