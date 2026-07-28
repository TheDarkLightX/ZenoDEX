"""Exact committed-pool AMM dispatch with no legacy pool reachability."""

from __future__ import annotations

from dataclasses import dataclass
from typing import final

from ..kernels.python.cpmm_exact_out_policy_v1 import (
    CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
)
from ..kernels.python.cpmm_swap_v8 import (
    compute_fee_total as _compute_fee_total_v8,
)
from ..kernels.python.cpmm_swap_v8 import (
    swap_exact_in as _cpmm_exact_in_v8,
)
from ..kernels.python.cpmm_swap_v8 import (
    swap_exact_out as _cpmm_exact_out_v8,
)
from ..kernels.python.cubic_sum_swap_v1 import swap_exact_in as _cubic_exact_in_v1
from ..kernels.python.cubic_sum_swap_v1 import swap_exact_out as _cubic_exact_out_v1
from ..kernels.python.quartic_blend_swap_v1 import swap_exact_in as _quartic_exact_in_v1
from ..kernels.python.quartic_blend_swap_v1 import swap_exact_out as _quartic_exact_out_v1
from ..kernels.python.quintic_blend_swap_v1 import swap_exact_in as _quintic_exact_in_v1
from ..kernels.python.quintic_blend_swap_v1 import swap_exact_out as _quintic_exact_out_v1
from ..kernels.python.sum_boost_swap_v1 import swap_exact_in as _sum_boost_exact_in_v1
from ..kernels.python.sum_boost_swap_v1 import swap_exact_out as _sum_boost_exact_out_v1
from ..state.fcis_curve_config import (
    CPMMCurveConfigV1,
    CubicSumCurveConfigV1,
    ExactCurveConfigV1,
    QuarticBlendCurveConfigV1,
    QuinticBlendCurveConfigV1,
    SumBoostCurveConfigV1,
    decode_canonical_curve_config_v1,
)
from ..state.state_snapshot_values import CommittedPoolStateV1
from .domain_limits import (
    DEX_POOL_RESERVE_MAX,
    DEX_SWAP_AMOUNT_MAX,
    require_int_range,
)

SwapResultV1 = tuple[int, tuple[int, int]]


@final
@dataclass(frozen=True, slots=True)
class CommittedPoolSwapQuoteV1:
    """One exact swap quote, including protocol-fee reserve semantics."""

    amount_in: int
    amount_out: int
    fee_paid: int
    protocol_fee_paid: int
    new_reserve_in: int
    new_reserve_out: int

    def __post_init__(self) -> None:
        for name, value in (
            ("amount_in", self.amount_in),
            ("amount_out", self.amount_out),
            ("fee_paid", self.fee_paid),
            ("protocol_fee_paid", self.protocol_fee_paid),
            ("new_reserve_in", self.new_reserve_in),
            ("new_reserve_out", self.new_reserve_out),
        ):
            require_int_range(name, value, minimum=0)
        if self.amount_in == 0 or self.amount_out == 0:
            raise ValueError("swap quote amounts must be positive")
        if self.protocol_fee_paid > self.fee_paid:
            raise ValueError("protocol fee cannot exceed total fee")
        if self.new_reserve_in > DEX_POOL_RESERVE_MAX:
            raise ValueError("swap quote reserve_in exceeds domain")
        if self.new_reserve_out > DEX_POOL_RESERVE_MAX:
            raise ValueError("swap quote reserve_out exceeds domain")


def _revalidate_curve_config_v1(config: ExactCurveConfigV1) -> None:
    if type(config) is CPMMCurveConfigV1:
        return
    if type(config) is CubicSumCurveConfigV1:
        config.__post_init__()
        return
    if type(config) is SumBoostCurveConfigV1:
        config.__post_init__()
        return
    if type(config) is QuarticBlendCurveConfigV1:
        config.__post_init__()
        return
    if type(config) is QuinticBlendCurveConfigV1:
        config.__post_init__()
        return
    raise TypeError("config must be an exact closed curve variant")


def _require_swap_inputs_v1(
    *,
    reserve_in: object,
    reserve_out: object,
    amount: object,
    amount_name: str,
    fee_bps: object,
) -> tuple[int, int, int, int]:
    exact_reserve_in = require_int_range(
        "reserve_in",
        reserve_in,
        minimum=1,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    exact_reserve_out = require_int_range(
        "reserve_out",
        reserve_out,
        minimum=1,
        maximum=DEX_POOL_RESERVE_MAX,
    )
    exact_amount = require_int_range(
        amount_name,
        amount,
        minimum=1,
        maximum=DEX_SWAP_AMOUNT_MAX,
    )
    exact_fee_bps = require_int_range("fee_bps", fee_bps, minimum=0, maximum=10_000)
    return exact_reserve_in, exact_reserve_out, exact_amount, exact_fee_bps


def swap_exact_in_curve_v1(
    config: ExactCurveConfigV1,
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
) -> SwapResultV1:
    """Evaluate one exact-in swap from a closed curve value."""

    _revalidate_curve_config_v1(config)
    reserve_in, reserve_out, amount_in, fee_bps = _require_swap_inputs_v1(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount=amount_in,
        amount_name="amount_in",
        fee_bps=fee_bps,
    )
    if reserve_in + amount_in > DEX_POOL_RESERVE_MAX:
        raise ValueError(
            f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
            f"{reserve_in} + {amount_in}"
        )

    if type(config) is CPMMCurveConfigV1:
        result = _cpmm_exact_in_v8(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=fee_bps,
            protocol_fee_share_bps=0,
        )
    elif type(config) is CubicSumCurveConfigV1:
        result = _cubic_exact_in_v1(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            p=config.p,
            q=config.q,
            fee_bps=fee_bps,
        )
    elif type(config) is SumBoostCurveConfigV1:
        result = _sum_boost_exact_in_v1(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            mu_num=config.mu_num,
            mu_den=config.mu_den,
            fee_bps=fee_bps,
        )
    elif type(config) is QuarticBlendCurveConfigV1:
        result = _quartic_exact_in_v1(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            c_num=config.c_num,
            c_den=config.c_den,
            fee_bps=fee_bps,
        )
    elif type(config) is QuinticBlendCurveConfigV1:
        result = _quintic_exact_in_v1(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            c_num=config.c_num,
            c_den=config.c_den,
            fee_bps=fee_bps,
        )
    else:
        raise TypeError("config must be an exact closed curve variant")

    if result.k_after < result.k_before:
        raise ValueError(
            f"Invariant violation: new_k ({result.k_after}) < old_k ({result.k_before})"
        )
    return result.amount_out, (result.new_reserve_in, result.new_reserve_out)


def swap_exact_out_curve_v1(
    config: ExactCurveConfigV1,
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
) -> SwapResultV1:
    """Evaluate one exact-out swap from a closed curve value."""

    _revalidate_curve_config_v1(config)
    reserve_in, reserve_out, amount_out, fee_bps = _require_swap_inputs_v1(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount=amount_out,
        amount_name="amount_out",
        fee_bps=fee_bps,
    )
    if amount_out >= reserve_out:
        raise ValueError(
            f"Cannot drain full reserve: amount_out ({amount_out}) >= reserve_out ({reserve_out})"
        )

    if type(config) is CPMMCurveConfigV1:
        result = _cpmm_exact_out_v8(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            fee_bps=fee_bps,
        )
        gap_bps = ((result.overdelivery_gap * 10_000) + amount_out - 1) // amount_out
        if gap_bps > CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT:
            raise ValueError(
                "overdelivery gap exceeds bps policy: "
                f"gap_bps={gap_bps} > {CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT}"
            )
    elif type(config) is CubicSumCurveConfigV1:
        result = _cubic_exact_out_v1(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            p=config.p,
            q=config.q,
            fee_bps=fee_bps,
        )
    elif type(config) is SumBoostCurveConfigV1:
        result = _sum_boost_exact_out_v1(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            mu_num=config.mu_num,
            mu_den=config.mu_den,
            fee_bps=fee_bps,
        )
    elif type(config) is QuarticBlendCurveConfigV1:
        result = _quartic_exact_out_v1(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            c_num=config.c_num,
            c_den=config.c_den,
            fee_bps=fee_bps,
        )
    elif type(config) is QuinticBlendCurveConfigV1:
        result = _quintic_exact_out_v1(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            c_num=config.c_num,
            c_den=config.c_den,
            fee_bps=fee_bps,
        )
    else:
        raise TypeError("config must be an exact closed curve variant")

    if result.k_after < result.k_before:
        raise ValueError(
            f"Invariant violation: new_k ({result.k_after}) < old_k ({result.k_before})"
        )
    return result.amount_in, (result.new_reserve_in, result.new_reserve_out)


def swap_exact_in_for_committed_pool_v1(
    pool: CommittedPoolStateV1,
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
) -> SwapResultV1:
    """Dispatch exact-in math from one recursively revalidated committed pool."""

    if type(pool) is not CommittedPoolStateV1:
        raise TypeError("pool must be an exact committed pool")
    pool.__post_init__()
    config = decode_canonical_curve_config_v1(pool.curve_tag, pool.curve_params)
    return swap_exact_in_curve_v1(
        config,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=pool.fee_bps,
    )


def swap_exact_out_for_committed_pool_v1(
    pool: CommittedPoolStateV1,
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
) -> SwapResultV1:
    """Dispatch exact-out math from one recursively revalidated committed pool."""

    if type(pool) is not CommittedPoolStateV1:
        raise TypeError("pool must be an exact committed pool")
    pool.__post_init__()
    config = decode_canonical_curve_config_v1(pool.curve_tag, pool.curve_params)
    return swap_exact_out_curve_v1(
        config,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=pool.fee_bps,
    )


def _committed_pool_and_config_v1(
    pool: CommittedPoolStateV1,
) -> ExactCurveConfigV1:
    if type(pool) is not CommittedPoolStateV1:
        raise TypeError("pool must be an exact committed pool")
    pool.__post_init__()
    return decode_canonical_curve_config_v1(pool.curve_tag, pool.curve_params)


def quote_exact_in_for_committed_pool_v1(
    pool: CommittedPoolStateV1,
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    protocol_fee_share_bps: int,
) -> CommittedPoolSwapQuoteV1:
    """Return the exact bounded quote used by strong settlement replay."""

    config = _committed_pool_and_config_v1(pool)
    reserve_in, reserve_out, amount_in, fee_bps = _require_swap_inputs_v1(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount=amount_in,
        amount_name="amount_in",
        fee_bps=pool.fee_bps,
    )
    protocol_fee_share_bps = require_int_range(
        "protocol_fee_share_bps",
        protocol_fee_share_bps,
        minimum=0,
        maximum=10_000,
    )
    if reserve_in + amount_in > DEX_POOL_RESERVE_MAX:
        raise ValueError(
            f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
            f"{reserve_in} + {amount_in}"
        )
    if protocol_fee_share_bps:
        if type(config) is not CPMMCurveConfigV1:
            raise ValueError("protocol fee unsupported for curve")
        result = _cpmm_exact_in_v8(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=fee_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
        if result.k_after < result.k_before:
            raise ValueError(
                f"Invariant violation: new_k ({result.k_after}) < old_k ({result.k_before})"
            )
        return CommittedPoolSwapQuoteV1(
            amount_in=amount_in,
            amount_out=result.amount_out,
            fee_paid=result.fee_total,
            protocol_fee_paid=result.protocol_fee,
            new_reserve_in=result.new_reserve_in,
            new_reserve_out=result.new_reserve_out,
        )
    amount_out, (new_reserve_in, new_reserve_out) = swap_exact_in_curve_v1(
        config,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )
    return CommittedPoolSwapQuoteV1(
        amount_in=amount_in,
        amount_out=amount_out,
        fee_paid=_compute_fee_total_v8(gross_in=amount_in, fee_bps=fee_bps),
        protocol_fee_paid=0,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )


def quote_exact_out_for_committed_pool_v1(
    pool: CommittedPoolStateV1,
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    protocol_fee_share_bps: int,
) -> CommittedPoolSwapQuoteV1:
    """Return one exact-out quote with the protocol overdelivery policy."""

    config = _committed_pool_and_config_v1(pool)
    reserve_in, reserve_out, amount_out, fee_bps = _require_swap_inputs_v1(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount=amount_out,
        amount_name="amount_out",
        fee_bps=pool.fee_bps,
    )
    protocol_fee_share_bps = require_int_range(
        "protocol_fee_share_bps",
        protocol_fee_share_bps,
        minimum=0,
        maximum=10_000,
    )
    if amount_out >= reserve_out:
        raise ValueError(
            f"Cannot drain full reserve: amount_out ({amount_out}) >= reserve_out ({reserve_out})"
        )
    if protocol_fee_share_bps:
        if type(config) is not CPMMCurveConfigV1:
            raise ValueError("protocol fee unsupported for curve")
        result = _cpmm_exact_out_v8(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            fee_bps=fee_bps,
            protocol_fee_share_bps=protocol_fee_share_bps,
        )
        if result.new_reserve_in > DEX_POOL_RESERVE_MAX:
            raise ValueError(
                f"swap would exceed reserve_in domain max {DEX_POOL_RESERVE_MAX}: "
                f"{reserve_in} + {result.amount_in}"
            )
        gap_bps = ((result.overdelivery_gap * 10_000) + amount_out - 1) // amount_out
        if gap_bps > CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT:
            raise ValueError(
                "overdelivery gap exceeds bps policy: "
                f"gap_bps={gap_bps} > {CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT}"
            )
        if result.k_after < result.k_before:
            raise ValueError(
                f"Invariant violation: new_k ({result.k_after}) < old_k ({result.k_before})"
            )
        return CommittedPoolSwapQuoteV1(
            amount_in=result.amount_in,
            amount_out=amount_out,
            fee_paid=result.fee_total,
            protocol_fee_paid=result.protocol_fee,
            new_reserve_in=result.new_reserve_in,
            new_reserve_out=result.new_reserve_out,
        )
    amount_in, (new_reserve_in, new_reserve_out) = swap_exact_out_curve_v1(
        config,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
    )
    return CommittedPoolSwapQuoteV1(
        amount_in=amount_in,
        amount_out=amount_out,
        fee_paid=_compute_fee_total_v8(gross_in=amount_in, fee_bps=fee_bps),
        protocol_fee_paid=0,
        new_reserve_in=new_reserve_in,
        new_reserve_out=new_reserve_out,
    )
