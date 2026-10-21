"""
Curve dispatch for pool swap execution/quoting.

DEX core uses PoolState.curve_tag/curve_params to select the correct verified
swap kernel (CPMM vs cubic-sum v1, etc).
"""

from __future__ import annotations

from typing import Tuple

from ..kernels.python.settlement_swap_runtime_v1 import (
    CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
)
from ..state.balances import Amount
from ..state.pools import (
    CURVE_TAG_CPMM,
    CURVE_TAG_CUBIC_SUM_V1,
    CURVE_TAG_QUARTIC_BLEND_V1,
    CURVE_TAG_QUINTIC_BLEND_V1,
    CURVE_TAG_SUM_BOOST_V1,
    PoolState,
    parse_cubic_sum_params,
    parse_quartic_blend_params,
    parse_quintic_blend_params,
    parse_sum_boost_params,
)
from ..state.state_snapshot_values import CommittedPoolStateV1
from . import cpmm, cubic_sum_amm, quartic_blend_amm, quintic_blend_amm, sum_boost_amm


def _swap_exact_in_for_pool_value_v1(
    pool: PoolState | CommittedPoolStateV1,
    *,
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """Dispatch exact-in math from the closed legacy/exact pool union."""

    if pool.curve_tag == CURVE_TAG_CPMM:
        return cpmm.swap_exact_in(reserve_in, reserve_out, amount_in, pool.fee_bps)
    if pool.curve_tag == CURVE_TAG_CUBIC_SUM_V1:
        p, q = parse_cubic_sum_params(pool.curve_params)
        return cubic_sum_amm.swap_exact_in_cubic_sum(
            reserve_in, reserve_out, amount_in, p=p, q=q, fee_bps=pool.fee_bps
        )
    if pool.curve_tag == CURVE_TAG_SUM_BOOST_V1:
        mu_num, mu_den = parse_sum_boost_params(pool.curve_params)
        return sum_boost_amm.swap_exact_in_sum_boost(
            reserve_in,
            reserve_out,
            amount_in,
            mu_num=mu_num,
            mu_den=mu_den,
            fee_bps=pool.fee_bps,
        )
    if pool.curve_tag == CURVE_TAG_QUARTIC_BLEND_V1:
        c_num, c_den = parse_quartic_blend_params(pool.curve_params)
        return quartic_blend_amm.swap_exact_in_quartic_blend(
            reserve_in,
            reserve_out,
            amount_in,
            c_num=c_num,
            c_den=c_den,
            fee_bps=pool.fee_bps,
        )
    if pool.curve_tag == CURVE_TAG_QUINTIC_BLEND_V1:
        c_num, c_den = parse_quintic_blend_params(pool.curve_params)
        return quintic_blend_amm.swap_exact_in_quintic_blend(
            reserve_in,
            reserve_out,
            amount_in,
            c_num=c_num,
            c_den=c_den,
            fee_bps=pool.fee_bps,
        )
    raise ValueError(f"unsupported pool curve_tag: {pool.curve_tag!r}")


def swap_exact_in_for_pool(
    pool: PoolState, *, reserve_in: Amount, reserve_out: Amount, amount_in: Amount
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    return _swap_exact_in_for_pool_value_v1(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
    )


def swap_exact_in_for_committed_pool_v1(
    pool: CommittedPoolStateV1,
    *,
    reserve_in: Amount,
    reserve_out: Amount,
    amount_in: Amount,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    if type(pool) is not CommittedPoolStateV1:
        raise TypeError("pool must be an exact committed pool")
    return _swap_exact_in_for_pool_value_v1(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
    )


def _swap_exact_out_for_pool_value_v1(
    pool: PoolState | CommittedPoolStateV1,
    *,
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    """Dispatch exact-out math from the closed legacy/exact pool union."""

    if pool.curve_tag == CURVE_TAG_CPMM:
        return cpmm.swap_exact_out(
            reserve_in,
            reserve_out,
            amount_out,
            pool.fee_bps,
            max_overdelivery_gap_bps=CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
        )
    if pool.curve_tag == CURVE_TAG_CUBIC_SUM_V1:
        p, q = parse_cubic_sum_params(pool.curve_params)
        return cubic_sum_amm.swap_exact_out_cubic_sum(
            reserve_in, reserve_out, amount_out, p=p, q=q, fee_bps=pool.fee_bps
        )
    if pool.curve_tag == CURVE_TAG_SUM_BOOST_V1:
        mu_num, mu_den = parse_sum_boost_params(pool.curve_params)
        return sum_boost_amm.swap_exact_out_sum_boost(
            reserve_in,
            reserve_out,
            amount_out,
            mu_num=mu_num,
            mu_den=mu_den,
            fee_bps=pool.fee_bps,
        )
    if pool.curve_tag == CURVE_TAG_QUARTIC_BLEND_V1:
        c_num, c_den = parse_quartic_blend_params(pool.curve_params)
        return quartic_blend_amm.swap_exact_out_quartic_blend(
            reserve_in,
            reserve_out,
            amount_out,
            c_num=c_num,
            c_den=c_den,
            fee_bps=pool.fee_bps,
        )
    if pool.curve_tag == CURVE_TAG_QUINTIC_BLEND_V1:
        c_num, c_den = parse_quintic_blend_params(pool.curve_params)
        return quintic_blend_amm.swap_exact_out_quintic_blend(
            reserve_in,
            reserve_out,
            amount_out,
            c_num=c_num,
            c_den=c_den,
            fee_bps=pool.fee_bps,
        )
    raise ValueError(f"unsupported pool curve_tag: {pool.curve_tag!r}")


def swap_exact_out_for_pool(
    pool: PoolState, *, reserve_in: Amount, reserve_out: Amount, amount_out: Amount
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    return _swap_exact_out_for_pool_value_v1(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
    )


def swap_exact_out_for_committed_pool_v1(
    pool: CommittedPoolStateV1,
    *,
    reserve_in: Amount,
    reserve_out: Amount,
    amount_out: Amount,
) -> Tuple[Amount, Tuple[Amount, Amount]]:
    if type(pool) is not CommittedPoolStateV1:
        raise TypeError("pool must be an exact committed pool")
    return _swap_exact_out_for_pool_value_v1(
        pool,
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
    )
