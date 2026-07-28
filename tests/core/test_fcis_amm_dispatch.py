from __future__ import annotations

import pytest

from src.core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from src.core.domain_limits import DEX_POOL_RESERVE_MAX
from src.core.fcis_amm_dispatch import (
    quote_exact_in_for_committed_pool_v1,
    quote_exact_out_for_committed_pool_v1,
    swap_exact_in_for_committed_pool_v1,
    swap_exact_out_for_committed_pool_v1,
)
from src.kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from src.state.pools import (
    CURVE_TAG_CPMM,
    CURVE_TAG_CUBIC_SUM_V1,
    CURVE_TAG_QUARTIC_BLEND_V1,
    CURVE_TAG_QUINTIC_BLEND_V1,
    CURVE_TAG_SUM_BOOST_V1,
    PoolState,
    PoolStatus,
    compute_pool_id,
    normalize_curve_config,
)
from src.state.state_snapshots import snapshot_pool

ASSET0 = "0x" + "01" * 32
ASSET1 = "0x" + "02" * 32

CURVE_CASES = (
    (CURVE_TAG_CPMM, None),
    (CURVE_TAG_CUBIC_SUM_V1, {"p": 3, "q": 5}),
    (CURVE_TAG_SUM_BOOST_V1, {"mu_num": 200, "mu_den": 10_000}),
    (CURVE_TAG_QUARTIC_BLEND_V1, {"c_num": 2, "c_den": 3}),
    (CURVE_TAG_QUINTIC_BLEND_V1, {"c_num": 3, "c_den": 5}),
)
CURVE_GOLDENS = {
    CURVE_TAG_CPMM: ((1_494, (2_001_000, 2_998_506)), (336, (2_000_336, 2_999_500))),
    CURVE_TAG_CUBIC_SUM_V1: ((1_121, (2_001_000, 2_998_879)), (447, (2_000_447, 2_999_500))),
    CURVE_TAG_SUM_BOOST_V1: ((1_223, (2_001_000, 2_998_777)), (410, (2_000_410, 2_999_500))),
    CURVE_TAG_QUARTIC_BLEND_V1: ((1_111, (2_001_000, 2_998_889)), (451, (2_000_451, 2_999_500))),
    CURVE_TAG_QUINTIC_BLEND_V1: ((1_081, (2_001_000, 2_998_919)), (463, (2_000_463, 2_999_500))),
}


def _pool(curve_tag: str, curve_params: object) -> PoolState:
    tag, params = normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)
    return PoolState(
        pool_id=compute_pool_id(
            ASSET0,
            ASSET1,
            30,
            curve_tag=tag,
            curve_params=params,
        ),
        asset0=ASSET0,
        asset1=ASSET1,
        reserve0=2_000_000,
        reserve1=3_000_000,
        fee_bps=30,
        lp_supply=2_400_000,
        status=PoolStatus.ACTIVE,
        created_at=7,
        curve_tag=tag,
        curve_params=params,
    )


@pytest.mark.parametrize(("curve_tag", "curve_params"), CURVE_CASES)
def test_exact_in_dispatch_matches_legacy_for_every_registered_curve(
    curve_tag: str,
    curve_params: object,
) -> None:
    legacy = _pool(curve_tag, curve_params)
    exact = snapshot_pool(legacy)
    expected = swap_exact_in_for_pool(
        legacy,
        reserve_in=legacy.reserve0,
        reserve_out=legacy.reserve1,
        amount_in=1_000,
    )
    assert expected == CURVE_GOLDENS[curve_tag][0]
    assert (
        swap_exact_in_for_committed_pool_v1(
            exact,
            reserve_in=legacy.reserve0,
            reserve_out=legacy.reserve1,
            amount_in=1_000,
        )
        == expected
    )


@pytest.mark.parametrize(("curve_tag", "curve_params"), CURVE_CASES)
def test_exact_out_dispatch_matches_legacy_for_every_registered_curve(
    curve_tag: str,
    curve_params: object,
) -> None:
    legacy = _pool(curve_tag, curve_params)
    exact = snapshot_pool(legacy)
    expected = swap_exact_out_for_pool(
        legacy,
        reserve_in=legacy.reserve0,
        reserve_out=legacy.reserve1,
        amount_out=500,
    )
    assert expected == CURVE_GOLDENS[curve_tag][1]
    assert (
        swap_exact_out_for_committed_pool_v1(
            exact,
            reserve_in=legacy.reserve0,
            reserve_out=legacy.reserve1,
            amount_out=500,
        )
        == expected
    )


@pytest.mark.parametrize(
    ("operation", "kwargs", "message"),
    (
        ("in", {"reserve_in": 0, "reserve_out": 10, "amount_in": 1}, "reserve_in must be >= 1"),
        ("in", {"reserve_in": 10, "reserve_out": 10, "amount_in": 0}, "amount_in must be >= 1"),
        (
            "in",
            {"reserve_in": DEX_POOL_RESERVE_MAX, "reserve_out": 10, "amount_in": 1},
            "swap would exceed reserve_in domain max",
        ),
        (
            "out",
            {"reserve_in": 10, "reserve_out": 10, "amount_out": 10},
            "Cannot drain full reserve",
        ),
    ),
)
def test_exact_dispatch_fails_closed_at_numeric_boundaries(
    operation: str,
    kwargs: dict[str, int],
    message: str,
) -> None:
    exact = snapshot_pool(_pool(CURVE_TAG_CPMM, None))
    call = (
        swap_exact_in_for_committed_pool_v1
        if operation == "in"
        else swap_exact_out_for_committed_pool_v1
    )
    with pytest.raises(ValueError, match=message):
        call(exact, **kwargs)


def test_exact_dispatch_revalidates_hostile_curve_mutation() -> None:
    exact = snapshot_pool(_pool(CURVE_TAG_CUBIC_SUM_V1, {"p": 3, "q": 5}))
    object.__setattr__(exact, "curve_params", '{"q":5,"p":3}')
    with pytest.raises(ValueError):
        swap_exact_in_for_committed_pool_v1(
            exact,
            reserve_in=exact.reserve0,
            reserve_out=exact.reserve1,
            amount_in=1_000,
        )


def test_exact_dispatch_rejects_legacy_pool_objects() -> None:
    legacy = _pool(CURVE_TAG_CPMM, None)
    with pytest.raises(TypeError, match="exact committed pool"):
        swap_exact_in_for_committed_pool_v1(
            legacy,
            reserve_in=legacy.reserve0,
            reserve_out=legacy.reserve1,
            amount_in=1_000,
        )


def test_protocol_fee_quotes_match_the_mixed_oracle_cpmm_leaf() -> None:
    exact = snapshot_pool(_pool(CURVE_TAG_CPMM, None))
    exact_in = quote_exact_in_for_committed_pool_v1(
        exact,
        reserve_in=exact.reserve0,
        reserve_out=exact.reserve1,
        amount_in=1_000,
        protocol_fee_share_bps=2_500,
    )
    mixed_in = quote_cpmm_swap_exact_in(
        reserve_in=exact.reserve0,
        reserve_out=exact.reserve1,
        amount_in=1_000,
        fee_bps=exact.fee_bps,
        protocol_fee_share_bps=2_500,
    )
    assert (
        exact_in.amount_in,
        exact_in.amount_out,
        exact_in.fee_paid,
        exact_in.protocol_fee_paid,
        exact_in.new_reserve_in,
        exact_in.new_reserve_out,
    ) == (
        mixed_in.amount_in,
        mixed_in.amount_out,
        mixed_in.fee_paid,
        mixed_in.protocol_fee_paid,
        mixed_in.reserve_in_after,
        mixed_in.reserve_out_after,
    )

    exact_out = quote_exact_out_for_committed_pool_v1(
        exact,
        reserve_in=exact.reserve0,
        reserve_out=exact.reserve1,
        amount_out=500,
        protocol_fee_share_bps=2_500,
    )
    mixed_out = quote_cpmm_swap_exact_out(
        reserve_in=exact.reserve0,
        reserve_out=exact.reserve1,
        amount_out=500,
        fee_bps=exact.fee_bps,
        protocol_fee_share_bps=2_500,
    )
    assert (
        exact_out.amount_in,
        exact_out.amount_out,
        exact_out.fee_paid,
        exact_out.protocol_fee_paid,
        exact_out.new_reserve_in,
        exact_out.new_reserve_out,
    ) == (
        mixed_out.amount_in,
        mixed_out.amount_out,
        mixed_out.fee_paid,
        mixed_out.protocol_fee_paid,
        mixed_out.reserve_in_after,
        mixed_out.reserve_out_after,
    )


def test_protocol_fee_exact_out_enforces_the_shared_overdelivery_policy() -> None:
    legacy = _pool(CURVE_TAG_CPMM, None)
    legacy.reserve0 = 1
    legacy.reserve1 = 4
    exact = snapshot_pool(legacy)

    with pytest.raises(ValueError, match="overdelivery gap exceeds bps policy"):
        quote_exact_out_for_committed_pool_v1(
            exact,
            reserve_in=1,
            reserve_out=4,
            amount_out=1,
            protocol_fee_share_bps=1_000,
        )


def test_protocol_fee_quote_rejects_non_cpmm_curve() -> None:
    exact = snapshot_pool(_pool(CURVE_TAG_CUBIC_SUM_V1, {"p": 3, "q": 5}))

    with pytest.raises(ValueError, match="protocol fee unsupported for curve"):
        quote_exact_in_for_committed_pool_v1(
            exact,
            reserve_in=exact.reserve0,
            reserve_out=exact.reserve1,
            amount_in=1_000,
            protocol_fee_share_bps=1,
        )
