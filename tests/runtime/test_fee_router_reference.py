"""Unit tests for the authoritative Python fee router (src.core.fee_router).

These pin the reference semantics that the Rust shadow must match bit-for-bit.
"""

from __future__ import annotations

import pytest

from src.core.fee_router import (
    BORROW,
    BPS_DENOM,
    DEX,
    MAX_FEE_AMOUNT,
    PERPS,
    REDEMPTION,
    FeeAccumulator,
    FeeSplitTable,
    RouteAccepted,
    RouteRejected,
    canonical_split_table,
    route_fee,
)


def _route(source, amount, table=None, acc=None):
    table = table if table is not None else canonical_split_table(source)
    acc = acc if acc is not None else FeeAccumulator()
    return route_fee(source=source, asset="zUSD", amount=amount, split_table=table, accumulator=acc)


# --- Canonical MVP tables -----------------------------------------------------


def test_canonical_tables_match_mvp_spec():
    assert canonical_split_table(DEX) == FeeSplitTable(6_000, 0, 2_000, 2_000)
    assert canonical_split_table(PERPS) == FeeSplitTable(6_000, 0, 2_000, 2_000)
    assert canonical_split_table(BORROW) == FeeSplitTable(0, 6_000, 2_000, 2_000)
    assert canonical_split_table(REDEMPTION) == FeeSplitTable(0, 6_000, 4_000, 0)


@pytest.mark.parametrize("source", [DEX, PERPS, BORROW, REDEMPTION])
def test_canonical_tables_sum_to_denom(source):
    t = canonical_split_table(source)
    assert t.buyburn_bps + t.stakers_bps + t.reserve_bps + t.hosts_bps == BPS_DENOM


# --- Happy paths --------------------------------------------------------------


def test_dex_exact_split_no_dust():
    res = _route(DEX, 10_000)
    assert isinstance(res, RouteAccepted)
    r = res.receipt
    assert (r.buyburn, r.stakers, r.reserve, r.hosts, r.dust) == (6_000, 0, 2_000, 2_000, 0)
    assert res.accumulator.cum_buyburn == 6_000
    assert res.accumulator.dust == 0


def test_redemption_routes_no_buyburn_no_hosts():
    res = _route(REDEMPTION, 10_000)
    assert isinstance(res, RouteAccepted)
    r = res.receipt
    assert r.buyburn == 0
    assert r.hosts == 0
    assert (r.stakers, r.reserve) == (6_000, 4_000)


def test_borrow_routes_to_stakers_not_buyburn():
    res = _route(BORROW, 10_000)
    assert isinstance(res, RouteAccepted)
    assert res.receipt.buyburn == 0
    assert res.receipt.stakers == 6_000


@pytest.mark.parametrize("source", [DEX, PERPS, BORROW, REDEMPTION])
@pytest.mark.parametrize("amount", [0, 1, 7, 12_347, 999_983, MAX_FEE_AMOUNT])
def test_conservation_invariant(source, amount):
    res = _route(source, amount)
    assert isinstance(res, RouteAccepted)
    r = res.receipt
    # dust_in == 0 here, so the task's literal invariant must hold exactly.
    assert amount == r.buyburn + r.stakers + r.reserve + r.hosts + r.dust
    assert all(v >= 0 for v in (r.buyburn, r.stakers, r.reserve, r.hosts, r.dust))


def test_dust_carry_conserves_across_steps():
    acc = FeeAccumulator()
    routed_out = 0
    total_in = 0
    for amount in (3, 7, 9, 11, 13, 9999):
        res = route_fee(
            source=DEX, asset="zUSD", amount=amount,
            split_table=canonical_split_table(DEX), accumulator=acc,
        )
        assert isinstance(res, RouteAccepted)
        r = res.receipt
        total_in += amount
        routed_out += r.buyburn + r.stakers + r.reserve + r.hosts
        acc = res.accumulator
    # Everything in is either routed to a bucket or still carried as dust.
    assert total_in == routed_out + acc.dust
    assert acc.cum_buyburn + acc.cum_stakers + acc.cum_reserve + acc.cum_hosts == routed_out


# --- Hashing: determinism + sensitivity --------------------------------------


def test_receipt_hash_is_deterministic_and_sensitive():
    a = _route(DEX, 12_347)
    b = _route(DEX, 12_347)
    assert isinstance(a, RouteAccepted) and isinstance(b, RouteAccepted)
    assert a.receipt.receipt_hash() == b.receipt.receipt_hash()
    assert a.receipt.receipt_hash().startswith("0x")
    # A different amount must change the hash.
    c = _route(DEX, 12_348)
    assert isinstance(c, RouteAccepted)
    assert a.receipt.receipt_hash() != c.receipt.receipt_hash()
    # A different domain (same buckets count) must change the hash too.
    d = _route(PERPS, 12_347)
    assert isinstance(d, RouteAccepted)
    assert a.receipt.receipt_hash() != d.receipt.receipt_hash()


def test_accumulator_root_is_deterministic_and_sensitive():
    z0 = FeeAccumulator().state_root()
    z1 = FeeAccumulator().state_root()
    assert z0 == z1
    assert FeeAccumulator(cum_buyburn=1).state_root() != z0
    assert FeeAccumulator(dust=1).state_root() != z0


# --- Rejections (stable codes) ------------------------------------------------


def test_reject_negative_amount():
    res = _route(DEX, -1)
    assert isinstance(res, RouteRejected)
    assert res.reason == "negative_amount"


def test_reject_amount_too_large():
    res = _route(DEX, MAX_FEE_AMOUNT + 1)
    assert isinstance(res, RouteRejected)
    assert res.reason == "amount_too_large"


def test_reject_split_not_summing():
    res = _route(DEX, 1_000, table=FeeSplitTable(6_000, 0, 2_000, 1_999))
    assert isinstance(res, RouteRejected)
    assert res.reason == "split_does_not_sum_to_10000"


def test_reject_component_out_of_range():
    res = _route(DEX, 1_000, table=FeeSplitTable(10_001, 0, 0, 0))
    assert isinstance(res, RouteRejected)
    assert res.reason == "split_component_out_of_range"


def test_reject_unknown_domain():
    res = route_fee(
        source="lending", asset="zUSD", amount=1,
        split_table=FeeSplitTable(2_500, 2_500, 2_500, 2_500), accumulator=FeeAccumulator(),
    )
    assert isinstance(res, RouteRejected)
    assert res.reason == "unknown_domain"


def test_reject_dex_buyburn_below_floor():
    res = _route(DEX, 1_000, table=FeeSplitTable(4_999, 1, 3_000, 2_000))
    assert isinstance(res, RouteRejected)
    assert (res.reason, res.detail) == ("domain_constraint_violated", "buyburn_below_floor")


def test_reject_borrow_stakers_below_floor():
    res = _route(BORROW, 1_000, table=FeeSplitTable(0, 4_999, 3_001, 2_000))
    assert isinstance(res, RouteRejected)
    assert (res.reason, res.detail) == ("domain_constraint_violated", "stakers_below_floor")


def test_reject_redemption_nonzero_buyburn():
    res = _route(REDEMPTION, 1_000, table=FeeSplitTable(1, 5_999, 4_000, 0))
    assert isinstance(res, RouteRejected)
    assert (res.reason, res.detail) == (
        "domain_constraint_violated",
        "redemption_buyburn_must_be_zero",
    )


def test_reject_redemption_nonzero_hosts():
    res = _route(REDEMPTION, 1_000, table=FeeSplitTable(0, 5_999, 4_000, 1))
    assert isinstance(res, RouteRejected)
    assert (res.reason, res.detail) == (
        "domain_constraint_violated",
        "redemption_hosts_must_be_zero",
    )


def test_reject_redemption_reserve_below_floor():
    res = _route(REDEMPTION, 1_000, table=FeeSplitTable(0, 8_001, 1_999, 0))
    assert isinstance(res, RouteRejected)
    assert (res.reason, res.detail) == (
        "domain_constraint_violated",
        "redemption_reserve_below_floor",
    )
