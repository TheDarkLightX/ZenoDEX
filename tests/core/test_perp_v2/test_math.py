"""Tests for src/core/perp_v2/math.py — pure arithmetic functions."""

from src.core.perp_v2.math import (
    PRICE_SCALE,
    abs_val,
    funding_payment,
    funding_same_sign,
    init_margin_req,
    is_liquidatable,
    is_oracle_fresh,
    liq_penalty,
    liq_penalty_capped,
    maint_margin_req,
    margin_requirement,
    notional_quote,
    oracle_move_violated,
    pnl_magnitude,
    pnl_quote,
    pnl_same_sign,
    settle_price,
)


# ---------------------------------------------------------------------------
# abs_val
# ---------------------------------------------------------------------------

class TestAbsVal:
    def test_positive(self):
        assert abs_val(42) == 42

    def test_negative(self):
        assert abs_val(-42) == 42

    def test_zero(self):
        assert abs_val(0) == 0


# ---------------------------------------------------------------------------
# Oracle freshness
# ---------------------------------------------------------------------------

class TestOracleFresh:
    def test_fresh(self):
        assert is_oracle_fresh(10, 5, 100, True) is True

    def test_stale(self):
        assert is_oracle_fresh(110, 5, 100, True) is False

    def test_not_seen(self):
        assert is_oracle_fresh(0, 0, 100, False) is False

    def test_exact_boundary(self):
        assert is_oracle_fresh(105, 5, 100, True) is True

    def test_one_past_boundary(self):
        assert is_oracle_fresh(106, 5, 100, True) is False


# ---------------------------------------------------------------------------
# Oracle move
# ---------------------------------------------------------------------------

class TestOracleMove:
    def test_no_violation(self):
        # 5% move on price 1e8 → diff=5e6, threshold=5e6 → not violated
        assert oracle_move_violated(105_000_000, 100_000_000, 500, True) is False

    def test_violation(self):
        # 6% move → diff=6e6, threshold=5e6 → violated
        assert oracle_move_violated(106_000_000, 100_000_000, 500, True) is True

    def test_not_seen(self):
        assert oracle_move_violated(200_000_000, 100_000_000, 500, False) is False

    def test_downward_violation(self):
        assert oracle_move_violated(93_000_000, 100_000_000, 500, True) is True


# ---------------------------------------------------------------------------
# Settle price
# ---------------------------------------------------------------------------

class TestSettlePrice:
    def test_no_clamp(self):
        sp = settle_price(105_000_000, 100_000_000, 500, True)
        assert sp == 105_000_000

    def test_clamp_up(self):
        sp = settle_price(200_000_000, 100_000_000, 500, True)
        # max_delta = 100_000_000 * 500 // 10000 = 5_000_000
        assert sp == 105_000_000

    def test_clamp_down(self):
        sp = settle_price(50_000_000, 100_000_000, 500, True)
        assert sp == 95_000_000

    def test_oracle_not_seen(self):
        # No clamping when oracle not seen
        sp = settle_price(200_000_000, 100_000_000, 500, False)
        assert sp == 200_000_000


# ---------------------------------------------------------------------------
# Notional + margin
# ---------------------------------------------------------------------------

class TestNotional:
    def test_long(self):
        # 100 base * 1e8 price / 1e8 = 100
        assert notional_quote(100, PRICE_SCALE) == 100

    def test_short(self):
        assert notional_quote(-100, PRICE_SCALE) == 100

    def test_zero(self):
        assert notional_quote(0, PRICE_SCALE) == 0


class TestMarginRequirement:
    def test_basic(self):
        # notional=1000, margin_bps=1000 (10%) → 100
        assert margin_requirement(1000, 1000) == 100

    def test_zero(self):
        assert margin_requirement(0, 1000) == 0


class TestMaintMarginReq:
    def test_basic(self):
        # 100 base * 2e8 price / 1e8 = 200 notional
        # (500+100)/10000 * 200 = 12
        result = maint_margin_req(100, 200_000_000, 500, 100)
        assert result == 12


class TestInitMarginReq:
    def test_basic(self):
        # 100 base * 2e8 price / 1e8 = 200 notional
        # 1000/10000 * 200 = 20
        result = init_margin_req(100, 200_000_000, 1000)
        assert result == 20


# ---------------------------------------------------------------------------
# PnL
# ---------------------------------------------------------------------------

class TestPnl:
    def test_long_profit(self):
        # Long 100 base, price goes from 1e8 to 1.1e8
        pnl = pnl_quote(100, 110_000_000, 100_000_000)
        assert pnl == 10  # 100 * 10_000_000 / 1e8 = 10

    def test_long_loss(self):
        pnl = pnl_quote(100, 90_000_000, 100_000_000)
        assert pnl == -10

    def test_short_profit(self):
        pnl = pnl_quote(-100, 90_000_000, 100_000_000)
        assert pnl == 10

    def test_short_loss(self):
        pnl = pnl_quote(-100, 110_000_000, 100_000_000)
        assert pnl == -10

    def test_zero_position(self):
        assert pnl_quote(0, 110_000_000, 100_000_000) == 0

    def test_same_price(self):
        assert pnl_quote(100, 100_000_000, 100_000_000) == 0


class TestPnlMagnitude:
    def test_basic(self):
        mag = pnl_magnitude(100, 110_000_000, 100_000_000)
        assert mag == 10


class TestPnlSameSign:
    def test_long_up(self):
        assert pnl_same_sign(100, 110_000_000, 100_000_000) is True

    def test_long_down(self):
        assert pnl_same_sign(100, 90_000_000, 100_000_000) is False

    def test_short_down(self):
        assert pnl_same_sign(-100, 90_000_000, 100_000_000) is True

    def test_short_up(self):
        assert pnl_same_sign(-100, 110_000_000, 100_000_000) is False


# ---------------------------------------------------------------------------
# Liquidation
# ---------------------------------------------------------------------------

class TestLiqPenalty:
    def test_above_threshold(self):
        # notional = 100 * 1e8 / 1e8 = 100; penalty = 100 * 50 / 10000 = 0
        # Need larger values for non-zero penalty
        penalty = liq_penalty(100_000, 100_000_000, 50, 100)
        # notional = 100000 * 1e8 / 1e8 = 100000
        # penalty = 100000 * 50 / 10000 = 500
        assert penalty == 500

    def test_below_threshold(self):
        penalty = liq_penalty(1, 100_000_000, 50, 100_000_000)
        # notional = 1 < 100_000_000 threshold → 0
        assert penalty == 0


class TestLiqPenaltyCapped:
    def test_capped_at_collateral(self):
        capped = liq_penalty_capped(10, 100_000, 100_000_000, 50, 100)
        assert capped == 10  # collateral = 10 < raw penalty = 500

    def test_not_capped(self):
        capped = liq_penalty_capped(1000, 100_000, 100_000_000, 50, 100)
        assert capped == 500  # collateral = 1000 > raw penalty = 500


class TestIsLiquidatable:
    def test_undercollateralized(self):
        # maint_req = maint_margin_req(100, 1e8, 500, 100)
        # = notional(100, 1e8) * 600 / 10000 = 100 * 600 / 10000 = 6
        assert is_liquidatable(100, 5, 100_000_000, 500, 100) is True

    def test_well_collateralized(self):
        assert is_liquidatable(100, 100, 100_000_000, 500, 100) is False

    def test_flat(self):
        assert is_liquidatable(0, 0, 100_000_000, 500, 100) is False


# ---------------------------------------------------------------------------
# Funding
# ---------------------------------------------------------------------------

class TestFunding:
    def test_long_positive_rate(self):
        # Same sign → payer: magnitude
        # notional = 100 * 1e8 / 1e8 = 100, magnitude = 100 * 50 / 10000 = 0
        # Need larger values
        fp = funding_payment(1000, 100_000_000, 100)
        # notional = 1000, mag = 1000 * 100 / 10000 = 10
        assert fp == 10

    def test_long_negative_rate(self):
        fp = funding_payment(1000, 100_000_000, -100)
        assert fp == -10

    def test_short_positive_rate(self):
        fp = funding_payment(-1000, 100_000_000, 100)
        assert fp == -10

    def test_short_negative_rate(self):
        fp = funding_payment(-1000, 100_000_000, -100)
        assert fp == 10

    def test_zero_position(self):
        fp = funding_payment(0, 100_000_000, 100)
        assert fp == 0

    def test_zero_rate(self):
        fp = funding_payment(1000, 100_000_000, 0)
        assert fp == 0


class TestFundingSameSign:
    def test_both_positive(self):
        assert funding_same_sign(100, 50) is True

    def test_both_negative(self):
        assert funding_same_sign(-100, -50) is True

    def test_mixed(self):
        assert funding_same_sign(100, -50) is False

    def test_zero_position(self):
        # 0 >= 0 is True; 50 >= 0 is True → same sign
        assert funding_same_sign(0, 50) is True
