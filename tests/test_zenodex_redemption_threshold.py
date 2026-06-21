"""Tests for ZenoDEX Redemption Profitability Threshold Verifier."""

from __future__ import annotations

import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

from tools.zenodex_redemption_threshold import (
    E8,
    BPS_SCALE,
    MAX_AMOUNT_E8,
    gross_collateral,
    fee_collateral,
    net_collateral,
    payout_value,
    market_cost,
    redeemer_profit_e8,
    exact_payout_per_unit,
    redemption_profitable_exact,
    redemption_profitable_threshold,
    largest_profitable_market_e8,
    first_nonprofitable_market_e8,
    verify_redemption_envelope,
)

TOOL_PATH = Path(__file__).resolve().parent.parent / "tools" / "zenodex_redemption_threshold.py"


def _base_envelope(
    *,
    amount_e8: int = 1_000_000_000,
    market_price_e8: int = 99_000_000,
    oracle_price_e8: int = 100_000_000,
    fee_bps: int = 50,
) -> dict:
    return {
        "amount_e8": amount_e8,
        "market_price_e8": market_price_e8,
        "oracle_price_e8": oracle_price_e8,
        "fee_bps": fee_bps,
    }


# --- Pure Function Tests ---


class TestPureFunctions:
    def test_gross_collateral_basic(self) -> None:
        assert gross_collateral(1_000_000_000, 100_000_000) == 1_000_000_000

    def test_gross_collateral_zero_oracle(self) -> None:
        assert gross_collateral(1_000_000_000, 0) == 0

    def test_fee_collateral_zero_fee(self) -> None:
        assert fee_collateral(1_000_000_000, 0) == 0

    def test_fee_collateral_basic(self) -> None:
        assert fee_collateral(1_000_000_000, 50) == 5_000_000

    def test_fee_collateral_ceiling(self) -> None:
        result = fee_collateral(1, 1)
        assert result == 1

    def test_net_collateral_basic(self) -> None:
        assert net_collateral(1_000_000_000, 50) == 995_000_000

    def test_payout_value_basic(self) -> None:
        result = payout_value(1_000_000_000, 100_000_000, 50)
        assert result == 995_000_000

    def test_payout_value_zero_oracle(self) -> None:
        assert payout_value(1_000_000_000, 0, 50) == 0

    def test_market_cost_basic(self) -> None:
        assert market_cost(1_000_000_000, 99_000_000) == 990_000_000

    def test_market_cost_ceiling(self) -> None:
        result = market_cost(1, 1)
        assert result == 1

    def test_redeemer_profit_positive(self) -> None:
        profit = redeemer_profit_e8(1_000_000_000, 99_000_000, 100_000_000, 50)
        assert profit > 0

    def test_redeemer_profit_zero_amount(self) -> None:
        assert redeemer_profit_e8(0, 99_000_000, 100_000_000, 50) == 0

    def test_exact_payout_per_unit_basic(self) -> None:
        result = exact_payout_per_unit(50)
        assert result == 99_500_000

    def test_exact_payout_per_unit_zero_fee(self) -> None:
        assert exact_payout_per_unit(0) == E8

    def test_redemption_profitable_exact_true(self) -> None:
        assert redemption_profitable_exact(99_000_000, 50) is True

    def test_redemption_profitable_exact_false(self) -> None:
        assert redemption_profitable_exact(100_000_000, 50) is False

    def test_redemption_profitable_exact_at_threshold(self) -> None:
        threshold = redemption_profitable_threshold(50)
        assert redemption_profitable_exact(threshold, 50) is False

    def test_redemption_profitable_exact_below_threshold(self) -> None:
        threshold = redemption_profitable_threshold(50)
        assert redemption_profitable_exact(threshold - 1, 50) is True


# --- Zero Fee Tests ---


class TestZeroFee:
    def test_zero_fee_threshold_equals_par(self) -> None:
        assert exact_payout_per_unit(0) == E8

    def test_zero_fee_profitable_when_market_below_par(self) -> None:
        assert redemption_profitable_exact(99_000_000, 0) is True

    def test_zero_fee_not_profitable_at_par(self) -> None:
        assert redemption_profitable_exact(E8, 0) is False

    def test_zero_fee_not_profitable_above_par(self) -> None:
        assert redemption_profitable_exact(101_000_000, 0) is False


# --- Fee Monotonicity Tests ---


class TestFeeMonotonicity:
    def test_higher_fee_lowers_threshold(self) -> None:
        t1 = redemption_profitable_threshold(50)
        t2 = redemption_profitable_threshold(100)
        assert t2 < t1

    def test_higher_fee_narrows_profit_window(self) -> None:
        market = 99_400_000
        assert redemption_profitable_exact(market, 50) is True
        assert redemption_profitable_exact(market, 100) is False

    def test_fee_increase_property(self) -> None:
        for fee1 in range(0, 200, 10):
            for fee2 in range(fee1 + 1, 300, 10):
                t1 = redemption_profitable_threshold(fee1)
                t2 = redemption_profitable_threshold(fee2)
                assert t2 <= t1


# --- Oracle Independence Tests ---


class TestOracleIndependence:
    def test_threshold_has_no_oracle_parameter(self) -> None:
        """The threshold function signature does not accept oracle_price.
        This is the API-level confirmation of oracle independence.
        """
        for fee in [0, 50, 100, 500]:
            t = redemption_profitable_threshold(fee)
            assert t == (E8 * (BPS_SCALE - fee)) // BPS_SCALE

    def test_profitability_has_no_oracle_parameter(self) -> None:
        """The exact profitability function signature does not accept oracle_price.
        """
        market = 99_000_000
        fee = 50
        assert redemption_profitable_exact(market, fee) is True

    def test_envelope_threshold_unchanged_across_oracle_values(self) -> None:
        """The threshold reported in the envelope is the same for different oracle prices.
        """
        for oracle in [50_000_000, 80_000_000, 100_000_000, 120_000_000, 200_000_000]:
            env = _base_envelope(oracle_price_e8=oracle, fee_bps=50)
            result = verify_redemption_envelope(env)
            assert result.threshold_e8 == 99_500_000
            assert result.exact_profitable is True


# --- Profitable Implies Market Below Par ---


class TestProfitableImpliesBelowPar:
    def test_profitable_market_below_par(self) -> None:
        for fee in [1, 50, 100, 500, 1000, 5000, 9999]:
            for market in [50_000_000, 90_000_000, 99_000_000, 99_900_000]:
                if redemption_profitable_exact(market, fee):
                    assert market < E8

    def test_market_at_par_not_profitable(self) -> None:
        for fee in [1, 50, 100, 5000]:
            assert not redemption_profitable_exact(E8, fee)

    def test_market_above_par_not_profitable(self) -> None:
        for fee in [1, 50, 100, 5000]:
            assert not redemption_profitable_exact(101_000_000, fee)


# --- Schema Validation Tests ---


class TestSchemaValidation:
    def test_missing_required_field_rejected(self) -> None:
        env = _base_envelope()
        del env["fee_bps"]
        result = verify_redemption_envelope(env)
        assert result.status == "rejected"
        assert any("missing_required_field" in e for e in result.errors)

    def test_amount_must_be_positive(self) -> None:
        env = _base_envelope(amount_e8=0)
        result = verify_redemption_envelope(env)
        assert "amount_must_be_positive" in result.errors

    def test_market_price_must_be_positive(self) -> None:
        env = _base_envelope(market_price_e8=0)
        result = verify_redemption_envelope(env)
        assert "market_price_must_be_positive" in result.errors

    def test_oracle_price_must_be_positive(self) -> None:
        env = _base_envelope(oracle_price_e8=0)
        result = verify_redemption_envelope(env)
        assert "oracle_price_must_be_positive" in result.errors

    def test_fee_bps_must_be_nonneg(self) -> None:
        env = _base_envelope(fee_bps=-1)
        result = verify_redemption_envelope(env)
        assert "fee_bps_must_be_nonneg" in result.errors

    def test_fee_bps_must_be_below_bps(self) -> None:
        env = _base_envelope(fee_bps=BPS_SCALE)
        result = verify_redemption_envelope(env)
        assert "fee_bps_must_be_below_bps" in result.errors

    def test_bool_as_int_rejected(self) -> None:
        env = _base_envelope(amount_e8=True)
        result = verify_redemption_envelope(env)
        assert any("must_be_int" in e for e in result.errors)

    def test_non_dict_direct_call_rejected(self) -> None:
        result = verify_redemption_envelope("not a dict")  # type: ignore
        assert result.status == "rejected"

    def test_amount_exceeds_max(self) -> None:
        env = _base_envelope(amount_e8=MAX_AMOUNT_E8 + 1)
        result = verify_redemption_envelope(env)
        assert "amount_exceeds_max" in result.errors


# --- Envelope Verification Tests ---


class TestEnvelopeVerification:
    def test_valid_envelope_accepted(self) -> None:
        env = _base_envelope()
        result = verify_redemption_envelope(env)
        assert result.status == "accepted_exact_profitable"
        assert result.errors == []

    def test_profitable_envelope(self) -> None:
        env = _base_envelope(market_price_e8=99_000_000, oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.status == "accepted_exact_profitable"
        assert result.exact_profitable is True
        assert result.redeemer_profit_e8 > 0

    def test_not_profitable_envelope(self) -> None:
        env = _base_envelope(market_price_e8=100_000_000, oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.status == "accepted_not_exact_profitable"
        assert result.exact_profitable is False

    def test_threshold_value(self) -> None:
        env = _base_envelope(oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.threshold_e8 == 99_500_000

    def test_zero_fee_threshold(self) -> None:
        env = _base_envelope(fee_bps=0)
        result = verify_redemption_envelope(env)
        assert result.threshold_e8 == E8

    def test_envelope_profit_matches_pure_function(self) -> None:
        env = _base_envelope()
        result = verify_redemption_envelope(env)
        direct = redeemer_profit_e8(
            env["amount_e8"], env["market_price_e8"], env["oracle_price_e8"], env["fee_bps"]
        )
        assert result.redeemer_profit_e8 == direct


# --- Boundary Tests ---


class TestBoundary:
    def test_fee_at_bps_minus_one(self) -> None:
        env = _base_envelope(fee_bps=BPS_SCALE - 1)
        result = verify_redemption_envelope(env)
        assert not result.errors
        assert result.threshold_e8 == (E8 * 1) // BPS_SCALE

    def test_fee_zero(self) -> None:
        env = _base_envelope(fee_bps=0)
        result = verify_redemption_envelope(env)
        assert not result.errors

    def test_market_at_threshold_not_profitable(self) -> None:
        threshold = redemption_profitable_threshold(50)
        env = _base_envelope(market_price_e8=threshold, oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.exact_profitable is False

    def test_market_one_below_threshold_profitable(self) -> None:
        threshold = redemption_profitable_threshold(50)
        env = _base_envelope(market_price_e8=threshold - 1, oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.exact_profitable is True

    def test_large_amount(self) -> None:
        env = _base_envelope(amount_e8=MAX_AMOUNT_E8)
        result = verify_redemption_envelope(env)
        assert not result.errors


# --- Property Tests ---


class TestPropertyTests:
    def test_threshold_decreasing_in_fee(self) -> None:
        prev = E8
        for fee in range(0, BPS_SCALE, 100):
            t = redemption_profitable_threshold(fee)
            assert t <= prev
            prev = t

    def test_profitable_implies_below_par(self) -> None:
        for fee in [1, 50, 100, 500, 1000, 5000, 9999]:
            for market in range(1, 200_000_000, 1_000_000):
                if redemption_profitable_exact(market, fee):
                    assert market < E8

    def test_zero_fee_profitable_iff_below_par(self) -> None:
        for market in range(1, 200_000_000, 1_000_000):
            profitable = redemption_profitable_exact(market, 0)
            below = market < E8
            assert profitable == below

    def test_threshold_independent_of_oracle_property(self) -> None:
        for fee in [0, 50, 100, 500, 1000, 5000, 9999]:
            t = redemption_profitable_threshold(fee)
            assert t == (E8 * (BPS_SCALE - fee)) // BPS_SCALE


# --- Threshold Boundary Tests ---


class TestThresholdBoundary:
    def test_threshold_boundary_profitable_and_not(self) -> None:
        fee = 50
        largest = largest_profitable_market_e8(fee)
        first_np = first_nonprofitable_market_e8(fee)
        assert largest < first_np
        assert first_np == largest + 1
        assert redemption_profitable_exact(largest, fee) is True
        assert redemption_profitable_exact(first_np, fee) is False

    def test_threshold_floor_vs_exact(self) -> None:
        fee = 50
        threshold = redemption_profitable_threshold(fee)
        largest = largest_profitable_market_e8(fee)
        first_np = first_nonprofitable_market_e8(fee)
        assert threshold == (E8 * (BPS_SCALE - fee)) // BPS_SCALE
        assert largest == (E8 * (BPS_SCALE - fee) - 1) // BPS_SCALE
        assert first_np == (E8 * (BPS_SCALE - fee) + BPS_SCALE - 1) // BPS_SCALE

    def test_envelope_reports_largest_profitable(self) -> None:
        env = _base_envelope(oracle_price_e8=100_000_001, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.largest_profitable_market_e8 > 0
        assert result.first_nonprofitable_market_e8 > result.largest_profitable_market_e8


# --- Exact vs Rounded Tests ---


class TestExactVsRounded:
    def test_rounded_profit_positive_when_exact_profitable(self) -> None:
        env = _base_envelope(
            amount_e8=1_000_000_000,
            market_price_e8=99_000_000,
            oracle_price_e8=100_000_000,
            fee_bps=50,
        )
        result = verify_redemption_envelope(env)
        assert result.exact_profitable is True
        assert result.redeemer_profit_e8 > 0

    def test_rounded_profit_may_disagree_near_threshold(self) -> None:
        largest = largest_profitable_market_e8(50)
        env = _base_envelope(
            amount_e8=1_000_000,
            market_price_e8=largest,
            oracle_price_e8=100_000_000,
            fee_bps=50,
        )
        result = verify_redemption_envelope(env)
        assert result.exact_profitable is True

    def test_small_amount_fee_consumes_collateral(self) -> None:
        env = _base_envelope(amount_e8=1, oracle_price_e8=100_000_000, fee_bps=9999)
        result = verify_redemption_envelope(env)
        assert result.gross_collateral_e8 > 0
        assert result.fee_collateral_e8 >= result.gross_collateral_e8

    def test_oracle_above_par_threshold_unchanged(self) -> None:
        env = _base_envelope(oracle_price_e8=150_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.threshold_e8 == 99_500_000

    def test_oracle_below_par_threshold_unchanged(self) -> None:
        env = _base_envelope(oracle_price_e8=50_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.threshold_e8 == 99_500_000

    def test_profit_negative_when_market_above_threshold(self) -> None:
        env = _base_envelope(
            amount_e8=1_000_000_000,
            market_price_e8=100_000_000,
            oracle_price_e8=100_000_000,
            fee_bps=50,
        )
        result = verify_redemption_envelope(env)
        assert result.exact_profitable is False
        assert result.redeemer_profit_e8 < 0


# --- Malformed Input Tests ---


class TestMalformedInputs:
    def test_string_amount_rejected(self) -> None:
        env = _base_envelope(amount_e8="abc")  # type: ignore
        result = verify_redemption_envelope(env)
        assert result.status == "rejected"
        assert any("must_be_int" in e for e in result.errors)

    def test_list_amount_rejected(self) -> None:
        env = _base_envelope(amount_e8=[1, 2])  # type: ignore
        result = verify_redemption_envelope(env)
        assert result.status == "rejected"

    def test_dict_amount_rejected(self) -> None:
        env = _base_envelope(amount_e8={"a": 1})  # type: ignore
        result = verify_redemption_envelope(env)
        assert result.status == "rejected"

    def test_string_fee_rejected(self) -> None:
        env = _base_envelope(fee_bps="50")  # type: ignore
        result = verify_redemption_envelope(env)
        assert result.status == "rejected"

    def test_negative_fee_no_derived_values(self) -> None:
        env = _base_envelope(fee_bps=-1)
        result = verify_redemption_envelope(env)
        assert result.status == "rejected"
        assert result.gross_collateral_e8 == 0
        assert result.redeemer_profit_e8 == 0

    def test_fee_above_bps_no_derived_values(self) -> None:
        env = _base_envelope(fee_bps=BPS_SCALE + 1)
        result = verify_redemption_envelope(env)
        assert result.status == "rejected"
        assert result.gross_collateral_e8 == 0

    def test_status_distinguishes_profitable_from_not(self) -> None:
        env_profitable = _base_envelope(market_price_e8=99_000_000)
        env_not = _base_envelope(market_price_e8=100_000_000)
        r1 = verify_redemption_envelope(env_profitable)
        r2 = verify_redemption_envelope(env_not)
        assert r1.status == "accepted_exact_profitable"
        assert r2.status == "accepted_not_exact_profitable"
        assert r1.exact_profitable is True
        assert r2.exact_profitable is False


# --- Fee Boundary Structure Tests ---


class TestFeeBoundaryStructure:
    """Test threshold boundary structure for various fee values.

    Since E8 = 100_000_000 is divisible by BPS = 10_000, the threshold
    E8 * (BPS - fee) / BPS is always an integer. The largest profitable
    market price is threshold - 1, and the first non-profitable is threshold.
    """

    def test_fee_33_threshold_structure(self) -> None:
        fee = 33
        rhs = E8 * (BPS_SCALE - fee)
        threshold = redemption_profitable_threshold(fee)
        largest = largest_profitable_market_e8(fee)
        first_np = first_nonprofitable_market_e8(fee)
        assert threshold == rhs // BPS_SCALE
        assert largest == (rhs - 1) // BPS_SCALE
        assert first_np == (rhs + BPS_SCALE - 1) // BPS_SCALE
        assert first_np == largest + 1

    def test_fee_33_boundary_profitable(self) -> None:
        fee = 33
        largest = largest_profitable_market_e8(fee)
        assert redemption_profitable_exact(largest, fee) is True

    def test_fee_33_boundary_not_profitable(self) -> None:
        fee = 33
        first_np = first_nonprofitable_market_e8(fee)
        assert redemption_profitable_exact(first_np, fee) is False

    def test_fee_33_threshold_not_profitable(self) -> None:
        fee = 33
        threshold = redemption_profitable_threshold(fee)
        assert redemption_profitable_exact(threshold, fee) is False


# --- Exact vs Rounded Bounded Tests ---


class TestExactVsRoundedBounded:
    def test_large_amount_exact_implies_rounded_profitable(self) -> None:
        """For large amounts (>= 1B E8), exact profitable implies rounded profitable.

        Rounding errors are bounded by O(1) units and become negligible
        relative to the payout for large amounts.
        """
        for fee in [1, 33, 50, 100, 500, 9999]:
            largest = largest_profitable_market_e8(fee)
            for delta in [0, 1, 100, 1000, 10000]:
                market = largest - delta
                if market <= 0:
                    continue
                for amount in [1_000_000_000, 10_000_000_000]:
                    for oracle in [50_000_000, 100_000_000, 150_000_000]:
                        exact = redemption_profitable_exact(market, fee)
                        rounded = redeemer_profit_e8(amount, market, oracle, fee)
                        if exact:
                            assert rounded > 0, (
                                f"exact profitable but rounded loss: "
                                f"fee={fee} market={market} amount={amount} oracle={oracle}"
                            )

    def test_small_amount_rounding_discrepancy_bounded(self) -> None:
        """For small amounts, rounding can cause exact profitable but rounded loss.

        The discrepancy is bounded: rounded_profit >= -2 for amount=1M E8.
        This documents the known rounding gap between exact and rounded arithmetic.
        """
        for fee in [1, 33, 50, 100, 500, 9999]:
            largest = largest_profitable_market_e8(fee)
            for delta in [0, 1, 100, 1000, 10000]:
                market = largest - delta
                if market <= 0:
                    continue
                for oracle in [50_000_000, 100_000_000, 150_000_000]:
                    exact = redemption_profitable_exact(market, fee)
                    rounded = redeemer_profit_e8(1_000_000, market, oracle, fee)
                    if exact:
                        assert rounded >= -2, (
                            f"rounding discrepancy exceeds bound: "
                            f"fee={fee} market={market} oracle={oracle} rounded={rounded}"
                        )

    def test_small_amount_exact_profitable_rounded_loss_counterexample(self) -> None:
        """Document the canonical counterexample: exact profitable but rounded loss.

        amount=100, market=99_499_999, oracle=100_000_000, fee=50.
        Exact: 99_499_999 * 10000 < 100_000_000 * 9950 => profitable.
        Rounded: gross=100, fee=1, payout=99, cost=100, profit=-1.
        """
        exact = redemption_profitable_exact(99_499_999, 50)
        assert exact is True
        rounded = redeemer_profit_e8(100, 99_499_999, 100_000_000, 50)
        assert rounded < 0
        env = _base_envelope(
            amount_e8=100,
            market_price_e8=99_499_999,
            oracle_price_e8=100_000_000,
            fee_bps=50,
        )
        result = verify_redemption_envelope(env)
        assert result.status == "accepted_exact_profitable"
        assert result.exact_profitable is True
        assert result.rounded_profitable is False
        assert result.redeemer_profit_e8 < 0


# --- CLI Tests ---


class TestCLI:
    def test_sample_outputs_valid_json(self) -> None:
        result = subprocess.run(
            [sys.executable, str(TOOL_PATH), "sample"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data["status"] == "accepted_exact_profitable"
        assert data["oracle_price_e8"] == 100_000_000
        assert data["fee_bps"] == 50

    def test_sample_output_to_file(self) -> None:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
            sample = _base_envelope()
            json.dump(sample, f)
            tmp_path = f.name
        try:
            result = subprocess.run(
                [sys.executable, str(TOOL_PATH), "verify", tmp_path],
                capture_output=True, text=True,
            )
            assert result.returncode == 0
            data = json.loads(result.stdout)
            assert data["status"] == "accepted_exact_profitable"
        finally:
            os.unlink(tmp_path)

    def test_verify_accepts_valid_envelope(self) -> None:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
            json.dump(_base_envelope(), f)
            tmp_path = f.name
        try:
            result = subprocess.run(
                [sys.executable, str(TOOL_PATH), "verify", tmp_path],
                capture_output=True, text=True,
            )
            assert result.returncode == 0
        finally:
            os.unlink(tmp_path)

    def test_verify_rejects_bad_envelope(self) -> None:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
            env = _base_envelope(fee_bps=BPS_SCALE)
            json.dump(env, f)
            tmp_path = f.name
        try:
            result = subprocess.run(
                [sys.executable, str(TOOL_PATH), "verify", tmp_path],
                capture_output=True, text=True,
            )
            assert result.returncode == 1
            data = json.loads(result.stdout)
            assert data["status"] == "rejected"
        finally:
            os.unlink(tmp_path)

    def test_verify_nonexistent_file(self) -> None:
        result = subprocess.run(
            [sys.executable, str(TOOL_PATH), "verify", "/nonexistent/file.json"],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "not found" in result.stderr.lower()

    def test_verify_malformed_json(self) -> None:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
            f.write("{bad json")
            tmp_path = f.name
        try:
            result = subprocess.run(
                [sys.executable, str(TOOL_PATH), "verify", tmp_path],
                capture_output=True, text=True,
            )
            assert result.returncode == 1
        finally:
            os.unlink(tmp_path)

    def test_verify_non_object_top_level(self) -> None:
        with tempfile.NamedTemporaryFile(mode="w", suffix=".json", delete=False) as f:
            f.write("[1, 2, 3]")
            tmp_path = f.name
        try:
            result = subprocess.run(
                [sys.executable, str(TOOL_PATH), "verify", tmp_path],
                capture_output=True, text=True,
            )
            assert result.returncode == 1
        finally:
            os.unlink(tmp_path)
