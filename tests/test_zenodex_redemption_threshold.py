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
        result = exact_payout_per_unit(100_000_000, 50)
        assert result == 99_500_000

    def test_exact_payout_per_unit_zero_fee(self) -> None:
        assert exact_payout_per_unit(100_000_000, 0) == 100_000_000

    def test_redemption_profitable_exact_true(self) -> None:
        assert redemption_profitable_exact(99_000_000, 100_000_000, 50) is True

    def test_redemption_profitable_exact_false(self) -> None:
        assert redemption_profitable_exact(100_000_000, 100_000_000, 50) is False

    def test_redemption_profitable_exact_at_threshold(self) -> None:
        threshold = redemption_profitable_threshold(100_000_000, 50)
        assert redemption_profitable_exact(threshold, 100_000_000, 50) is False

    def test_redemption_profitable_exact_below_threshold(self) -> None:
        threshold = redemption_profitable_threshold(100_000_000, 50)
        assert redemption_profitable_exact(threshold - 1, 100_000_000, 50) is True


# --- Zero Fee Tests ---


class TestZeroFee:
    def test_zero_fee_threshold_equals_oracle(self) -> None:
        assert exact_payout_per_unit(100_000_000, 0) == 100_000_000

    def test_zero_fee_profitable_when_market_below_oracle(self) -> None:
        assert redemption_profitable_exact(99_000_000, 100_000_000, 0) is True

    def test_zero_fee_not_profitable_at_oracle(self) -> None:
        assert redemption_profitable_exact(100_000_000, 100_000_000, 0) is False

    def test_zero_fee_not_profitable_above_oracle(self) -> None:
        assert redemption_profitable_exact(101_000_000, 100_000_000, 0) is False


# --- Fee Monotonicity Tests ---


class TestFeeMonotonicity:
    def test_higher_fee_lowers_threshold(self) -> None:
        t1 = redemption_profitable_threshold(100_000_000, 50)
        t2 = redemption_profitable_threshold(100_000_000, 100)
        assert t2 < t1

    def test_higher_fee_narrows_profit_window(self) -> None:
        market = 99_400_000
        assert redemption_profitable_exact(market, 100_000_000, 50) is True
        assert redemption_profitable_exact(market, 100_000_000, 100) is False

    def test_fee_increase_property(self) -> None:
        for fee1 in range(0, 200, 10):
            for fee2 in range(fee1 + 1, 300, 10):
                t1 = redemption_profitable_threshold(100_000_000, fee1)
                t2 = redemption_profitable_threshold(100_000_000, fee2)
                assert t2 <= t1


# --- Oracle Monotonicity Tests ---


class TestOracleMonotonicity:
    def test_higher_oracle_raises_threshold(self) -> None:
        t1 = redemption_profitable_threshold(100_000_000, 50)
        t2 = redemption_profitable_threshold(110_000_000, 50)
        assert t2 > t1

    def test_higher_oracle_widens_profit_window(self) -> None:
        market = 99_400_000
        assert redemption_profitable_exact(market, 100_000_000, 50) is True
        assert redemption_profitable_exact(market, 110_000_000, 50) is True


# --- Profitable Implies Market Below Oracle ---


class TestProfitableImpliesBelowOracle:
    def test_profitable_market_below_oracle(self) -> None:
        for fee in [1, 50, 100, 500, 1000, 5000, 9999]:
            for market in [50_000_000, 90_000_000, 99_000_000, 99_900_000]:
                if redemption_profitable_exact(market, 100_000_000, fee):
                    assert market < 100_000_000

    def test_market_at_oracle_not_profitable(self) -> None:
        for fee in [1, 50, 100, 5000]:
            assert not redemption_profitable_exact(100_000_000, 100_000_000, fee)

    def test_market_above_oracle_not_profitable(self) -> None:
        for fee in [1, 50, 100, 5000]:
            assert not redemption_profitable_exact(101_000_000, 100_000_000, fee)


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
        assert result.status == "accepted"
        assert result.errors == []

    def test_profitable_envelope(self) -> None:
        env = _base_envelope(market_price_e8=99_000_000, oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.status == "accepted"
        assert result.exact_profitable is True
        assert result.redeemer_profit_e8 > 0

    def test_not_profitable_envelope(self) -> None:
        env = _base_envelope(market_price_e8=100_000_000, oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.status == "accepted"
        assert result.exact_profitable is False

    def test_threshold_value(self) -> None:
        env = _base_envelope(oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.threshold_e8 == 99_500_000

    def test_zero_fee_threshold(self) -> None:
        env = _base_envelope(fee_bps=0)
        result = verify_redemption_envelope(env)
        assert result.threshold_e8 == 100_000_000


# --- Boundary Tests ---


class TestBoundary:
    def test_fee_at_bps_minus_one(self) -> None:
        env = _base_envelope(fee_bps=BPS_SCALE - 1)
        result = verify_redemption_envelope(env)
        assert result.status == "accepted"
        assert result.threshold_e8 == (100_000_000 * 1) // BPS_SCALE

    def test_fee_zero(self) -> None:
        env = _base_envelope(fee_bps=0)
        result = verify_redemption_envelope(env)
        assert result.status == "accepted"

    def test_market_at_threshold_not_profitable(self) -> None:
        threshold = redemption_profitable_threshold(100_000_000, 50)
        env = _base_envelope(market_price_e8=threshold, oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.exact_profitable is False

    def test_market_one_below_threshold_profitable(self) -> None:
        threshold = redemption_profitable_threshold(100_000_000, 50)
        env = _base_envelope(market_price_e8=threshold - 1, oracle_price_e8=100_000_000, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.exact_profitable is True

    def test_large_amount(self) -> None:
        env = _base_envelope(amount_e8=MAX_AMOUNT_E8)
        result = verify_redemption_envelope(env)
        assert result.status == "accepted"


# --- Property Tests ---


class TestPropertyTests:
    def test_threshold_monotonic_in_oracle(self) -> None:
        for oracle1 in [50_000_000, 80_000_000, 100_000_000, 120_000_000]:
            for oracle2 in [oracle1 + 10_000_000, oracle1 + 50_000_000]:
                for fee in [0, 50, 100, 500]:
                    t1 = redemption_profitable_threshold(oracle1, fee)
                    t2 = redemption_profitable_threshold(oracle2, fee)
                    assert t2 >= t1

    def test_threshold_decreasing_in_fee(self) -> None:
        oracle = 100_000_000
        prev = oracle
        for fee in range(0, BPS_SCALE, 100):
            t = redemption_profitable_threshold(oracle, fee)
            assert t <= prev
            prev = t

    def test_profitable_implies_below_oracle(self) -> None:
        for fee in [1, 50, 100, 500, 1000, 5000, 9999]:
            for market in range(1, 200_000_000, 1_000_000):
                if redemption_profitable_exact(market, 100_000_000, fee):
                    assert market < 100_000_000

    def test_zero_fee_profitable_iff_below_oracle(self) -> None:
        for market in range(1, 200_000_000, 1_000_000):
            profitable = redemption_profitable_exact(market, 100_000_000, 0)
            below = market < 100_000_000
            assert profitable == below


# --- CLI Tests ---


class TestNonDivisibleThreshold:
    def test_non_divisible_threshold_boundary(self) -> None:
        oracle = 100_000_001
        fee = 50
        largest = largest_profitable_market_e8(oracle, fee)
        first_np = first_nonprofitable_market_e8(oracle, fee)
        assert largest < first_np
        assert first_np == largest + 1
        assert redemption_profitable_exact(largest, oracle, fee) is True
        assert redemption_profitable_exact(first_np, oracle, fee) is False

    def test_divisible_threshold_boundary(self) -> None:
        oracle = 100_000_000
        fee = 50
        largest = largest_profitable_market_e8(oracle, fee)
        first_np = first_nonprofitable_market_e8(oracle, fee)
        assert largest < first_np
        assert first_np == largest + 1
        assert redemption_profitable_exact(largest, oracle, fee) is True
        assert redemption_profitable_exact(first_np, oracle, fee) is False

    def test_threshold_floor_vs_exact(self) -> None:
        oracle = 100_000_001
        fee = 50
        threshold = redemption_profitable_threshold(oracle, fee)
        largest = largest_profitable_market_e8(oracle, fee)
        first_np = first_nonprofitable_market_e8(oracle, fee)
        assert threshold == (oracle * (BPS_SCALE - fee)) // BPS_SCALE
        assert largest == (oracle * (BPS_SCALE - fee) - 1) // BPS_SCALE
        assert first_np == (oracle * (BPS_SCALE - fee) + BPS_SCALE - 1) // BPS_SCALE

    def test_envelope_reports_largest_profitable(self) -> None:
        env = _base_envelope(oracle_price_e8=100_000_001, fee_bps=50)
        result = verify_redemption_envelope(env)
        assert result.largest_profitable_market_e8 > 0
        assert result.first_nonprofitable_market_e8 > result.largest_profitable_market_e8


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
        largest = largest_profitable_market_e8(100_000_000, 50)
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


class TestCLI:
    def test_sample_outputs_valid_json(self) -> None:
        result = subprocess.run(
            [sys.executable, str(TOOL_PATH), "sample"],
            capture_output=True, text=True,
        )
        assert result.returncode == 0
        data = json.loads(result.stdout)
        assert data["status"] == "accepted"
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
            assert data["status"] == "accepted"
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
