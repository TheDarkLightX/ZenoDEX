#!/usr/bin/env python3
"""Tests for ZenoDEX Liquidation Cascade Termination Verifier.

Covers:
- Schema validation (missing fields, bad types, out of range)
- Position decrease theorem (fraction >= 1, pos >= BPS)
- Cascade termination bound (remaining <= pos - 1)
- Post-liquidation safety (guard condition)
- Funded liquidation condition
- Boundary cases (fraction=0, fraction=BPS, pos=BPS, pos=0)
- CLI subprocess tests
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_liquidation_cascade import (
    BPS_SCALE,
    capped_penalty,
    closed_portion,
    funded_liquidation_ok,
    is_liquidatable,
    liq_penalty,
    maint_margin_req,
    remaining_position,
    sample_envelope,
    verify_liquidation_cascade_envelope,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
TOOL = REPO_ROOT / "tools" / "zenodex_liquidation_cascade.py"


def _base_envelope(**overrides: object) -> dict[str, object]:
    env = sample_envelope()
    env.update(overrides)
    return env


def _write_temp_env(tmp_path: Path, env: dict[str, object]) -> Path:
    p = tmp_path / "envelope.json"
    p.write_text(json.dumps(env))
    return p


# --- Unit tests for pure functions ---


class TestPureFunctions:
    def test_closed_portion_half(self) -> None:
        assert closed_portion(10_000, 5_000) == 5_000

    def test_closed_portion_full(self) -> None:
        assert closed_portion(10_000, 10_000) == 10_000

    def test_closed_portion_zero(self) -> None:
        assert closed_portion(10_000, 0) == 0

    def test_closed_portion_small_fraction(self) -> None:
        assert closed_portion(10_000, 1) == 1

    def test_remaining_position_half(self) -> None:
        assert remaining_position(10_000, 5_000) == 5_000

    def test_remaining_position_full(self) -> None:
        assert remaining_position(10_000, 10_000) == 0

    def test_maint_margin_req(self) -> None:
        assert maint_margin_req(100, 1_000_000, 500, 100) == 100 * 1_000_000 * 600 // 10_000

    def test_liq_penalty(self) -> None:
        assert liq_penalty(5_000, 1_000_000, 200) == 5_000 * 1_000_000 * 200 // 10_000

    def test_capped_penalty_below_collateral(self) -> None:
        assert capped_penalty(1_000_000_000, 5_000, 1_000_000, 200) == liq_penalty(5_000, 1_000_000, 200)

    def test_capped_penalty_above_collateral(self) -> None:
        assert capped_penalty(1_000, 5_000, 1_000_000, 200) == 1_000

    def test_is_liquidatable_true(self) -> None:
        assert is_liquidatable(10_000, 100, 1_000_000, 500, 100) is True

    def test_is_liquidatable_false_safe(self) -> None:
        mreq = maint_margin_req(10_000, 1_000_000, 500, 100)
        assert is_liquidatable(10_000, mreq, 1_000_000, 500, 100) is False

    def test_is_liquidatable_false_zero_pos(self) -> None:
        assert is_liquidatable(0, 100, 1_000_000, 500, 100) is False

    def test_funded_liquidation_ok_true(self) -> None:
        assert funded_liquidation_ok(200, 300, 500, 100) is True

    def test_funded_liquidation_ok_false(self) -> None:
        assert funded_liquidation_ok(2_000, 300, 500, 100) is False


# --- Schema Validation ---


class TestSchemaValidation:
    def test_missing_required_field_rejected(self) -> None:
        env = _base_envelope()
        del env["position_base"]
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert "missing_required_field:position_base" in result.errors

    def test_position_must_be_nonneg(self) -> None:
        env = _base_envelope(position_base=-1)
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("position_base" in e for e in result.errors)

    def test_price_must_be_positive(self) -> None:
        env = _base_envelope(index_price_e8=0)
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("index_price_e8" in e for e in result.errors)

    def test_bool_as_int_rejected(self) -> None:
        env = _base_envelope(position_base=True)
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("position_base" in e for e in result.errors)

    def test_non_dict_direct_call_rejected(self) -> None:
        result = verify_liquidation_cascade_envelope([1, 2, 3])  # type: ignore[arg-type]
        assert result.status == "rejected"
        assert "top_level_must_be_object" in result.errors

    def test_bad_position_id_rejected(self) -> None:
        env = _base_envelope(position_id="bad id with spaces")
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("position_id" in e for e in result.errors)


# --- Position Decrease Theorem ---


class TestPositionDecrease:
    def test_position_decreases_with_fraction(self) -> None:
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=5_000)
        result = verify_liquidation_cascade_envelope(env)
        assert result.position_decreases is True
        assert result.remaining_position < result.position_base

    def test_full_close_reaches_zero(self) -> None:
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=10_000)
        result = verify_liquidation_cascade_envelope(env)
        assert result.remaining_position == 0
        assert result.position_decreases is True

    def test_small_fraction_large_position(self) -> None:
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=1)
        result = verify_liquidation_cascade_envelope(env)
        assert result.closed_portion == 1
        assert result.remaining_position == 9_999
        assert result.position_decreases is True

    def test_zero_fraction_no_decrease(self) -> None:
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=0)
        result = verify_liquidation_cascade_envelope(env)
        assert result.remaining_position == 10_000
        assert result.position_decreases is False
        assert "fraction_must_be_at_least_1_bps" in result.errors

    def test_position_below_bps_no_termination(self) -> None:
        env = _base_envelope(position_base=5_000, liquidation_fraction_bps=1)
        result = verify_liquidation_cascade_envelope(env)
        assert result.position_decreases is False
        assert "position_must_be_at_least_bps_for_termination" in result.errors


# --- Cascade Termination Bound ---


class TestCascadeTermination:
    def test_cascade_terminates_bounded(self) -> None:
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=5_000)
        result = verify_liquidation_cascade_envelope(env)
        assert result.cascade_terminates is True
        assert result.remaining_position <= result.position_base - 1

    def test_max_cascade_steps(self) -> None:
        env = _base_envelope(position_base=10_000)
        result = verify_liquidation_cascade_envelope(env)
        assert result.max_cascade_steps == 10_000

    def test_zero_position_zero_steps(self) -> None:
        env = _base_envelope(position_base=0)
        result = verify_liquidation_cascade_envelope(env)
        assert result.max_cascade_steps == 0
        assert result.cascade_terminates is True


# --- Post-Liquidation Safety ---


class TestPostLiquidationSafety:
    def test_post_safe_when_guard_satisfied(self) -> None:
        env = _base_envelope(
            position_base=10_000,
            collateral_quote=100_000_000_000,
            liquidation_fraction_bps=5_000,
        )
        result = verify_liquidation_cascade_envelope(env)
        assert result.post_liquidation_safe is True

    def test_post_unsafe_detected(self) -> None:
        env = _base_envelope(
            position_base=10_000,
            collateral_quote=1,
            liquidation_fraction_bps=5_000,
            penalty_bps=200,
        )
        result = verify_liquidation_cascade_envelope(env)
        assert "post_liquidation_unsafe" in result.errors


# --- Funded Liquidation ---


class TestFundedLiquidation:
    def test_funded_ok_accepted(self) -> None:
        env = _base_envelope(
            penalty_bps=200,
            max_oracle_move_bps=300,
            maint_bps=500,
            depeg_buffer_bps=100,
        )
        result = verify_liquidation_cascade_envelope(env)
        assert result.funded_liquidation_ok is True
        assert "funded_liquidation_violated" not in result.errors

    def test_funded_violated_detected(self) -> None:
        env = _base_envelope(
            penalty_bps=2_000,
            max_oracle_move_bps=300,
            maint_bps=500,
            depeg_buffer_bps=100,
        )
        result = verify_liquidation_cascade_envelope(env)
        assert result.funded_liquidation_ok is False
        assert "funded_liquidation_violated" in result.errors

    def test_penalty_exceeds_eff_maint(self) -> None:
        env = _base_envelope(
            penalty_bps=700,
            maint_bps=500,
            depeg_buffer_bps=100,
        )
        result = verify_liquidation_cascade_envelope(env)
        assert "penalty_exceeds_eff_maint_margin" in result.errors

    def test_oracle_move_exceeds_eff_maint(self) -> None:
        env = _base_envelope(
            max_oracle_move_bps=700,
            maint_bps=500,
            depeg_buffer_bps=100,
        )
        result = verify_liquidation_cascade_envelope(env)
        assert "oracle_move_exceeds_eff_maint" in result.errors

    def test_raw_penalty_exceeds_collateral(self) -> None:
        env = _base_envelope(
            position_base=10_000,
            collateral_quote=1_000,
            liquidation_fraction_bps=5_000,
            penalty_bps=200,
        )
        result = verify_liquidation_cascade_envelope(env)
        assert result.raw_penalty > result.collateral_quote
        assert "raw_penalty_exceeds_collateral" in result.errors


# --- Boundary Cases ---


class TestBoundary:
    def test_fraction_equals_bps(self) -> None:
        env = _base_envelope(liquidation_fraction_bps=10_000)
        result = verify_liquidation_cascade_envelope(env)
        assert result.remaining_position == 0

    def test_position_equals_bps(self) -> None:
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=1)
        result = verify_liquidation_cascade_envelope(env)
        assert result.position_decreases is True
        assert result.remaining_position == 9_999

    def test_position_zero_accepted(self) -> None:
        env = _base_envelope(position_base=0)
        result = verify_liquidation_cascade_envelope(env)
        assert result.is_liquidatable is False
        assert result.cascade_terminates is True

    def test_max_position_accepted(self) -> None:
        env = _base_envelope(position_base=10**18)
        result = verify_liquidation_cascade_envelope(env)
        assert result.position_base == 10**18

    def test_position_above_max_rejected(self) -> None:
        env = _base_envelope(position_base=10**18 + 1)
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("position_base" in e for e in result.errors)


# --- CLI Subprocess Tests ---


class TestCLI:
    def test_sample_outputs_valid_json(self) -> None:
        proc = subprocess.run(
            [sys.executable, str(TOOL), "sample"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert proc.returncode == 0
        envelope = json.loads(proc.stdout)
        assert "position_id" in envelope
        assert "maint_bps" in envelope

    def test_sample_output_to_file(self, tmp_path: Path) -> None:
        out = tmp_path / "sample.json"
        proc = subprocess.run(
            [sys.executable, str(TOOL), "sample", "--output", str(out)],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert proc.returncode == 0
        assert proc.stdout == ""
        envelope = json.loads(out.read_text())
        assert "position_id" in envelope

    def test_verify_accepts_valid_envelope(self, tmp_path: Path) -> None:
        env = _base_envelope()
        p = _write_temp_env(tmp_path, env)
        proc = subprocess.run(
            [sys.executable, str(TOOL), "verify", str(p)],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert proc.returncode == 0
        result = json.loads(proc.stdout)
        assert result["status"] == "accepted"

    def test_verify_rejects_bad_envelope(self, tmp_path: Path) -> None:
        env = _base_envelope(position_base=-1)
        p = _write_temp_env(tmp_path, env)
        proc = subprocess.run(
            [sys.executable, str(TOOL), "verify", str(p)],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert proc.returncode == 2
        result = json.loads(proc.stdout)
        assert result["status"] == "rejected"

    def test_verify_nonexistent_file(self) -> None:
        proc = subprocess.run(
            [sys.executable, str(TOOL), "verify", "/nonexistent/path.json"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert proc.returncode == 3
        result = json.loads(proc.stdout)
        assert result["status"] == "inconclusive"

    def test_verify_malformed_json(self, tmp_path: Path) -> None:
        p = tmp_path / "bad.json"
        p.write_text("{not valid json")
        proc = subprocess.run(
            [sys.executable, str(TOOL), "verify", str(p)],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert proc.returncode == 3
        result = json.loads(proc.stdout)
        assert result["status"] == "inconclusive"
        assert any("cascade_load_failed" in e for e in result["errors"])

    def test_verify_non_object_top_level(self, tmp_path: Path) -> None:
        p = tmp_path / "array.json"
        p.write_text("[1, 2, 3]")
        proc = subprocess.run(
            [sys.executable, str(TOOL), "verify", str(p)],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert proc.returncode == 3
        result = json.loads(proc.stdout)
        assert result["status"] == "inconclusive"
        assert any("top_level_must_be_object" in e for e in result["errors"])
