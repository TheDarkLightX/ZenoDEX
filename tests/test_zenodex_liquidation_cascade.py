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
    cascade_run_fixed,
    cascade_run_variable,
    closed_portion,
    funded_liquidation_ok,
    is_liquidatable,
    liq_penalty,
    liq_step,
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

    def test_position_below_bps_dust_escalation(self) -> None:
        # pos=5000, fraction=1: closed = 5000*1/10000 = 0 (dust)
        # With dust escalation (liq_step), position full-closes to 0
        # This matches the Lean liqStep_strictly_decreases theorem
        env = _base_envelope(position_base=5_000, liquidation_fraction_bps=1)
        result = verify_liquidation_cascade_envelope(env)
        assert result.position_decreases is True
        assert result.cascade_terminates is True


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


class TestLiqStepDustEscalation:
    """Test liqStep with dust escalation, matching the Lean `liqStep` definition.

    When closedPortion = 0 (dust) and pos > 0 and fraction >= 1,
    liqStep full-closes to 0 instead of returning pos unchanged.
    """

    def test_dust_position_full_closes(self) -> None:
        # pos=50, fraction=1: closed = 50*1/10000 = 0 (dust)
        # liqStep should escalate to full close = 0
        assert liq_step(50, 1) == 0

    def test_dust_position_fraction_100(self) -> None:
        # pos=99, fraction=100: closed = 99*100/10000 = 0 (dust)
        # liqStep should escalate to full close = 0
        assert liq_step(99, 100) == 0

    def test_non_dust_position_decreases(self) -> None:
        # pos=10000, fraction=1: closed = 10000*1/10000 = 1 (not dust)
        # liqStep = remaining = 9999
        assert liq_step(10000, 1) == 9999

    def test_full_close_reaches_zero(self) -> None:
        # pos=100, fraction=10000: closed = 100*10000/10000 = 100
        # liqStep = remaining = 0
        assert liq_step(100, 10000) == 0

    def test_zero_position_stays_zero(self) -> None:
        assert liq_step(0, 5000) == 0

    def test_liq_step_strictly_decreases(self) -> None:
        # For pos > 0 and 1 <= fraction <= BPS, liqStep < pos
        for pos in [1, 50, 99, 100, 1000, 10000, 50000]:
            for frac in [1, 100, 1000, 5000, 10000]:
                result = liq_step(pos, frac)
                assert result < pos, f"liq_step({pos},{frac})={result} should be < {pos}"


class TestCascadeRunFixed:
    """Test cascade_run_fixed matches the Lean iterated_cascade_terminates theorem.

    For any pos and fixed fraction in [1, BPS], the cascade terminates
    in at most pos steps.
    """

    def test_small_position_terminates(self) -> None:
        steps = cascade_run_fixed(100, 1000)
        assert steps <= 100
        assert steps > 0

    def test_large_position_terminates(self) -> None:
        steps = cascade_run_fixed(10000, 5000)
        assert steps <= 10000
        assert steps > 0

    def test_dust_position_terminates_quickly(self) -> None:
        # pos=50, fraction=1: dust escalation full-closes in 1 step
        steps = cascade_run_fixed(50, 1)
        assert steps == 1

    def test_full_close_one_step(self) -> None:
        steps = cascade_run_fixed(10000, 10000)
        assert steps == 1

    def test_zero_position_zero_steps(self) -> None:
        steps = cascade_run_fixed(0, 5000)
        assert steps == 0

    def test_steps_bounded_by_position(self) -> None:
        # For all tested positions and fractions, steps <= pos
        for pos in [1, 10, 100, 1000, 10000]:
            for frac in [1, 100, 5000, 10000]:
                steps = cascade_run_fixed(pos, frac)
                assert steps <= pos, f"steps={steps} should be <= pos={pos} (frac={frac})"


class TestCascadeRunVariable:
    """Test cascade_run_variable matches the Lean iterated_cascade_terminates_variable theorem.

    For any pos and variable fraction schedule (each fraction in [1, BPS]),
    the cascade terminates in at most pos steps.
    """

    def test_variable_schedule_terminates(self) -> None:
        # Alternating between fraction=1 and fraction=5000
        steps = cascade_run_variable(10000, [1, 5000])
        assert steps <= 10000
        assert steps > 0

    def test_variable_schedule_dust_escalation(self) -> None:
        # Start with dust fraction, then escalate
        steps = cascade_run_variable(50, [1, 10000])
        assert steps == 1  # First step: dust escalation to 0

    def test_variable_schedule_all_full_close(self) -> None:
        steps = cascade_run_variable(10000, [10000, 10000, 10000])
        assert steps == 1

    def test_variable_schedule_steps_bounded_by_position(self) -> None:
        for pos in [1, 10, 100, 1000, 10000]:
            for schedule in [[1, 5000], [1, 100, 10000], [5000], [1], [10000]]:
                steps = cascade_run_variable(pos, schedule)
                assert steps <= pos, (
                    f"steps={steps} should be <= pos={pos} (schedule={schedule})"
                )

    def test_variable_schedule_mixed_fractions(self) -> None:
        # Mix of small and large fractions
        steps = cascade_run_variable(10000, [1, 100, 1000, 5000, 10000])
        assert steps <= 10000
        assert steps > 0

    def test_variable_schedule_single_fraction(self) -> None:
        # Single fraction schedule should match fixed fraction
        steps_var = cascade_run_variable(10000, [5000])
        steps_fixed = cascade_run_fixed(10000, 5000)
        assert steps_var == steps_fixed


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
