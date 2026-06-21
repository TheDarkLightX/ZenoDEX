#!/usr/bin/env python3
"""Tests for ZenoDEX Liquidation Cascade Termination Verifier.

Covers:
- Schema validation (missing fields, bad types, out of range)
- Position strictly decreases (fraction >= 1, pos >= BPS)
- Cascade terminates (remaining <= pos - 1)
- Post-liquidation safety (guard ensures margin invariant)
- Penalty bounds (penalty <= maint margin)
- Boundary cases (full close, half close, zero fraction)
- CLI subprocess tests
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_liquidation_cascade import (
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


# --- Schema Validation ---


class TestSchemaValidation:
    def test_missing_required_field_rejected(self) -> None:
        env = _base_envelope()
        del env["penalty_bps"]
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert "missing_required_field:penalty_bps" in result.errors

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

    def test_maint_bps_must_be_positive(self) -> None:
        env = _base_envelope(maint_bps=0)
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("maint_bps" in e for e in result.errors)

    def test_penalty_bps_must_be_nonneg(self) -> None:
        env = _base_envelope(penalty_bps=-1)
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("penalty_bps" in e for e in result.errors)

    def test_fraction_above_bps_rejected(self) -> None:
        env = _base_envelope(liquidation_fraction_bps=10_001)
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("liquidation_fraction_bps" in e for e in result.errors)

    def test_bad_position_id_rejected(self) -> None:
        env = _base_envelope(position_id="")
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("position_id" in e for e in result.errors)

    def test_bool_as_int_rejected(self) -> None:
        env = _base_envelope(penalty_bps=True)
        result = verify_liquidation_cascade_envelope(env)
        assert result.status == "rejected"
        assert any("penalty_bps" in e for e in result.errors)

    def test_non_dict_rejected(self) -> None:
        result = verify_liquidation_cascade_envelope([1, 2, 3])  # type: ignore[arg-type]
        assert result.status == "rejected"
        assert "top_level_must_be_object" in result.errors


# --- Position Strictly Decreases ---


class TestPositionDecreases:
    def test_position_decreases_with_valid_fraction(self) -> None:
        # pos=10000, fraction=5000 (50%): closed=5000, remaining=5000 < 10000
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=5_000)
        result = verify_liquidation_cascade_envelope(env)
        assert result.closed_portion == 5_000
        assert result.remaining_position == 5_000
        assert result.position_decreases is True
        assert result.cascade_terminates is True

    def test_full_close_reaches_zero(self) -> None:
        # pos=10000, fraction=10000 (100%): closed=10000, remaining=0
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=10_000)
        result = verify_liquidation_cascade_envelope(env)
        assert result.closed_portion == 10_000
        assert result.remaining_position == 0
        assert result.position_decreases is True

    def test_small_fraction_large_position(self) -> None:
        # pos=10000, fraction=1 (0.01%): closed=1, remaining=9999
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=1)
        result = verify_liquidation_cascade_envelope(env)
        assert result.closed_portion == 1
        assert result.remaining_position == 9_999
        assert result.position_decreases is True

    def test_zero_fraction_rejected(self) -> None:
        env = _base_envelope(liquidation_fraction_bps=0)
        result = verify_liquidation_cascade_envelope(env)
        assert "fraction_must_be_at_least_1_bps" in result.errors
        assert result.status == "rejected"


# --- Cascade Terminates ---


class TestCascadeTerminates:
    def test_cascade_terminates_remaining_le_pos_minus_1(self) -> None:
        env = _base_envelope(position_base=10_000, liquidation_fraction_bps=5_000)
        result = verify_liquidation_cascade_envelope(env)
        assert result.remaining_position <= 10_000 - 1
        assert result.cascade_terminates is True

    def test_position_below_bps_flagged(self) -> None:
        # pos=100 < BPS=10000: termination guarantee doesn't apply
        env = _base_envelope(position_base=100, liquidation_fraction_bps=5_000)
        result = verify_liquidation_cascade_envelope(env)
        assert "position_must_be_at_least_bps_for_termination" in result.errors


# --- Post-Liquidation Safety ---


class TestPostLiquidationSafety:
    def test_safe_post_liquidation_accepted(self) -> None:
        env = _base_envelope()
        result = verify_liquidation_cascade_envelope(env)
        assert result.post_liquidation_safe is True
        assert result.status == "accepted"

    def test_penalty_exceeds_maint_rejected(self) -> None:
        env = _base_envelope(maint_bps=500, penalty_bps=600)
        result = verify_liquidation_cascade_envelope(env)
        assert "penalty_exceeds_maint_margin" in result.errors
        assert result.status == "rejected"


# --- Penalty Bounds ---


class TestPenaltyBounds:
    def test_penalty_capped_at_collateral(self) -> None:
        # Very low collateral, high penalty: capped_penalty = collateral
        env = _base_envelope(
            collateral_quote=1_000_000,
            penalty_bps=5_000,
            position_base=10_000,
            liquidation_fraction_bps=10_000,
        )
        result = verify_liquidation_cascade_envelope(env)
        assert result.capped_penalty <= result.collateral_quote

    def test_zero_penalty(self) -> None:
        env = _base_envelope(penalty_bps=0)
        result = verify_liquidation_cascade_envelope(env)
        assert result.raw_penalty == 0
        assert result.capped_penalty == 0
        assert result.post_collateral == result.collateral_quote


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
        env = _base_envelope(liquidation_fraction_bps=0)
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
