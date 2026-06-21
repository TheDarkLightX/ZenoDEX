#!/usr/bin/env python3
"""Tests for ZenoDEX Self-Liquidation Bound Verifier.

Covers:
- Schema validation (missing fields, bad types, out of range)
- Self-liquidation unprofitability (safe, unsafe, boundary)
- MCR must exceed 100% (mcr <= BPS rejected)
- Max safe gas compensation computation
- MCR monotonicity (higher MCR allows higher comp)
- CLI subprocess tests
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_self_liquidation_bound import (
    sample_envelope,
    verify_self_liquidation_envelope,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
TOOL = REPO_ROOT / "tools" / "zenodex_self_liquidation_bound.py"


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
        del env["gas_comp_bps"]
        result = verify_self_liquidation_envelope(env)
        assert result.status == "rejected"
        assert "missing_required_field:gas_comp_bps" in result.errors

    def test_mcr_must_be_positive(self) -> None:
        env = _base_envelope(mcr_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.status == "rejected"
        assert any("mcr_bps" in e for e in result.errors)

    def test_gas_comp_must_be_nonneg(self) -> None:
        env = _base_envelope(gas_comp_bps=-1)
        result = verify_self_liquidation_envelope(env)
        assert result.status == "rejected"
        assert any("gas_comp_bps" in e for e in result.errors)

    def test_gas_comp_above_bps_rejected(self) -> None:
        env = _base_envelope(gas_comp_bps=10_001)
        result = verify_self_liquidation_envelope(env)
        assert result.status == "rejected"
        assert any("gas_comp_bps" in e for e in result.errors)

    def test_mcr_above_max_rejected(self) -> None:
        env = _base_envelope(mcr_bps=30_001)
        result = verify_self_liquidation_envelope(env)
        assert result.status == "rejected"
        assert any("mcr_bps" in e for e in result.errors)

    def test_bad_vault_id_rejected(self) -> None:
        env = _base_envelope(vault_id="")
        result = verify_self_liquidation_envelope(env)
        assert result.status == "rejected"
        assert any("vault_id" in e for e in result.errors)

    def test_bool_as_int_rejected(self) -> None:
        env = _base_envelope(gas_comp_bps=True)
        result = verify_self_liquidation_envelope(env)
        assert result.status == "rejected"
        assert any("gas_comp_bps" in e for e in result.errors)

    def test_non_dict_rejected(self) -> None:
        result = verify_self_liquidation_envelope([1, 2, 3])  # type: ignore[arg-type]
        assert result.status == "rejected"
        assert "top_level_must_be_object" in result.errors


# --- Self-Liquidation Unprofitability ---


class TestSelfLiquidationBound:
    def test_safe_compensation_accepted(self) -> None:
        # mcr=13000, gas_comp=2307: 2307*13000=29991000 <= 10000*3000=30000000
        env = _base_envelope(mcr_bps=13000, gas_comp_bps=2307)
        result = verify_self_liquidation_envelope(env)
        assert result.self_liquidation_unprofitable is True
        assert result.lhs == 29_991_000
        assert result.rhs == 30_000_000
        assert result.status == "accepted"

    def test_unsafe_compensation_rejected(self) -> None:
        # mcr=13000, gas_comp=2308: 2308*13000=30004000 > 30000000
        env = _base_envelope(mcr_bps=13000, gas_comp_bps=2308)
        result = verify_self_liquidation_envelope(env)
        assert result.self_liquidation_unprofitable is False
        assert "self_liquidation_profitable" in result.errors
        assert result.status == "rejected"

    def test_boundary_equality_accepted(self) -> None:
        # mcr=20000, gas_comp=5000: 5000*20000=100000000 = 10000*10000
        env = _base_envelope(mcr_bps=20000, gas_comp_bps=5000)
        result = verify_self_liquidation_envelope(env)
        assert result.lhs == result.rhs
        assert result.self_liquidation_unprofitable is True
        assert result.status == "accepted"

    def test_one_above_boundary_rejected(self) -> None:
        # mcr=20000, gas_comp=5001: 5001*20000=100020000 > 100000000
        env = _base_envelope(mcr_bps=20000, gas_comp_bps=5001)
        result = verify_self_liquidation_envelope(env)
        assert result.self_liquidation_unprofitable is False
        assert result.status == "rejected"

    def test_zero_compensation_always_safe(self) -> None:
        env = _base_envelope(mcr_bps=11000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.self_liquidation_unprofitable is True
        assert result.status == "accepted"


# --- MCR Must Exceed 100% ---


class TestMCRExceeds100pct:
    def test_mcr_below_100pct_rejected(self) -> None:
        env = _base_envelope(mcr_bps=9000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.mcr_exceeds_100pct is False
        assert "mcr_must_exceed_100pct" in result.errors
        assert result.status == "rejected"

    def test_mcr_exactly_100pct_rejected(self) -> None:
        env = _base_envelope(mcr_bps=10000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.mcr_exceeds_100pct is False
        assert "mcr_must_exceed_100pct" in result.errors
        assert result.status == "rejected"

    def test_mcr_above_100pct_accepted(self) -> None:
        env = _base_envelope(mcr_bps=10001, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.mcr_exceeds_100pct is True
        assert result.status == "accepted"


# --- Max Safe Gas Compensation ---


class TestMaxSafeGasComp:
    def test_max_safe_at_130pct(self) -> None:
        # max_safe = 10000 * 3000 / 13000 = 2307 (floor)
        env = _base_envelope(mcr_bps=13000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.max_safe_gas_comp_bps == 2307

    def test_max_safe_at_150pct(self) -> None:
        # max_safe = 10000 * 5000 / 15000 = 3333 (floor)
        env = _base_envelope(mcr_bps=15000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.max_safe_gas_comp_bps == 3333

    def test_max_safe_at_110pct(self) -> None:
        # max_safe = 10000 * 1000 / 11000 = 909 (floor)
        env = _base_envelope(mcr_bps=11000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.max_safe_gas_comp_bps == 909

    def test_max_safe_at_200pct(self) -> None:
        # max_safe = 10000 * 10000 / 20000 = 5000
        env = _base_envelope(mcr_bps=20000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.max_safe_gas_comp_bps == 5000

    def test_max_safe_zero_when_mcr_below_100pct(self) -> None:
        env = _base_envelope(mcr_bps=9000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.max_safe_gas_comp_bps == 0


# --- MCR Monotonicity ---


class TestMCRMonotonicity:
    def test_higher_mcr_allows_higher_comp(self) -> None:
        # At mcr=11000, max_safe=909. At mcr=13000, max_safe=2307.
        env_low = _base_envelope(mcr_bps=11000, gas_comp_bps=0)
        env_high = _base_envelope(mcr_bps=13000, gas_comp_bps=0)
        r_low = verify_self_liquidation_envelope(env_low)
        r_high = verify_self_liquidation_envelope(env_high)
        assert r_high.max_safe_gas_comp_bps > r_low.max_safe_gas_comp_bps

    def test_same_comp_safe_at_higher_mcr_unsafe_at_lower(self) -> None:
        # gas_comp=2000: safe at mcr=13000, unsafe at mcr=11000
        env_high = _base_envelope(mcr_bps=13000, gas_comp_bps=2000)
        env_low = _base_envelope(mcr_bps=11000, gas_comp_bps=2000)
        r_high = verify_self_liquidation_envelope(env_high)
        r_low = verify_self_liquidation_envelope(env_low)
        assert r_high.self_liquidation_unprofitable is True
        assert r_low.self_liquidation_unprofitable is False


# --- Bounded Sweep: max_safe accepted, max_safe+1 rejected across MCR range ---


class TestBoundedSweepMaxSafe:
    """Sweep mcr_bps in 10001..30000 asserting max_safe is accepted and
    max_safe + 1 is rejected. Covers edge cases 10001 and 30000."""

    def test_max_safe_accepted_across_mcr_range(self) -> None:
        for mcr_bps in range(10001, 30001):
            env = _base_envelope(mcr_bps=mcr_bps, gas_comp_bps=0)
            result = verify_self_liquidation_envelope(env)
            max_safe = result.max_safe_gas_comp_bps
            assert max_safe >= 0
            env_safe = _base_envelope(mcr_bps=mcr_bps, gas_comp_bps=max_safe)
            r_safe = verify_self_liquidation_envelope(env_safe)
            assert r_safe.self_liquidation_unprofitable is True, (
                f"max_safe={max_safe} should be safe at mcr={mcr_bps}"
            )

    def test_max_safe_plus_one_rejected_across_mcr_range(self) -> None:
        for mcr_bps in range(10001, 30001):
            env = _base_envelope(mcr_bps=mcr_bps, gas_comp_bps=0)
            result = verify_self_liquidation_envelope(env)
            max_safe = result.max_safe_gas_comp_bps
            env_unsafe = _base_envelope(
                mcr_bps=mcr_bps, gas_comp_bps=max_safe + 1
            )
            r_unsafe = verify_self_liquidation_envelope(env_unsafe)
            assert r_unsafe.self_liquidation_unprofitable is False, (
                f"max_safe+1={max_safe + 1} should be unsafe at mcr={mcr_bps}"
            )

    def test_edge_case_mcr_10001(self) -> None:
        # Lowest valid MCR: max_safe = 10000 * 1 / 10001 = 0 (floor)
        env = _base_envelope(mcr_bps=10001, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.max_safe_gas_comp_bps == 0
        env_unsafe = _base_envelope(mcr_bps=10001, gas_comp_bps=1)
        r_unsafe = verify_self_liquidation_envelope(env_unsafe)
        assert r_unsafe.self_liquidation_unprofitable is False

    def test_edge_case_mcr_30000(self) -> None:
        # Highest valid MCR: max_safe = 10000 * 20000 / 30000 = 6666 (floor)
        env = _base_envelope(mcr_bps=30000, gas_comp_bps=0)
        result = verify_self_liquidation_envelope(env)
        assert result.max_safe_gas_comp_bps == 6666
        env_safe = _base_envelope(mcr_bps=30000, gas_comp_bps=6666)
        r_safe = verify_self_liquidation_envelope(env_safe)
        assert r_safe.self_liquidation_unprofitable is True
        env_unsafe = _base_envelope(mcr_bps=30000, gas_comp_bps=6667)
        r_unsafe = verify_self_liquidation_envelope(env_unsafe)
        assert r_unsafe.self_liquidation_unprofitable is False


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
        assert "vault_id" in envelope
        assert "mcr_bps" in envelope

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
        assert "vault_id" in envelope

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
        env = _base_envelope(mcr_bps=13000, gas_comp_bps=2308)
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
        assert any("self_liquidation_load_failed" in e for e in result["errors"])

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
