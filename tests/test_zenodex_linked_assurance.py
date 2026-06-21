#!/usr/bin/env python3
"""Tests for ZenoDEX Linked Assurance Threshold Verifier.

Covers:
- Schema validation (missing fields, bad types, out of range)
- Pledge dominance (threshold, boundary, free-rider)
- Delay monotonicity (longer delay pulls in more pledgers)
- Aggregate funding (n*B >= C)
- Required bond computation
- CLI subprocess tests
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_linked_assurance import (
    sample_envelope,
    verify_linked_assurance_envelope,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
TOOL = REPO_ROOT / "tools" / "zenodex_linked_assurance.py"


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
        del env["pledge_bond_e8"]
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert "missing_required_field:pledge_bond_e8" in result.errors

    def test_bond_must_be_nonneg(self) -> None:
        env = _base_envelope(pledge_bond_e8=-1)
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert any("pledge_bond_e8" in e for e in result.errors)

    def test_valuation_must_be_positive(self) -> None:
        env = _base_envelope(buyer_valuation_e8=0)
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert any("buyer_valuation_e8" in e for e in result.errors)

    def test_delta_num_must_be_positive(self) -> None:
        env = _base_envelope(delta_num=0)
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert any("delta_num" in e for e in result.errors)

    def test_delta_den_must_be_at_least_2(self) -> None:
        env = _base_envelope(delta_den=1)
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert any("delta_den" in e for e in result.errors)

    def test_delta_must_be_strictly_less_than_one(self) -> None:
        env = _base_envelope(delta_num=2, delta_den=2)
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert "delta_must_be_strictly_less_than_one" in result.errors

    def test_bad_campaign_id_rejected(self) -> None:
        env = _base_envelope(campaign_id="")
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert any("campaign_id" in e for e in result.errors)

    def test_bool_as_int_rejected(self) -> None:
        env = _base_envelope(pledge_bond_e8=True)
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert any("pledge_bond_e8" in e for e in result.errors)

    def test_non_dict_rejected(self) -> None:
        result = verify_linked_assurance_envelope([1, 2, 3])  # type: ignore[arg-type]
        assert result.status == "rejected"
        assert "top_level_must_be_object" in result.errors

    def test_participant_count_above_max_rejected(self) -> None:
        env = _base_envelope(participant_count=10_001)
        result = verify_linked_assurance_envelope(env)
        assert result.status == "rejected"
        assert any("participant_count" in e for e in result.errors)


# --- Pledge Dominance ---


class TestPledgeDominance:
    def test_pledge_dominates_at_sample(self) -> None:
        # v=100, B=30, delta=1/2: LHS = 100*(2-1) = 100 >= 30*2 = 60.
        env = _base_envelope()
        result = verify_linked_assurance_envelope(env)
        assert result.pledge_dominates is True
        assert result.lhs == 100_000_000
        assert result.rhs == 60_000_000
        assert result.status == "accepted"

    def test_free_rider_does_not_dominate(self) -> None:
        # v=100, B=60, delta=1/2: LHS = 100 < 120 = RHS. Free-rider.
        env = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=60_000_000,
            delta_num=1,
            delta_den=2,
        )
        result = verify_linked_assurance_envelope(env)
        assert result.pledge_dominates is False
        assert "pledge_does_not_dominate" in result.errors
        assert result.status == "rejected"

    def test_delay_pulls_in_pledger(self) -> None:
        # Same buyer v=100, B=60, but delta=1/4 (longer delay):
        # LHS = 100*(4-1) = 300 >= 60*4 = 240. Pledge dominates.
        env = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=60_000_000,
            delta_num=1,
            delta_den=4,
            production_cost_e8=300_000_000,  # n*B = 5*60 = 300 >= 300
        )
        result = verify_linked_assurance_envelope(env)
        assert result.pledge_dominates is True
        assert result.lhs == 300_000_000
        assert result.rhs == 240_000_000
        assert result.status == "accepted"

    def test_boundary_equality_dominates(self) -> None:
        # v=100, B=50, delta=1/2: LHS = 100, RHS = 100. Equality = dominates.
        env = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=50_000_000,
            delta_num=1,
            delta_den=2,
            production_cost_e8=250_000_000,  # n*B = 5*50 = 250 >= 250
        )
        result = verify_linked_assurance_envelope(env)
        assert result.pledge_dominates is True
        assert result.lhs == result.rhs
        assert result.status == "accepted"

    def test_one_above_boundary_not_dominant(self) -> None:
        # v=100, B=51, delta=1/2: LHS = 100 < 102 = RHS.
        env = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=51_000_000,
            delta_num=1,
            delta_den=2,
        )
        result = verify_linked_assurance_envelope(env)
        assert result.pledge_dominates is False
        assert result.status == "rejected"

    def test_zero_bond_always_dominant(self) -> None:
        # B=0: RHS = 0. Any positive v with valid delta: LHS > 0.
        env = _base_envelope(
            pledge_bond_e8=0,
            production_cost_e8=1,  # n*B = 0 < 1, aggregate fails
        )
        result = verify_linked_assurance_envelope(env)
        assert result.pledge_dominates is True
        assert "pledge_does_not_dominate" not in result.errors
        # But aggregate is insufficient
        assert "aggregate_insufficient" in result.errors
        assert result.status == "rejected"


# --- Delay Monotonicity ---


class TestDelayMonotonicity:
    def test_longer_delay_larger_lhs(self) -> None:
        env_half = _base_envelope(delta_num=1, delta_den=2)
        env_quarter = _base_envelope(delta_num=1, delta_den=4, production_cost_e8=120_000_000)
        r_half = verify_linked_assurance_envelope(env_half)
        r_quarter = verify_linked_assurance_envelope(env_quarter)
        assert r_quarter.lhs > r_half.lhs

    def test_delay_flips_free_rider_to_pledger(self) -> None:
        # At delta=1/2, B=60: free-rider (100 < 120)
        env_half = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=60_000_000,
            delta_num=1,
            delta_den=2,
        )
        r_half = verify_linked_assurance_envelope(env_half)
        assert r_half.pledge_dominates is False

        # At delta=1/4, same B=60: pledger (300 >= 240)
        env_quarter = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=60_000_000,
            delta_num=1,
            delta_den=4,
            production_cost_e8=300_000_000,
        )
        r_quarter = verify_linked_assurance_envelope(env_quarter)
        assert r_quarter.pledge_dominates is True


# --- Aggregate Funding ---


class TestAggregateFunding:
    def test_aggregate_meets_cost(self) -> None:
        # n=5, B=20, C=100: 5*20 = 100 >= 100.
        env = _base_envelope(
            pledge_bond_e8=20_000_000,
            participant_count=5,
            production_cost_e8=100_000_000,
        )
        result = verify_linked_assurance_envelope(env)
        assert result.aggregate_meets_cost is True
        assert result.total_pledged_e8 == 100_000_000

    def test_aggregate_insufficient(self) -> None:
        # n=4, B=20, C=100: 4*20 = 80 < 100.
        env = _base_envelope(
            pledge_bond_e8=20_000_000,
            participant_count=4,
            production_cost_e8=100_000_000,
        )
        result = verify_linked_assurance_envelope(env)
        assert result.aggregate_meets_cost is False
        assert "aggregate_insufficient" in result.errors
        assert result.status == "rejected"

    def test_aggregate_exact_boundary(self) -> None:
        # n=5, B=20, C=100: exact boundary.
        env = _base_envelope(
            pledge_bond_e8=20_000_000,
            participant_count=5,
            production_cost_e8=100_000_000,
        )
        result = verify_linked_assurance_envelope(env)
        assert result.total_pledged_e8 == result.production_cost_e8
        assert result.aggregate_meets_cost is True


# --- Required Bond ---


class TestRequiredBond:
    def test_required_bond_when_not_dominant(self) -> None:
        # v=100, B=60, delta=1/2: LHS=100, deltaDen=2.
        # required = ceil(100/2) = 50.
        env = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=60_000_000,
            delta_num=1,
            delta_den=2,
        )
        result = verify_linked_assurance_envelope(env)
        assert result.required_bond_e8 is not None
        assert result.required_bond_e8 == 50_000_000

    def test_required_bond_none_when_dominant(self) -> None:
        env = _base_envelope()
        result = verify_linked_assurance_envelope(env)
        assert result.required_bond_e8 is None

    def test_required_bond_with_longer_delay(self) -> None:
        # v=100, B=60, delta=1/4: LHS=300, deltaDen=4.
        # But this IS dominant (300 >= 240), so required_bond = None.
        env = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=61_000_000,  # 61*4=244 > 300? No, 244 < 300. Still dominant.
            delta_num=1,
            delta_den=4,
            production_cost_e8=305_000_000,
        )
        result = verify_linked_assurance_envelope(env)
        # 300 >= 244, dominant. required_bond = None.
        assert result.pledge_dominates is True
        assert result.required_bond_e8 is None

    def test_required_bond_with_longer_delay_not_dominant(self) -> None:
        # v=100, B=80, delta=1/4: LHS=300, RHS=320. Not dominant.
        # required = ceil(300/4) = 75.
        env = _base_envelope(
            buyer_valuation_e8=100_000_000,
            pledge_bond_e8=80_000_000,
            delta_num=1,
            delta_den=4,
        )
        result = verify_linked_assurance_envelope(env)
        assert result.pledge_dominates is False
        assert result.required_bond_e8 is not None
        assert result.required_bond_e8 == 75_000_000


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
        assert "campaign_id" in envelope
        assert "delta_num" in envelope

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
        assert "campaign_id" in envelope

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
        env = _base_envelope(pledge_bond_e8=60_000_000, delta_num=1, delta_den=2)
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
        assert any("linked_assurance_load_failed" in e for e in result["errors"])

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
