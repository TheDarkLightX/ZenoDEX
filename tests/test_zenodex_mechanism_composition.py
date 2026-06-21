#!/usr/bin/env python3
"""Tests for ZenoDEX Mechanism Composition Verifier.

Covers:
- Schema validation (missing fields, bad types, out of range)
- Parallel composition: payout bounded by sum cap, zero when ineligible
- Series composition: payout bounded by shared cap, counterexample beats proof
- Boundary cases: zero cap, zero claims, equality
- CLI subprocess tests
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_mechanism_composition import (
    Submission,
    parallel_payout,
    sample_envelope,
    series_payout,
    verify_composition_envelope,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
TOOL = REPO_ROOT / "tools" / "zenodex_mechanism_composition.py"


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
    def test_non_dict_rejected(self) -> None:
        result = verify_composition_envelope([1, 2, 3])  # type: ignore[arg-type]
        assert result.status == "rejected"
        assert "top_level_must_be_object" in result.errors

    def test_bad_composition_type_rejected(self) -> None:
        env = _base_envelope(composition_type="invalid")
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert "composition_type_must_be_parallel_or_series" in result.errors

    def test_missing_composition_type_rejected(self) -> None:
        env = _base_envelope()
        del env["composition_type"]
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert "composition_type_must_be_parallel_or_series" in result.errors

    def test_cap_must_be_nonneg(self) -> None:
        env = _base_envelope(cap1=-1)
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("cap1" in e for e in result.errors)

    def test_bool_as_int_rejected(self) -> None:
        env = _base_envelope(cap1=True)
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("cap1" in e for e in result.errors)

    def test_sub_must_be_object(self) -> None:
        env = _base_envelope(sub1="not_an_object")
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("sub1" in e for e in result.errors)

    def test_sub_eligible_must_be_bool(self) -> None:
        env = _base_envelope(sub1={"eligible": 1, "claimed": 50})
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("eligible" in e for e in result.errors)

    def test_sub_claimed_must_be_nonneg(self) -> None:
        env = _base_envelope(sub1={"eligible": True, "claimed": -1})
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("claimed" in e for e in result.errors)


# --- Parallel Composition ---


class TestParallelComposition:
    def test_both_eligible_within_bounds(self) -> None:
        env = _base_envelope(
            composition_type="parallel",
            cap1=100,
            cap2=200,
            sub1={"eligible": True, "claimed": 50},
            sub2={"eligible": True, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.sub1_payout == 50
        assert result.sub2_payout == 150
        assert result.total_payout == 200
        assert result.bound == 300
        assert result.within_bound is True

    def test_one_ineligible(self) -> None:
        env = _base_envelope(
            composition_type="parallel",
            cap1=100,
            cap2=200,
            sub1={"eligible": False, "claimed": 50},
            sub2={"eligible": True, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.sub1_payout == 0
        assert result.sub2_payout == 150
        assert result.total_payout == 150

    def test_both_ineligible_zero_payout(self) -> None:
        env = _base_envelope(
            composition_type="parallel",
            cap1=100,
            cap2=200,
            sub1={"eligible": False, "claimed": 50},
            sub2={"eligible": False, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.total_payout == 0
        assert result.within_bound is True

    def test_claim_exceeds_cap_capped(self) -> None:
        env = _base_envelope(
            composition_type="parallel",
            cap1=100,
            cap2=200,
            sub1={"eligible": True, "claimed": 500},
            sub2={"eligible": True, "claimed": 500},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.sub1_payout == 100
        assert result.sub2_payout == 200
        assert result.total_payout == 300
        assert result.bound == 300

    def test_zero_cap_zero_payout(self) -> None:
        env = _base_envelope(
            composition_type="parallel",
            cap1=0,
            cap2=0,
            sub1={"eligible": True, "claimed": 50},
            sub2={"eligible": True, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.total_payout == 0


# --- Series Composition ---


class TestSeriesComposition:
    def test_proof_eligible_proof_wins(self) -> None:
        env = _base_envelope(
            composition_type="series",
            cap1=100,
            cap2=0,
            sub1={"eligible": True, "claimed": 50},
            sub2={"eligible": True, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.sub1_payout == 50
        assert result.sub2_payout == 0
        assert result.total_payout == 50
        assert result.bound == 100

    def test_proof_ineligible_counterexample_wins(self) -> None:
        env = _base_envelope(
            composition_type="series",
            cap1=100,
            cap2=0,
            sub1={"eligible": False, "claimed": 50},
            sub2={"eligible": True, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.sub1_payout == 0
        assert result.sub2_payout == 100
        assert result.total_payout == 100
        assert result.bound == 100

    def test_both_ineligible_zero_payout(self) -> None:
        env = _base_envelope(
            composition_type="series",
            cap1=100,
            cap2=0,
            sub1={"eligible": False, "claimed": 50},
            sub2={"eligible": False, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.total_payout == 0
        assert result.bound == 100

    def test_counterexample_claim_exceeds_cap_capped(self) -> None:
        env = _base_envelope(
            composition_type="series",
            cap1=100,
            cap2=0,
            sub1={"eligible": False, "claimed": 50},
            sub2={"eligible": True, "claimed": 500},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.sub2_payout == 100
        assert result.total_payout == 100

    def test_zero_cap_zero_payout(self) -> None:
        env = _base_envelope(
            composition_type="series",
            cap1=0,
            cap2=0,
            sub1={"eligible": False, "claimed": 50},
            sub2={"eligible": True, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.total_payout == 0


# --- Pure Function Tests ---


class TestPureFunctions:
    def test_parallel_payout_sum(self) -> None:
        sub1 = Submission(eligible=True, claimed=50)
        sub2 = Submission(eligible=True, claimed=150)
        assert parallel_payout(100, 200, sub1, sub2) == 200

    def test_parallel_payout_ineligible_zero(self) -> None:
        sub1 = Submission(eligible=False, claimed=50)
        sub2 = Submission(eligible=True, claimed=150)
        assert parallel_payout(100, 200, sub1, sub2) == 150

    def test_series_payout_proof_wins(self) -> None:
        sub1 = Submission(eligible=True, claimed=50)
        sub2 = Submission(eligible=True, claimed=150)
        assert series_payout(100, sub1, sub2) == 50

    def test_series_payout_counterexample_wins(self) -> None:
        sub1 = Submission(eligible=False, claimed=50)
        sub2 = Submission(eligible=True, claimed=150)
        assert series_payout(100, sub1, sub2) == 100

    def test_series_payout_both_ineligible(self) -> None:
        sub1 = Submission(eligible=False, claimed=50)
        sub2 = Submission(eligible=False, claimed=150)
        assert series_payout(100, sub1, sub2) == 0

    def test_payout_capped_at_cap(self) -> None:
        sub = Submission(eligible=True, claimed=500)
        assert parallel_payout(100, 200, sub, sub) == 300

    def test_payout_zero_when_ineligible(self) -> None:
        sub = Submission(eligible=False, claimed=500)
        assert parallel_payout(100, 200, sub, sub) == 0


# --- Additional Edge Cases ---


class TestEdgeCases:
    def test_zero_claim_eligible_zero_payout(self) -> None:
        env = _base_envelope(
            composition_type="parallel",
            cap1=100,
            cap2=200,
            sub1={"eligible": True, "claimed": 0},
            sub2={"eligible": True, "claimed": 0},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.total_payout == 0

    def test_max_cap_boundary(self) -> None:
        from tools.zenodex_mechanism_composition import MAX_CAP

        env = _base_envelope(
            composition_type="parallel",
            cap1=MAX_CAP,
            cap2=MAX_CAP,
            sub1={"eligible": True, "claimed": MAX_CAP},
            sub2={"eligible": True, "claimed": MAX_CAP},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.total_payout == 2 * MAX_CAP
        assert result.bound == 2 * MAX_CAP

    def test_cap_above_max_rejected(self) -> None:
        from tools.zenodex_mechanism_composition import MAX_CAP

        env = _base_envelope(cap1=MAX_CAP + 1)
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("cap1" in e for e in result.errors)

    def test_missing_cap1_rejected(self) -> None:
        env = _base_envelope()
        del env["cap1"]
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("cap1" in e for e in result.errors)

    def test_missing_cap2_rejected(self) -> None:
        env = _base_envelope()
        del env["cap2"]
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("cap2" in e for e in result.errors)

    def test_missing_sub1_claimed_rejected(self) -> None:
        env = _base_envelope(sub1={"eligible": True})
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("claimed" in e for e in result.errors)

    def test_missing_sub1_eligible_rejected(self) -> None:
        env = _base_envelope(sub1={"claimed": 50})
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert any("eligible" in e for e in result.errors)

    def test_series_cap2_nonzero_rejected(self) -> None:
        env = _base_envelope(
            composition_type="series",
            cap1=100,
            cap2=200,
            sub1={"eligible": True, "claimed": 50},
            sub2={"eligible": True, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "rejected"
        assert "series_cap2_should_be_zero" in result.errors

    def test_series_cap2_zero_accepted(self) -> None:
        env = _base_envelope(
            composition_type="series",
            cap1=100,
            cap2=0,
            sub1={"eligible": True, "claimed": 50},
            sub2={"eligible": True, "claimed": 150},
        )
        result = verify_composition_envelope(env)
        assert result.status == "accepted"
        assert result.total_payout == 50

    def test_oversized_file_rejected(self, tmp_path: Path) -> None:
        p = tmp_path / "big.json"
        p.write_text("x" * 2_000_000)
        proc = subprocess.run(
            [sys.executable, str(TOOL), "verify", str(p)],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert proc.returncode == 3
        result = json.loads(proc.stdout)
        assert result["status"] == "inconclusive"


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
        assert "composition_type" in envelope
        assert "cap1" in envelope
        assert "sub1" in envelope

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
        assert "composition_type" in envelope

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
        env = _base_envelope(composition_type="invalid")
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
        assert any("load_failed" in e for e in result["errors"])
