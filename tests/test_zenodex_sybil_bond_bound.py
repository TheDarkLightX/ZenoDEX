#!/usr/bin/env python3
"""Tests for ZenoDEX Sybil Bond Bound Verifier (k-atom generalization).

Covers:
- Schema validation (missing fields, bad types, out of range)
- k=2 binding case (Sybil deterred at boundary)
- k=3, k=10, k=100 (larger splits easier to block)
- k2_binding implies covers_all_k
- Deficient bond admits Sybil
- Boundary cases (equality, off-by-one)
- Required bond computation
- CLI subprocess tests
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_sybil_bond_bound import (
    sample_envelope,
    verify_sybil_bond_envelope,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
TOOL = REPO_ROOT / "tools" / "zenodex_sybil_bond_bound.py"


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
        del env["identity_bond_e8"]
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert "missing_required_field:identity_bond_e8" in result.errors

    def test_bond_must_be_nonneg(self) -> None:
        env = _base_envelope(identity_bond_e8=-1)
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert any("identity_bond_e8" in e for e in result.errors)

    def test_reward_must_be_positive(self) -> None:
        env = _base_envelope(total_reward_e8=0)
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert any("total_reward_e8" in e for e in result.errors)

    def test_cohort_must_be_positive(self) -> None:
        env = _base_envelope(cohort_size=0)
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert any("cohort_size" in e for e in result.errors)

    def test_split_atoms_must_be_at_least_2(self) -> None:
        env = _base_envelope(split_atoms=1)
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert any("split_atoms" in e for e in result.errors)

    def test_bad_pool_id_rejected(self) -> None:
        env = _base_envelope(pool_id="")
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert any("pool_id" in e for e in result.errors)

    def test_bool_as_int_rejected(self) -> None:
        env = _base_envelope(identity_bond_e8=True)
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert any("identity_bond_e8" in e for e in result.errors)

    def test_non_dict_rejected(self) -> None:
        result = verify_sybil_bond_envelope([1, 2, 3])  # type: ignore[arg-type]
        assert result.status == "rejected"
        assert "top_level_must_be_object" in result.errors

    def test_cohort_above_max_rejected(self) -> None:
        env = _base_envelope(cohort_size=10_001)
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert any("cohort_size" in e for e in result.errors)

    def test_split_atoms_above_max_rejected(self) -> None:
        env = _base_envelope(split_atoms=10_001)
        result = verify_sybil_bond_envelope(env)
        assert result.status == "rejected"
        assert any("split_atoms" in e for e in result.errors)


# --- k=2 Binding Case ---


class TestK2Binding:
    def test_k2_boundary_deterred(self) -> None:
        # V=100, B=15, n=4: V*(n-1) = 300, B*n*(n+1) = 15*4*5 = 300. Equality = deterred.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=15_000_000,
            cohort_size=4,
            split_atoms=2,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.lhs == 300_000_000
        assert result.rhs == 300_000_000
        assert result.sybil_unprofitable is True
        assert result.k2_binding is True
        assert result.covers_all_k is True
        assert result.status == "accepted"

    def test_k2_deficient_bond_admits_sybil(self) -> None:
        # V=100, B=10, n=4: V*(n-1) = 300, B*n*(n+1) = 10*4*5 = 200. 300 > 200.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=10_000_000,
            cohort_size=4,
            split_atoms=2,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.sybil_unprofitable is False
        assert result.k2_binding is False
        assert result.status == "rejected"
        assert "sybil_profitable" in result.errors
        assert "k2_binding_violated" in result.errors

    def test_k2_one_above_boundary(self) -> None:
        # V=100, B=16, n=4: B*n*(n+1) = 16*4*5 = 320 > 300. Strictly deterred.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=16_000_000,
            cohort_size=4,
            split_atoms=2,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.sybil_unprofitable is True
        assert result.status == "accepted"


# --- k >= 3: Larger Splits Easier to Block ---


class TestKGeneralization:
    def test_k3_deterred_by_k2_bond(self) -> None:
        # B=15, n=4, k=3: B*n*(n+2) = 15*4*6 = 360 >= 300. Deterred.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=15_000_000,
            cohort_size=4,
            split_atoms=3,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.sybil_unprofitable is True
        assert result.k2_binding is True
        assert result.covers_all_k is True
        assert result.status == "accepted"

    def test_k10_deterred_by_k2_bond(self) -> None:
        # B=15, n=4, k=10: B*n*(n+9) = 15*4*13 = 780 >= 300. Deterred.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=15_000_000,
            cohort_size=4,
            split_atoms=10,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.sybil_unprofitable is True
        assert result.status == "accepted"

    def test_k100_deterred_by_k2_bond(self) -> None:
        # B=15, n=4, k=100: B*n*(n+99) = 15*4*103 = 6180 >= 300. Deterred.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=15_000_000,
            cohort_size=4,
            split_atoms=100,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.sybil_unprofitable is True
        assert result.covers_all_k is True
        assert result.status == "accepted"

    def test_k3_rhs_strictly_larger_than_k2_rhs(self) -> None:
        env_k2 = _base_envelope(split_atoms=2)
        env_k3 = _base_envelope(split_atoms=3)
        r_k2 = verify_sybil_bond_envelope(env_k2)
        r_k3 = verify_sybil_bond_envelope(env_k3)
        assert r_k2.lhs == r_k3.lhs
        assert r_k3.rhs > r_k2.rhs

    def test_covers_all_k_flag_true_when_k2_binding(self) -> None:
        for k in [2, 3, 5, 10, 100, 1000]:
            env = _base_envelope(split_atoms=k)
            result = verify_sybil_bond_envelope(env)
            assert result.k2_binding is True, f"k={k}"
            assert result.covers_all_k is True, f"k={k}"
            assert result.sybil_unprofitable is True, f"k={k}"

    def test_k3_passes_but_k2_fails(self) -> None:
        # V=100, B=11, n=4: k2_rhs = 11*4*5 = 220 < 300 (k2 fails).
        # k3_rhs = 11*4*6 = 264 < 300 (k3 also fails here).
        # Need B where k3 passes but k2 fails: k3_rhs >= 300 but k2_rhs < 300.
        # k3_rhs = B*4*6 = 24B >= 300 => B >= 12.5 => B >= 13.
        # k2_rhs = B*4*5 = 20B < 300 => B < 15.
        # So B=13: k2_rhs = 260 < 300 (fails), k3_rhs = 312 >= 300 (passes).
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=13_000_000,
            cohort_size=4,
            split_atoms=3,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.sybil_unprofitable is True
        assert result.k2_binding is False
        assert result.covers_all_k is False
        assert result.status == "rejected"
        assert "k2_binding_violated" in result.errors
        assert "sybil_profitable" not in result.errors
        # Required bond should be reported for the k2 binding case
        assert result.required_bond_e8 is not None
        assert result.required_bond_e8 == 15_000_000


# --- Required Bond Computation ---


class TestRequiredBond:
    def test_required_bond_for_k2(self) -> None:
        # V=100, n=4, k=2: lhs=300, denom=n*(n+k-1)=4*5=20.
        # required = ceil(300/20) = 15.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=10_000_000,  # deficient
            cohort_size=4,
            split_atoms=2,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.required_bond_e8 is not None
        assert result.required_bond_e8 == 15_000_000

    def test_required_bond_for_k3(self) -> None:
        # V=100_000_000, n=4, k=3: lhs=300_000_000, denom=n*(n+k-1)=4*6=24.
        # required = ceil(300_000_000/24) = 12_500_000 (divides evenly).
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=10_000_000,
            cohort_size=4,
            split_atoms=3,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.required_bond_e8 is not None
        assert result.required_bond_e8 == 12_500_000

    def test_required_bond_none_when_deterred(self) -> None:
        env = _base_envelope()
        result = verify_sybil_bond_envelope(env)
        assert result.required_bond_e8 is None


# --- Boundary Cases ---


class TestBoundary:
    def test_n1_no_sybil_gain(self) -> None:
        # n=1: V*(n-1) = 0. Any bond deters (lhs=0).
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=1,
            cohort_size=1,
            split_atoms=2,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.lhs == 0
        assert result.sybil_unprofitable is True
        assert result.status == "accepted"

    def test_zero_bond_admits_sybil_when_n_ge_2(self) -> None:
        # B=0, n=4: rhs = 0. lhs = 300 > 0. Sybil profitable.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=0,
            cohort_size=4,
            split_atoms=2,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.sybil_unprofitable is False
        assert result.status == "rejected"

    def test_large_cohort(self) -> None:
        # n=100, V=100, k=2: lhs = 100*99 = 9900.
        # B=1: rhs = 1*100*101 = 10100 >= 9900. Deterred.
        env = _base_envelope(
            total_reward_e8=100_000_000,
            identity_bond_e8=1_000_000,
            cohort_size=100,
            split_atoms=2,
        )
        result = verify_sybil_bond_envelope(env)
        assert result.sybil_unprofitable is True
        assert result.status == "accepted"


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
        assert "pool_id" in envelope
        assert "split_atoms" in envelope

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
        assert "pool_id" in envelope

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
        env = _base_envelope(identity_bond_e8=0, cohort_size=4, split_atoms=2)
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
        assert any("sybil_load_failed" in e for e in result["errors"])

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
