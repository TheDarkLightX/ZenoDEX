#!/usr/bin/env python3
"""Tests for ZenoDEX Oracle Collusion Bound Verifier.

Covers:
- Schema validation (missing fields, bad types, out of range)
- Per-identity bond + per-head reward (collusion invariance)
- Per-identity bond + split reward (deterrence amplification)
- Shared bond + per-head reward (collusion vulnerability)
- Boundary cases (equality, off-by-one)
- Coalition size edge cases
- Prob inversion detection
- CLI subprocess tests
"""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

from tools.zenodex_oracle_collusion_bound import (
    sample_envelope,
    verify_collusion_envelope,
)

REPO_ROOT = Path(__file__).resolve().parent.parent
TOOL = REPO_ROOT / "tools" / "zenodex_oracle_collusion_bound.py"


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
        del env["dispute_bond_e8"]
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert "missing_required_field:dispute_bond_e8" in result.errors

    def test_bond_must_be_positive(self) -> None:
        env = _base_envelope(dispute_bond_e8=0)
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("dispute_bond_e8" in e for e in result.errors)

    def test_bps_out_of_range_rejected(self) -> None:
        env = _base_envelope(prob_upheld_when_wrong_bps=20000)
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("prob_upheld_when_wrong_bps" in e for e in result.errors)

    def test_coalition_size_must_be_positive(self) -> None:
        env = _base_envelope(coalition_size=0)
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("coalition_size" in e for e in result.errors)

    def test_bad_bond_model_rejected(self) -> None:
        env = _base_envelope(bond_model="invalid")
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("bond_model" in e for e in result.errors)

    def test_bad_reward_model_rejected(self) -> None:
        env = _base_envelope(reward_model="invalid")
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("reward_model" in e for e in result.errors)

    def test_bad_query_id_rejected(self) -> None:
        env = _base_envelope(query_id="not_a_hash")
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("query_id" in e for e in result.errors)

    def test_bad_consumer_module_rejected(self) -> None:
        env = _base_envelope(consumer_module="x")
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("consumer_module" in e for e in result.errors)

    def test_prob_inversion_detected(self) -> None:
        env = _base_envelope(
            prob_upheld_when_wrong_bps=9000,
            prob_upheld_when_correct_bps=1000,
        )
        result = verify_collusion_envelope(env)
        assert "prob_inversion" in result.errors

    def test_non_dict_direct_call_rejected(self) -> None:
        result = verify_collusion_envelope([1, 2, 3])  # type: ignore[arg-type]
        assert result.status == "rejected"
        assert "top_level_must_be_object" in result.errors


# --- Per-Identity Bond + Per-Head Reward (Collusion Invariance) ---


class TestPerIdentityPerHead:
    def test_single_deterred_implies_collusion_deterred(self) -> None:
        env = _base_envelope(
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=10,
        )
        result = verify_collusion_envelope(env)
        assert result.single_deterred is True
        assert result.collusion_deterred is True
        assert result.collusion_invariant is True
        assert result.status == "accepted"

    def test_collusion_invariant_for_any_k(self) -> None:
        for k in [1, 2, 5, 100, 1000]:
            env = _base_envelope(
                bond_model="per_identity",
                reward_model="per_head",
                coalition_size=k,
            )
            result = verify_collusion_envelope(env)
            assert result.collusion_invariant is True, f"Failed for k={k}"
            assert result.collusion_deterred == result.single_deterred, f"Failed for k={k}"

    def test_deficient_bond_rejects_all_coalitions(self) -> None:
        env = _base_envelope(
            dispute_bond_e8=10_000_000,
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=1,
        )
        result = verify_collusion_envelope(env)
        assert result.single_deterred is False
        assert result.collusion_deterred is False
        assert result.status == "rejected"


# --- Per-Identity Bond + Split Reward (Deterrence Amplification) ---


class TestPerIdentitySplit:
    def test_split_reward_amplifies_deterrence(self) -> None:
        env = _base_envelope(
            bond_model="per_identity",
            reward_model="split",
            coalition_size=5,
        )
        result = verify_collusion_envelope(env)
        assert result.single_deterred is True
        assert result.collusion_deterred is True
        assert result.status == "accepted"

    def test_split_reward_stronger_than_per_head(self) -> None:
        env_per_head = _base_envelope(
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=5,
        )
        env_split = _base_envelope(
            bond_model="per_identity",
            reward_model="split",
            coalition_size=5,
        )
        r_ph = verify_collusion_envelope(env_per_head)
        r_sp = verify_collusion_envelope(env_split)
        assert r_ph.frivolous_scaled == r_sp.frivolous_scaled
        assert r_sp.collusion_deterred is True

    def test_split_reward_deters_even_when_per_head_fails(self) -> None:
        # With D=19, M_rej=0: frivolous_scaled = 1000*190 = 190000 = bond_scaled (19*10000)
        # Single reporter NOT deterred (equality). But k=2 split: 190000 < 2*190000 = 380000. Deterred.
        env = _base_envelope(
            dispute_reward_e8=190_000_000,
            mev_uphold_dispute_e8=0,
            mev_reject_dispute_e8=0,
            dispute_bond_e8=19_000_000,
            prob_upheld_when_wrong_bps=1000,
            prob_upheld_when_correct_bps=9000,
            bond_model="per_identity",
            reward_model="split",
            coalition_size=2,
        )
        result = verify_collusion_envelope(env)
        # Single is not deterred (equality), but split with k=2 IS deterred.
        # Overall status is rejected because single_reporter_not_deterred.
        assert result.single_deterred is False
        assert result.collusion_deterred is True
        assert result.status == "rejected"
        assert "single_reporter_not_deterred" in result.errors


# --- Shared Bond + Per-Head Reward (Collusion Vulnerability) ---


class TestSharedBondPerHead:
    def test_shared_bond_vulnerable_to_collusion(self) -> None:
        env = _base_envelope(
            bond_model="shared",
            reward_model="per_head",
            coalition_size=5,
        )
        result = verify_collusion_envelope(env)
        assert result.single_deterred is True
        assert result.collusion_deterred is False
        assert result.status == "rejected"
        assert "collusion_not_deterred" in result.errors
        assert "shared_bond_insufficient" in result.errors

    def test_shared_bond_requires_scaling(self) -> None:
        env = _base_envelope(
            bond_model="shared",
            reward_model="per_head",
            coalition_size=5,
        )
        result = verify_collusion_envelope(env)
        assert result.required_shared_bond_e8 is not None
        assert result.required_shared_bond_e8 > 20_000_000

    def test_shared_bond_deterred_at_5x(self) -> None:
        env = _base_envelope(
            dispute_reward_e8=200_000_000,
            mev_uphold_dispute_e8=0,
            mev_reject_dispute_e8=10_000_000,
            dispute_bond_e8=150_000_000,
            prob_upheld_when_wrong_bps=1000,
            prob_upheld_when_correct_bps=9000,
            bond_model="shared",
            reward_model="per_head",
            coalition_size=5,
        )
        result = verify_collusion_envelope(env)
        assert result.collusion_deterred is True
        assert result.status == "accepted"

    def test_shared_bond_k1_equals_single(self) -> None:
        env = _base_envelope(
            bond_model="shared",
            reward_model="per_head",
            coalition_size=1,
        )
        result = verify_collusion_envelope(env)
        assert result.collusion_deterred == result.single_deterred

    def test_shared_split_combination_rejected(self) -> None:
        env = _base_envelope(
            bond_model="shared",
            reward_model="split",
            coalition_size=5,
        )
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert "unsupported_bond_reward_combination" in result.errors


# --- Boundary Cases ---


class TestBoundary:
    def test_equality_not_deterred(self) -> None:
        env = _base_envelope(
            dispute_reward_e8=190_000_000,
            mev_uphold_dispute_e8=0,
            mev_reject_dispute_e8=0,
            dispute_bond_e8=19_000_000,
            prob_upheld_when_wrong_bps=1000,
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=1,
        )
        result = verify_collusion_envelope(env)
        assert result.frivolous_scaled == result.bond_scaled
        assert result.single_deterred is False

    def test_one_above_boundary_deterred(self) -> None:
        env = _base_envelope(
            dispute_reward_e8=190_000_000,
            mev_uphold_dispute_e8=0,
            mev_reject_dispute_e8=0,
            dispute_bond_e8=20_000_000,
            prob_upheld_when_wrong_bps=1000,
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=1,
        )
        result = verify_collusion_envelope(env)
        assert result.frivolous_scaled < result.bond_scaled
        assert result.single_deterred is True

    def test_shared_bond_boundary(self) -> None:
        env = _base_envelope(
            dispute_bond_e8=95_000_000,
            bond_model="shared",
            reward_model="per_head",
            coalition_size=5,
        )
        result = verify_collusion_envelope(env)
        assert result.collusion_deterred is False

    def test_shared_bond_one_above_boundary(self) -> None:
        env = _base_envelope(
            dispute_bond_e8=96_000_000,
            bond_model="shared",
            reward_model="per_head",
            coalition_size=5,
        )
        result = verify_collusion_envelope(env)
        assert result.collusion_deterred is True

    def test_honest_not_profitable_detected(self) -> None:
        env = _base_envelope(
            dispute_reward_e8=1_000_000,
            mev_uphold_dispute_e8=0,
            dispute_bond_e8=20_000_000,
            prob_upheld_when_correct_bps=100,
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=1,
        )
        result = verify_collusion_envelope(env)
        assert "honest_challenge_not_profitable" in result.errors

    def test_p_f_zero_deterred_if_bond_positive(self) -> None:
        env = _base_envelope(
            prob_upheld_when_wrong_bps=0,
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=1,
        )
        result = verify_collusion_envelope(env)
        assert result.frivolous_scaled == 0 * (100_000_000 + 0) + 10000 * 10_000_000
        assert result.single_deterred is True

    def test_p_f_equals_bps(self) -> None:
        env = _base_envelope(
            prob_upheld_when_wrong_bps=10000,
            prob_upheld_when_correct_bps=10000,
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=1,
        )
        result = verify_collusion_envelope(env)
        assert result.frivolous_scaled == 10000 * 100_000_000 + 0 * 10_000_000

    def test_p_w_equals_p_f(self) -> None:
        env = _base_envelope(
            prob_upheld_when_wrong_bps=5000,
            prob_upheld_when_correct_bps=5000,
            bond_model="per_identity",
            reward_model="per_head",
            coalition_size=1,
        )
        result = verify_collusion_envelope(env)
        assert "prob_inversion" not in result.errors

    def test_bool_as_int_rejected(self) -> None:
        env = _base_envelope(dispute_bond_e8=True)
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("dispute_bond_e8" in e for e in result.errors)

    def test_max_coalition_accepted(self) -> None:
        env = _base_envelope(
            coalition_size=10_000,
            bond_model="per_identity",
            reward_model="per_head",
        )
        result = verify_collusion_envelope(env)
        assert result.coalition_size == 10_000
        assert result.collusion_invariant is True

    def test_coalition_above_max_rejected(self) -> None:
        env = _base_envelope(coalition_size=10_001)
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("coalition_size" in e for e in result.errors)

    def test_max_amount_accepted(self) -> None:
        # p_f=0 => frivolous_scaled = 0, always deterred if bond > 0.
        # Honest profitable needs p_w * G > bond * BPS.
        # G = reward + mev_uphold = 10^30 + 1, p_w = 10000:
        #   honest_gain = 10000 * (10^30 + 1) = 10^34 + 10000 > 10^34 = bond * BPS.
        env = _base_envelope(
            dispute_reward_e8=10**30,
            dispute_bond_e8=10**30,
            mev_uphold_dispute_e8=1,
            mev_reject_dispute_e8=0,
            prob_upheld_when_wrong_bps=0,
            prob_upheld_when_correct_bps=10000,
            bond_model="per_identity",
            reward_model="per_head",
        )
        result = verify_collusion_envelope(env)
        assert result.status == "accepted"

    def test_amount_above_max_rejected(self) -> None:
        env = _base_envelope(dispute_reward_e8=10**30 + 1)
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert any("dispute_reward_e8" in e for e in result.errors)

    def test_exact_required_shared_bond(self) -> None:
        # Base envelope: G = 100_000_000, M_rej = 10_000_000, p_f = 1000
        # frivolous_scaled = 1000*100_000_000 + 9000*10_000_000
        #                  = 100_000_000_000 + 90_000_000_000 = 190_000_000_000
        # k=5 shared: 5 * 190_000_000_000 = 950_000_000_000
        # bond_scaled = 20_000_000 * 10000 = 200_000_000_000
        # required = ceil(950_000_000_000 / 10000) = 95_000_000 + 1 = 95_000_001
        env = _base_envelope(
            bond_model="shared",
            reward_model="per_head",
            coalition_size=5,
        )
        result = verify_collusion_envelope(env)
        assert result.required_shared_bond_e8 == 95_000_001

    def test_k2_split_boundary(self) -> None:
        # frivolous_scaled = 190_000_000, bond_scaled = 190_000_000 (equality)
        # k=2 split: 190_000_000 < 2 * 190_000_000 = 380_000_000 -> deterred
        env = _base_envelope(
            dispute_reward_e8=190_000_000,
            mev_uphold_dispute_e8=0,
            mev_reject_dispute_e8=0,
            dispute_bond_e8=19_000_000,
            prob_upheld_when_wrong_bps=1000,
            prob_upheld_when_correct_bps=9000,
            bond_model="per_identity",
            reward_model="split",
            coalition_size=2,
        )
        result = verify_collusion_envelope(env)
        assert result.single_deterred is False
        assert result.collusion_deterred is True
        assert result.collusion_invariant is False


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
        assert "query_id" in envelope
        assert "bond_model" in envelope

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
        assert "query_id" in envelope

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
        env = _base_envelope(dispute_bond_e8=0)
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
        assert any("collusion_load_failed" in e for e in result["errors"])

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
