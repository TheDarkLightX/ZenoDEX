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
BPS_SCALE = 10_000


def _base_envelope(**overrides: object) -> dict[str, object]:
    env = sample_envelope()
    env.update(overrides)
    return env


def _write_temp_env(tmp_path: Path, env: dict[str, object]) -> Path:
    p = tmp_path / "envelope.json"
    p.write_text(json.dumps(env))
    return p


def _median_var_terms(
    *,
    reporter_count: int,
    controlled_reporter_count: int,
    critical_value_at_risk_e8: int,
    reporter_bond_required_e8: int,
    slash_fraction_bps: int,
    detection_probability_bps: int,
    future_value_lost_e8: int,
    deterrence_margin_bps: int,
) -> tuple[bool, int, int, int, int]:
    threshold = (reporter_count // 2) + 1
    median_control_possible = controlled_reporter_count >= threshold
    slash_amount = (reporter_bond_required_e8 * slash_fraction_bps) // BPS_SCALE
    expected_downside_scaled = detection_probability_bps * slash_amount
    expected_downside_scaled += future_value_lost_e8 * BPS_SCALE
    required_downside_scaled = critical_value_at_risk_e8 * (BPS_SCALE + deterrence_margin_bps)
    max_critical_value_at_risk = expected_downside_scaled // (BPS_SCALE + deterrence_margin_bps)
    return (
        median_control_possible,
        slash_amount,
        expected_downside_scaled,
        required_downside_scaled,
        max_critical_value_at_risk,
    )


# --- Schema Validation ---


class TestSchemaValidation:
    def test_missing_required_field_rejected(self) -> None:
        env = _base_envelope()
        del env["dispute_bond_e8"]
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert "missing_required_field:dispute_bond_e8" in result.errors

    def test_unknown_field_rejected(self) -> None:
        env = _base_envelope(hidden_signal=1)
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert "unknown_collusion_field:hidden_signal" in result.errors

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

    def test_controlled_reporter_count_cannot_exceed_reporter_count(self) -> None:
        env = _base_envelope(reporter_count=3, controlled_reporter_count=4)
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert "controlled_reporter_count_exceeds_reporter_count" in result.errors


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


# --- Median3 Critical Value-At-Risk Control ---


class TestMedian3ValueAtRiskControl:
    def test_two_controlled_reporters_rejected_when_downside_below_value_at_risk(self) -> None:
        env = _base_envelope(
            reporter_count=3,
            controlled_reporter_count=2,
            critical_value_at_risk_e8=200_000_000_000,
            reporter_bond_required_e8=250_000_000_000,
            slash_fraction_bps=5_000,
            detection_probability_bps=10_000,
            future_value_lost_e8=0,
            deterrence_margin_bps=2_000,
        )
        result = verify_collusion_envelope(env)
        assert result.status == "rejected"
        assert result.median_control_possible is True
        assert result.value_at_risk_downside_ok is False
        assert result.slash_amount_e8 == 125_000_000_000
        assert result.expected_downside_scaled == 1_250_000_000_000_000
        assert result.required_downside_scaled == 2_400_000_000_000_000
        assert result.max_critical_value_at_risk_e8 == 104_166_666_666
        assert "median3_control_budget_reaches_threshold" in result.errors
        assert "value_at_risk_downside_below_required_margin" in result.errors

    def test_two_controlled_reporters_accepted_when_bonded_downside_covers_value_at_risk(self) -> None:
        env = _base_envelope(
            reporter_count=3,
            controlled_reporter_count=2,
            critical_value_at_risk_e8=100_000_000_000,
            reporter_bond_required_e8=250_000_000_000,
            slash_fraction_bps=5_000,
            detection_probability_bps=10_000,
            future_value_lost_e8=0,
            deterrence_margin_bps=2_000,
        )
        result = verify_collusion_envelope(env)
        assert result.status == "accepted"
        assert result.median_control_possible is True
        assert result.value_at_risk_downside_ok is True
        assert result.expected_downside_scaled == 1_250_000_000_000_000
        assert result.required_downside_scaled == 1_200_000_000_000_000
        assert result.max_critical_value_at_risk_e8 == 104_166_666_666

    def test_single_controlled_reporter_does_not_own_median3(self) -> None:
        env = _base_envelope(
            reporter_count=3,
            controlled_reporter_count=1,
            critical_value_at_risk_e8=10**30,
        )
        result = verify_collusion_envelope(env)
        assert result.status == "accepted"
        assert result.median_control_threshold == 2
        assert result.median_control_possible is False

    def test_value_at_risk_boundary_is_exact_floor(self) -> None:
        terms = _median_var_terms(
            reporter_count=3,
            controlled_reporter_count=2,
            critical_value_at_risk_e8=0,
            reporter_bond_required_e8=250_000_000_000,
            slash_fraction_bps=5_000,
            detection_probability_bps=10_000,
            future_value_lost_e8=0,
            deterrence_margin_bps=2_000,
        )
        max_value_at_risk = terms[4]

        accepted = verify_collusion_envelope(
            _base_envelope(
                reporter_count=3,
                controlled_reporter_count=2,
                critical_value_at_risk_e8=max_value_at_risk,
            )
        )
        rejected = verify_collusion_envelope(
            _base_envelope(
                reporter_count=3,
                controlled_reporter_count=2,
                critical_value_at_risk_e8=max_value_at_risk + 1,
            )
        )

        assert accepted.status == "accepted"
        assert accepted.value_at_risk_downside_ok is True
        assert rejected.status == "rejected"
        assert rejected.value_at_risk_downside_ok is False
        assert "value_at_risk_downside_below_required_margin" in rejected.errors

    def test_bounded_value_at_risk_sweep_matches_independent_formula(self) -> None:
        cases = 0
        for reporter_count in [3, 5, 7]:
            for controlled_reporter_count in range(reporter_count + 1):
                for critical_value_at_risk in [0, 1, 50_000_000_000, 125_000_000_000]:
                    for reporter_bond in [1, 250_000_000_000]:
                        for slash_fraction in [0, 5_000, 10_000]:
                            for detection_probability in [0, 2_500, 10_000]:
                                for future_value_lost in [0, 25_000_000_000]:
                                    for deterrence_margin in [0, 2_000]:
                                        expected = _median_var_terms(
                                            reporter_count=reporter_count,
                                            controlled_reporter_count=controlled_reporter_count,
                                            critical_value_at_risk_e8=critical_value_at_risk,
                                            reporter_bond_required_e8=reporter_bond,
                                            slash_fraction_bps=slash_fraction,
                                            detection_probability_bps=detection_probability,
                                            future_value_lost_e8=future_value_lost,
                                            deterrence_margin_bps=deterrence_margin,
                                        )
                                        result = verify_collusion_envelope(
                                            _base_envelope(
                                                reporter_count=reporter_count,
                                                controlled_reporter_count=controlled_reporter_count,
                                                critical_value_at_risk_e8=critical_value_at_risk,
                                                reporter_bond_required_e8=reporter_bond,
                                                slash_fraction_bps=slash_fraction,
                                                detection_probability_bps=detection_probability,
                                                future_value_lost_e8=future_value_lost,
                                                deterrence_margin_bps=deterrence_margin,
                                            )
                                        )
                                        (
                                            median_control_possible,
                                            slash_amount,
                                            expected_downside,
                                            required_downside,
                                            max_value_at_risk,
                                        ) = expected
                                        downside_ok = expected_downside >= required_downside

                                        assert result.median_control_possible is median_control_possible
                                        assert result.slash_amount_e8 == slash_amount
                                        assert result.expected_downside_scaled == expected_downside
                                        assert result.required_downside_scaled == required_downside
                                        assert result.max_critical_value_at_risk_e8 == max_value_at_risk
                                        assert result.value_at_risk_downside_ok is downside_ok
                                        if median_control_possible and not downside_ok:
                                            assert result.status == "rejected"
                                            assert "median3_control_budget_reaches_threshold" in result.errors
                                            assert (
                                                "value_at_risk_downside_below_required_margin"
                                                in result.errors
                                            )
                                        else:
                                            assert "median3_control_budget_reaches_threshold" not in result.errors
                                            assert (
                                                "value_at_risk_downside_below_required_margin"
                                                not in result.errors
                                            )
                                        cases += 1

        assert cases == 5184


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
