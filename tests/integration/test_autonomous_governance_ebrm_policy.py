"""Frozen EBRM-policy artifact runtime tests."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Any

from src.integration.autonomous_governance_ebrm_policy import (
    ebrm_policy_content_hash_v1,
    evaluate_autonomous_governance_ebrm_policy_step_v1,
    normalize_autonomous_governance_ebrm_policy_v1,
)
from src.integration.autonomous_governance_q_policy import (
    governance_surface_context_hash_v1,
)
from tools.support.autonomous_governance_policy_samples import (
    sample_autonomous_governance_ebrm_policy_v1,
)

ROOT = Path(__file__).resolve().parents[2]

_SURFACE_STATE: dict[str, int] = {
    "fee_bps": 30,
    "buyburn_bps": 5000,
    "stakers_bps": 3000,
    "reserve_bps": 1500,
    "hosts_bps": 500,
    "mcr_bps": 11000,
    "ccr_bps": 15000,
    "staker_bps": 5000,
    "funding_cap_bps": 100,
}


def _step(**overrides: Any) -> dict[str, Any]:
    policy = sample_autonomous_governance_ebrm_policy_v1()
    surface_state = dict(_SURFACE_STATE)
    proposal_epoch = 10
    current_epoch = 100
    kwargs: dict[str, Any] = {
        "policy": policy,
        "committed_surface_state": surface_state,
        "observation": {
            "observed_price_bps": 10_500,
            "target_price_bps": 10_000,
            "deviation_bps": 500,
            "volatility_bps": 250,
            "divergence_bps": 10,
            "freshness_lag_epochs": 0,
            "liquidity_depth_bps": 5_000,
        },
        "approved": True,
        "proposal_epoch": proposal_epoch,
        "current_epoch": current_epoch,
        "expected_policy_hash": ebrm_policy_content_hash_v1(policy),
        "expected_committed_context_hash": governance_surface_context_hash_v1(
            surface_state=surface_state,
            current_epoch=current_epoch,
            proposal_epoch=proposal_epoch,
        ),
    }
    kwargs.update(overrides)
    return evaluate_autonomous_governance_ebrm_policy_step_v1(**kwargs)


class TestArtifactValidation:
    def test_sample_artifact_is_valid_and_pinnable(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        normalized, errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
        assert errors == []
        assert normalized["surface"] == "fee_bps"
        assert ebrm_policy_content_hash_v1(policy) == ebrm_policy_content_hash_v1(policy)

    def test_energy_model_is_required_and_validated(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        policy["energy_model"] = {"targets": {"0": 30}, "w_track": 0, "w_move": 0}
        _, errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
        assert "ebrm_energy_model_invalid" in errors

    def test_training_domain_bounds_are_required(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        policy.pop("feature_bounds")
        _, errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
        assert "ebrm_feature_bounds_must_be_object" in errors

    def test_training_domain_bounds_must_cover_features(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        policy["feature_bounds"] = {}
        _, errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
        assert "ebrm_feature_bounds_missing:deviation_bps" in errors

    def test_unknown_feature_rejected(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        policy["features"] = ["not_a_feature"]
        _, errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
        assert "ebrm_feature_unknown:not_a_feature" in errors

    def test_duplicate_feature_rejected(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        policy["features"] = ["deviation_bps", "deviation_bps"]
        _, errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
        assert "ebrm_feature_duplicate:deviation_bps" in errors

    def test_unsorted_bins_rejected(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        policy["state_bins"] = {"deviation_bps": [100, 25]}
        _, errors = normalize_autonomous_governance_ebrm_policy_v1(policy)
        assert "ebrm_state_bins_deviation_bps_must_be_strictly_ascending" in errors


class TestPinAndContextBinding:
    def test_missing_pin_is_error_not_default(self) -> None:
        result = _step(expected_policy_hash=None)
        assert result["admitted"] is False
        assert "ebrm_expected_policy_hash_required" in result["errors"]
        assert result["final_state"] == result["committed_state"]

    def test_wrong_pin_refused(self) -> None:
        result = _step(expected_policy_hash="0x" + "00" * 32)
        assert result["admitted"] is False
        assert "ebrm_expected_policy_hash_mismatch" in result["errors"]

    def test_malformed_pin_refused(self) -> None:
        result = _step(expected_policy_hash="not-a-hash")
        assert result["admitted"] is False
        assert "ebrm_expected_policy_hash_invalid" in result["errors"]

    def test_missing_context_hash_is_error_not_default(self) -> None:
        result = _step(expected_committed_context_hash=None)
        assert result["admitted"] is False
        assert "ebrm_expected_committed_context_hash_required" in result["errors"]
        assert result["final_state"] == result["committed_state"]

    def test_malformed_context_hash_refused(self) -> None:
        result = _step(expected_committed_context_hash="not-a-hash")
        assert result["admitted"] is False
        assert "ebrm_expected_committed_context_hash_invalid" in result["errors"]

    def test_context_hash_binding_refuses_substituted_anchor(self) -> None:
        bound = governance_surface_context_hash_v1(
            surface_state=_SURFACE_STATE,
            current_epoch=100,
            proposal_epoch=10,
        )
        tampered = dict(_SURFACE_STATE)
        tampered["fee_bps"] = 900
        result = _step(
            committed_surface_state=tampered,
            expected_committed_context_hash=bound,
        )
        assert result["admitted"] is False
        assert "ebrm_committed_context_hash_mismatch" in result["errors"]

    def test_context_hash_binding_accepts_true_anchor(self) -> None:
        bound = governance_surface_context_hash_v1(
            surface_state=_SURFACE_STATE,
            current_epoch=100,
            proposal_epoch=10,
        )
        result = _step(expected_committed_context_hash=bound)
        assert result["admitted"] is True, result["errors"]

    def test_negative_context_epochs_fail_closed_without_raising(self) -> None:
        result = _step(last_update_epoch=-1)
        assert result["admitted"] is False
        assert "ebrm_last_update_epoch_must_be_nonnegative" in result["errors"]
        assert result["final_state"] == result["committed_state"]

        result = _step(current_epoch=-1)
        assert result["admitted"] is False
        assert "ebrm_current_epoch_must_be_nonnegative" in result["errors"]
        assert result["final_state"] == result["committed_state"]


class TestEBRMStepSemantics:
    def test_admitted_step_uses_energy_argmin_and_gate(self) -> None:
        result = _step()
        assert result["admitted"] is True, result["errors"]
        assert result["state_key"] == "3"
        assert result["target"] == 67
        assert result["candidate"] == 67
        assert result["energy"] == 0
        assert result["final_state"]["fee_bps"] == 67
        assert "does_not_train_ebrm_online" in result["not_claimed"]

    def test_missing_energy_target_is_fail_closed_noop(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        policy["energy_model"]["targets"].pop("3")
        result = _step(policy=policy, expected_policy_hash=ebrm_policy_content_hash_v1(policy))
        assert result["admitted"] is False
        assert "ebrm_energy_target_missing" in result["errors"]
        assert result["final_state"] == result["committed_state"]

    def test_high_target_is_constrained_to_exact_gate_band(self) -> None:
        policy = sample_autonomous_governance_ebrm_policy_v1()
        policy["energy_model"]["targets"]["3"] = 1000
        result = _step(policy=policy, expected_policy_hash=ebrm_policy_content_hash_v1(policy))
        assert result["candidate"] == 80
        assert result["gate_admitted"] is True
        assert result["admitted"] is True

    def test_unapproved_step_rejected_by_gate(self) -> None:
        result = _step(approved=False)
        assert result["admitted"] is False
        assert result["final_state"] == result["committed_state"]

    def test_timelock_immature_rejected_by_gate(self) -> None:
        result = _step(proposal_epoch=95, current_epoch=100)
        assert result["admitted"] is False
        assert result["final_state"] == result["committed_state"]

    def test_non_int_observation_fail_closed(self) -> None:
        observation = {
            "observed_price_bps": 10_500,
            "target_price_bps": 10_000,
            "deviation_bps": 1.5,
            "volatility_bps": 250,
            "divergence_bps": 10,
            "freshness_lag_epochs": 0,
            "liquidity_depth_bps": 5_000,
        }
        result = _step(observation=observation)
        assert result["admitted"] is False
        assert "ebrm_observation_deviation_bps_must_be_plain_int" in result["errors"]
        assert result["final_state"] == result["committed_state"]

    def test_out_of_training_domain_observation_fail_closed(self) -> None:
        result = _step(
            observation={
                "observed_price_bps": 30_000,
                "target_price_bps": 10_000,
                "deviation_bps": 20_000,
                "volatility_bps": 250,
                "divergence_bps": 10,
                "freshness_lag_epochs": 0,
                "liquidity_depth_bps": 5_000,
            }
        )
        assert result["admitted"] is False
        assert "ebrm_feature_out_of_training_domain:deviation_bps" in result["errors"]
        assert result["final_state"] == result["committed_state"]

    def test_cli_sample_and_ebrm_step_replays_frozen_artifact(self, tmp_path: Path) -> None:
        bundle_path = tmp_path / "ebrm-policy-bundle.json"
        sample = subprocess.run(
            [
                sys.executable,
                str(ROOT / "tools" / "autonomous_governance_q_policy.py"),
                "sample",
                "--ebrm",
                "--output",
                str(bundle_path),
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        assert sample.returncode == 0, sample.stderr

        step = subprocess.run(
            [
                sys.executable,
                str(ROOT / "tools" / "autonomous_governance_q_policy.py"),
                "ebrm-step",
                str(bundle_path),
            ],
            cwd=ROOT,
            check=False,
            capture_output=True,
            text=True,
        )
        assert step.returncode == 0, step.stderr
        result = json.loads(step.stdout)
        assert result["admitted"] is True, result["errors"]
        assert result["candidate"] == 67
        assert "does_not_use_energy_as_acceptance_predicate" in result["not_claimed"]
