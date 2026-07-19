"""Frozen PI-policy artifact runtime tests (production-shape proposer)."""

from __future__ import annotations

from typing import Any

from src.integration.autonomous_governance_pi_policy import (
    evaluate_autonomous_governance_pi_policy_step_v1,
    normalize_autonomous_governance_pi_policy_v1,
    pi_policy_content_hash_v1,
)
from src.integration.autonomous_governance_q_policy import (
    governance_surface_context_hash_v1,
)
from tools.support.autonomous_governance_policy_samples import (
    sample_autonomous_governance_pi_policy_v1,
)

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
    policy = sample_autonomous_governance_pi_policy_v1()
    kwargs: dict[str, Any] = {
        "policy": policy,
        "committed_surface_state": dict(_SURFACE_STATE),
        "measured": 100,
        "prev_error": 0,
        "approved": True,
        "proposal_epoch": 10,
        "current_epoch": 100,
        "expected_policy_hash": pi_policy_content_hash_v1(policy),
    }
    kwargs.update(overrides)
    return evaluate_autonomous_governance_pi_policy_step_v1(**kwargs)


class TestArtifactValidation:
    def test_sample_artifact_is_valid_and_pinnable(self) -> None:
        policy = sample_autonomous_governance_pi_policy_v1()
        normalized, errors = normalize_autonomous_governance_pi_policy_v1(policy)
        assert errors == []
        assert normalized["surface"] == "fee_bps"
        assert pi_policy_content_hash_v1(policy) == pi_policy_content_hash_v1(normalized)

    def test_float_gain_rejected(self) -> None:
        policy = sample_autonomous_governance_pi_policy_v1()
        policy["kp_num"] = 1.0
        _, errors = normalize_autonomous_governance_pi_policy_v1(policy)
        assert "pi_policy_kp_num_must_be_plain_int" in errors

    def test_bool_field_rejected(self) -> None:
        policy = sample_autonomous_governance_pi_policy_v1()
        policy["deadband"] = True
        _, errors = normalize_autonomous_governance_pi_policy_v1(policy)
        assert "pi_policy_deadband_must_be_plain_int" in errors

    def test_zero_denominator_rejected(self) -> None:
        policy = sample_autonomous_governance_pi_policy_v1()
        policy["ki_den"] = 0
        _, errors = normalize_autonomous_governance_pi_policy_v1(policy)
        assert "pi_policy_config_invalid" in errors

    def test_unknown_surface_rejected(self) -> None:
        policy = sample_autonomous_governance_pi_policy_v1()
        policy["surface"] = "mcr_bps"  # collateral pair is not a scalar PI surface
        _, errors = normalize_autonomous_governance_pi_policy_v1(policy)
        assert "pi_policy_surface_unsupported" in errors

    def test_unknown_keys_rejected(self) -> None:
        policy = sample_autonomous_governance_pi_policy_v1()
        policy["extra"] = 1
        _, errors = normalize_autonomous_governance_pi_policy_v1(policy)
        assert "pi_policy_unknown_keys" in errors


class TestPinDiscipline:
    def test_missing_pin_is_error_not_default(self) -> None:
        result = _step(expected_policy_hash=None)
        assert result["admitted"] is False
        assert "pi_expected_policy_hash_required" in result["errors"]
        assert result["final_state"] == result["committed_state"]

    def test_wrong_pin_refused(self) -> None:
        result = _step(expected_policy_hash="0x" + "00" * 32)
        assert result["admitted"] is False
        assert "pi_expected_policy_hash_mismatch" in result["errors"]

    def test_context_hash_binding_refuses_substituted_anchor(self) -> None:
        bound = governance_surface_context_hash_v1(
            surface_state=_SURFACE_STATE,
            current_epoch=100,
            proposal_epoch=10,
        )
        tampered = dict(_SURFACE_STATE)
        tampered["fee_bps"] = 900  # proposer-asserted curr
        result = _step(
            committed_surface_state=tampered,
            expected_committed_context_hash=bound,
        )
        assert result["admitted"] is False
        assert "pi_committed_context_hash_mismatch" in result["errors"]

    def test_context_hash_binding_accepts_true_anchor(self) -> None:
        bound = governance_surface_context_hash_v1(
            surface_state=_SURFACE_STATE,
            current_epoch=100,
            proposal_epoch=10,
        )
        result = _step(expected_committed_context_hash=bound)
        assert "pi_committed_context_hash_mismatch" not in result["errors"]

    def test_negative_context_epochs_fail_closed_without_raising(self) -> None:
        result = _step(last_update_epoch=-1)
        assert result["admitted"] is False
        assert "pi_last_update_epoch_must_be_nonnegative" in result["errors"]
        assert result["final_state"] == result["committed_state"]

        result = _step(current_epoch=-1)
        assert result["admitted"] is False
        assert "pi_current_epoch_must_be_nonnegative" in result["errors"]
        assert result["final_state"] == result["committed_state"]


class TestControllerSemantics:
    def test_admitted_step_moves_surface_and_advances_state(self) -> None:
        # error = measured - setpoint = 100; delta = 100//4 + 100//8 = 37; but
        # the fee gate's step limit is 50, so candidate 30+37=67 is admitted.
        result = _step()
        assert result["admitted"] is True, result["errors"]
        assert result["candidate"] == 67
        assert result["final_state"]["fee_bps"] == 67
        assert result["prev_error_out"] == 100

    def test_deadband_freezes_controller(self) -> None:
        result = _step(measured=1)  # |error| = 1 <= deadband 2
        assert result["deadband_frozen"] is True
        assert result["candidate"] == result["curr"]
        assert result["prev_error_out"] == result["prev_error_in"]

    def test_poisoned_setpoint_is_bounded_by_gate_total_noop(self) -> None:
        # A hostile measured value drives a huge candidate; the artifact clamp
        # allows it (out_hi=1000) but the exact fee gate's per-revision step
        # (|delta| <= 50) rejects it. Reject is a TOTAL no-op: parameter AND
        # controller state are unchanged.
        result = _step(measured=10_000, prev_error=0)
        assert result["gate_admitted"] is False
        assert result["admitted"] is False
        assert result["final_state"] == result["committed_state"]
        assert result["prev_error_out"] == result["prev_error_in"]

    def test_unapproved_step_rejected_by_gate(self) -> None:
        result = _step(approved=False)
        assert result["admitted"] is False
        assert result["final_state"] == result["committed_state"]

    def test_timelock_immature_rejected_by_gate(self) -> None:
        result = _step(proposal_epoch=95, current_epoch=100)  # delay 5 < 24
        assert result["admitted"] is False

    def test_determinism_same_inputs_same_step_hash(self) -> None:
        first = _step()
        second = _step()
        assert first["step_hash"] == second["step_hash"]

    def test_non_int_measured_fail_closed(self) -> None:
        result = _step(measured=1.5)
        assert result["admitted"] is False
        assert "pi_measured_must_be_plain_int" in result["errors"]
        assert result["final_state"] == result["committed_state"]
