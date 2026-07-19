"""Tests for the autonomous-governance trajectory runner and verifier.

The runner's value is owning the cross-step threading (applied state,
trajectory_used, previous_approved_deltas, last_update_epoch) that single-step
callers must otherwise hand-thread, plus invariant tripwires and a
self-contained, independently verifiable receipt. Tests are grouped:

- threading proofs (cooldown owned by the runner; hold does not reset cooldown;
  budget accumulation and screening; anti-oscillation via threaded deltas);
- fail-closed behavior (structural whole-trajectory no-ops; per-step rejection
  no-ops; poisoned policy bounded by the gates across a whole trajectory);
- invariant tripwires (pure audit function, non-vacuous corruption cases; a
  corrupted inner step halts the trajectory and the suspect state is refused);
- verification (tamper matrix: every forgery class must fail verification,
  including re-hashed forgeries that only deterministic replay can catch).
"""

from __future__ import annotations

import json
import os
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest

import src.integration.autonomous_governance_trajectory as trajectory_module
from src.integration.autonomous_governance_q_policy import (
    policy_content_hash_v1,
)
from src.integration.autonomous_governance_trajectory import (
    _TRAJECTORY_HASH_TAG,
    AUTONOMOUS_GOVERNANCE_TRAJECTORY_ADMISSION_SCHEMA_V1,
    AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1,
    MAX_TRAJECTORY_STEPS_V1,
    STATUS_COMPLETED,
    STATUS_HALTED_INVARIANT_BREACH,
    STATUS_REJECTED_STRUCTURAL,
    _audit_step_transition,
    _chain_genesis,
    _chain_link,
    admit_verified_autonomous_governance_surface_trajectory_v1,
    run_autonomous_governance_surface_trajectory_v1,
    verify_autonomous_governance_surface_trajectory_v1,
)
from src.integration.zeno_ledger_v0 import hash_v0
from tools.support.autonomous_governance_policy_samples import (
    sample_autonomous_governance_surface_q_policy_v1,
)


def _surface_state(**overrides: int) -> dict[str, int]:
    state = {
        "fee_bps": 30,
        "buyburn_bps": 6_000,
        "stakers_bps": 0,
        "reserve_bps": 2_000,
        "hosts_bps": 2_000,
        "mcr_bps": 11_000,
        "ccr_bps": 15_000,
        "staker_bps": 5_000,
        "funding_cap_bps": 120,
    }
    state.update(overrides)
    return state


def _hot_observation(**overrides: int) -> dict[str, int]:
    obs = {
        "observed_price_bps": 10_500,
        "target_price_bps": 10_000,
        "volatility_bps": 250,
        "divergence_bps": 10,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": 5_000,
    }
    obs.update(overrides)
    return obs


def _calm_observation(**overrides: int) -> dict[str, int]:
    obs = {
        "observed_price_bps": 10_000,
        "target_price_bps": 10_000,
        "volatility_bps": 25,
        "divergence_bps": 5,
        "freshness_lag_epochs": 0,
        "liquidity_depth_bps": 5_000,
    }
    obs.update(overrides)
    return obs


def _step(observation: dict[str, int], current_epoch: int) -> dict[str, Any]:
    return {
        "observation": observation,
        "current_epoch": current_epoch,
        "proposal_epoch": current_epoch - 24,
    }


def _budget(**overrides: int) -> dict[str, int]:
    budget = {
        "fee_bps": 50,
        "funding_cap_bps": 25,
        "buyburn_bps": 200,
        "reserve_bps": 200,
    }
    budget.update(overrides)
    return budget


def _sample_policy(**safety_overrides: Any) -> dict[str, Any]:
    policy = deepcopy(sample_autonomous_governance_surface_q_policy_v1())
    if safety_overrides:
        policy["safety"].update(safety_overrides)
        policy["policy_hash"] = policy_content_hash_v1(policy)
    return policy


def _run(**overrides: Any) -> dict[str, Any]:
    policy = overrides.pop("policy", None) or _sample_policy()
    kwargs: dict[str, Any] = {
        "policy": policy,
        "initial_surface_state": _surface_state(),
        "steps": [
            _step(_hot_observation(), 100),
            _step(_calm_observation(), 125),
            _step(_hot_observation(), 150),
        ],
        "expected_policy_hash": policy["policy_hash"],
        "trajectory_budget": _budget(),
    }
    kwargs.update(overrides)
    return run_autonomous_governance_surface_trajectory_v1(**kwargs)


# --------------------------------------------------------------------------- #
# Threading proofs
# --------------------------------------------------------------------------- #
def test_trajectory_threads_state_and_records_realized_deltas() -> None:
    receipt = _run()

    assert receipt["status"] == STATUS_COMPLETED
    assert receipt["ok"] is True
    assert receipt["admitted_count"] == 3
    assert receipt["rejected_count"] == 0
    assert receipt["state_changing_count"] == 2
    assert receipt["final_state"]["fee_bps"] == 50
    assert receipt["final_state"]["funding_cap_bps"] == 110
    assert receipt["cumulative_realized_drift"]["fee_bps"] == 20
    assert receipt["cumulative_realized_drift"]["funding_cap_bps"] == -20 + 10
    assert receipt["trajectory_used_final"]["fee_bps"] == 20
    assert receipt["trajectory_used_final"]["funding_cap_bps"] == 10
    assert receipt["previous_approved_deltas_final"]["fee_bps"] == 10
    assert receipt["last_update_epoch_final"] == 150
    assert [record["action_id"] for record in receipt["steps"]] == [
        "raise_fee_10_tighten_funding_5",
        "hold",
        "raise_fee_10_tighten_funding_5",
    ]
    assert all(record["adopted"] for record in receipt["steps"])
    assert all(receipt["invariant_report"].values())
    # Steps chain: state_after of step k is state_before of step k+1.
    for previous, current in zip(receipt["steps"], receipt["steps"][1:], strict=False):
        assert current["state_before"] == previous["state_after"]


def test_trajectory_owns_cooldown_threading() -> None:
    # min_cooldown_epochs=30 with steps 25 epochs apart: the second step must be
    # rejected even though the CALLER never threads last_update_epoch. A
    # forgetful single-step caller would have admitted it.
    receipt = _run(policy=_sample_policy(min_cooldown_epochs=30))

    steps = receipt["steps"]
    assert steps[0]["admitted"] is True
    assert steps[0]["state_changing"] is True
    assert steps[1]["admitted"] is False
    assert "cooldown_not_elapsed" in steps[1]["step_errors"]
    assert steps[1]["state_after"] == steps[0]["state_after"]
    assert steps[2]["admitted"] is True
    assert receipt["ok"] is True
    assert receipt["admitted_count"] == 2
    assert receipt["rejected_count"] == 1


def test_admitted_hold_does_not_reset_cooldown() -> None:
    # Factory replay semantics: only a state-changing approval resets the
    # cooldown clock. A hold admitted at epoch 131 must not push the next
    # allowed movement out to 161.
    receipt = _run(
        policy=_sample_policy(min_cooldown_epochs=30),
        steps=[
            _step(_hot_observation(), 100),
            _step(_calm_observation(), 131),
            _step(_hot_observation(), 135),
        ],
    )

    steps = receipt["steps"]
    assert steps[0]["state_changing"] is True
    assert steps[1]["admitted"] is True
    assert steps[1]["action_id"] == "hold"
    assert steps[1]["state_changing"] is False
    assert steps[1]["last_update_epoch_after"] == 100
    assert steps[2]["admitted"] is True
    assert steps[2]["state_changing"] is True
    assert receipt["last_update_epoch_final"] == 135


def test_trajectory_budget_binds_in_top_scored_mode() -> None:
    receipt = _run(
        trajectory_budget=_budget(fee_bps=15),
        steps=[_step(_hot_observation(), 100), _step(_hot_observation(), 125)],
    )

    steps = receipt["steps"]
    assert steps[0]["admitted"] is True
    assert steps[0]["realized_deltas"]["fee_bps"] == 10
    assert steps[1]["admitted"] is False
    assert "trajectory_budget_exceeded:fee_bps" in steps[1]["step_errors"]
    assert steps[1]["state_after"] == steps[0]["state_after"]
    assert receipt["trajectory_used_final"]["fee_bps"] == 10
    assert receipt["ok"] is True


def test_trajectory_budget_screens_to_hold_in_first_admissible_mode() -> None:
    policy = _sample_policy()
    policy["selection"] = {"mode": "first_admissible"}
    policy["policy_hash"] = policy_content_hash_v1(policy)

    receipt = _run(
        policy=policy,
        trajectory_budget=_budget(fee_bps=15),
        steps=[_step(_hot_observation(), 100), _step(_hot_observation(), 125)],
    )

    steps = receipt["steps"]
    assert steps[0]["action_id"] == "raise_fee_10_tighten_funding_5"
    assert steps[1]["admitted"] is True
    assert steps[1]["action_id"] == "hold"
    assert steps[1]["state_changing"] is False
    assert receipt["trajectory_used_final"]["fee_bps"] == 10
    assert receipt["trajectory_used_final"]["funding_cap_bps"] == 5


def test_carry_in_trajectory_used_screens_immediately() -> None:
    policy = _sample_policy()
    policy["selection"] = {"mode": "first_admissible"}
    policy["policy_hash"] = policy_content_hash_v1(policy)

    receipt = _run(
        policy=policy,
        trajectory_budget=_budget(fee_bps=15),
        trajectory_used={"fee_bps": 10},
        steps=[_step(_hot_observation(), 100)],
    )

    assert receipt["steps"][0]["action_id"] == "hold"
    assert receipt["trajectory_used_final"]["fee_bps"] == 10
    assert receipt["carry_in"]["trajectory_used"] == {"fee_bps": 10}


def test_anti_oscillation_uses_threaded_previous_deltas() -> None:
    policy = {
        "schema": "zenodex.autonomous_governance.q_policy.v1",
        "policy_id": "trajectory_anti_oscillation_policy",
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
        },
        "selection": {
            "mode": "first_admissible",
            "anti_oscillation": {"enabled": True, "parameters": ["fee_bps"]},
        },
        "state_bins": {"deviation_bps": [25, 100, 300]},
        "actions": [
            {"id": "hold", "deltas": {}},
            {"id": "lower_fee_10", "deltas": {"fee_bps": -10}},
            {"id": "raise_fee_10", "deltas": {"fee_bps": 10}},
        ],
        "q_layers": [
            {
                "id": "deviation_pressure",
                "features": ["deviation_bps"],
                "q_table": {
                    "0": {"lower_fee_10": 10, "hold": 0, "raise_fee_10": -10},
                    "3": {"raise_fee_10": 10, "hold": 0, "lower_fee_10": -10},
                },
            }
        ],
    }
    policy["policy_hash"] = policy_content_hash_v1(policy)

    receipt = _run(
        policy=policy,
        trajectory_budget={"fee_bps": 50},
        steps=[_step(_hot_observation(), 100), _step(_calm_observation(), 125)],
    )

    steps = receipt["steps"]
    assert steps[0]["action_id"] == "raise_fee_10"
    assert steps[0]["realized_deltas"]["fee_bps"] == 10
    # Step 2's table prefers lower_fee_10, but the runner threaded the +10
    # approved delta, so the reversal is screened and hold is selected.
    assert steps[1]["action_id"] == "hold"
    assert steps[1]["admitted"] is True
    assert receipt["previous_approved_deltas_final"]["fee_bps"] == 10


# --------------------------------------------------------------------------- #
# Fail-closed behavior
# --------------------------------------------------------------------------- #
def test_rejected_step_is_noop_and_trajectory_continues() -> None:
    receipt = _run(
        initial_surface_state=_surface_state(fee_bps=995),
        steps=[_step(_hot_observation(), 100), _step(_calm_observation(), 125)],
    )

    steps = receipt["steps"]
    assert steps[0]["admitted"] is False
    assert "governance_surface_gate_rejected:fee" in steps[0]["step_errors"]
    assert steps[0]["state_after"] == steps[0]["state_before"]
    assert steps[1]["admitted"] is True
    assert steps[1]["action_id"] == "hold"
    assert receipt["ok"] is True
    assert receipt["final_state"]["fee_bps"] == 995
    assert receipt["invariant_report"]["reject_is_noop_ok"] is True


def test_poisoned_policy_stays_bounded_across_whole_trajectory() -> None:
    # A policy whose only action exceeds the per-revision step cap can never
    # move state, no matter how many epochs it runs.
    policy = {
        "schema": "zenodex.autonomous_governance.q_policy.v1",
        "policy_id": "poisoned_fee_jump_policy",
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
        },
        "state_bins": {"deviation_bps": [25, 100, 300]},
        "actions": [{"id": "fee_jump_60", "deltas": {"fee_bps": 60}}],
        "q_layers": [
            {
                "id": "always_jump",
                "features": ["deviation_bps"],
                "q_table": {str(bin_index): {"fee_jump_60": 1} for bin_index in range(4)},
            }
        ],
    }
    policy["policy_hash"] = policy_content_hash_v1(policy)

    receipt = _run(
        policy=policy,
        trajectory_budget={"fee_bps": 1_000},
        steps=[_step(_hot_observation(), 100 + 25 * index) for index in range(4)],
    )

    assert receipt["ok"] is True
    assert receipt["admitted_count"] == 0
    assert receipt["rejected_count"] == 4
    assert receipt["final_state"] == receipt["initial_state"]
    assert all(
        "governance_surface_gate_rejected:fee" in record["step_errors"]
        for record in receipt["steps"]
    )


def _structural_case_kwargs() -> dict[str, Any]:
    policy = _sample_policy()
    return {
        "policy": policy,
        "initial_surface_state": _surface_state(),
        "steps": [_step(_hot_observation(), 100), _step(_calm_observation(), 125)],
        "expected_policy_hash": policy["policy_hash"],
        "trajectory_budget": _budget(),
    }


def test_structural_rejection_cases_are_total_noops() -> None:
    cases: list[tuple[str, dict[str, Any], str]] = []

    kwargs = _structural_case_kwargs()
    kwargs["steps"] = []
    cases.append(("empty_steps", kwargs, "trajectory_steps_empty"))

    kwargs = _structural_case_kwargs()
    kwargs["steps"][1]["current_epoch"] = 100
    cases.append(
        ("non_increasing_epochs", kwargs, "trajectory_epochs_not_strictly_increasing:1")
    )

    kwargs = _structural_case_kwargs()
    kwargs["steps"][0]["surprise"] = 1
    cases.append(("extra_step_field", kwargs, "trajectory_step_unknown_field:0:surprise"))

    kwargs = _structural_case_kwargs()
    del kwargs["steps"][0]["proposal_epoch"]
    cases.append(
        ("missing_step_field", kwargs, "trajectory_step_missing_field:0:proposal_epoch")
    )

    kwargs = _structural_case_kwargs()
    kwargs["steps"][0]["observation"] = {"volatility_bps": "high"}
    cases.append(
        (
            "non_int_observation_value",
            kwargs,
            "trajectory_step_observation_value_invalid:0:volatility_bps",
        )
    )

    kwargs = _structural_case_kwargs()
    kwargs["expected_policy_hash"] = "0x" + "00" * 32
    cases.append(("pin_mismatch", kwargs, "policy_hash_mismatch"))

    kwargs = _structural_case_kwargs()
    kwargs["expected_policy_hash"] = ""
    cases.append(("pin_required", kwargs, "expected_policy_hash_required"))

    kwargs = _structural_case_kwargs()
    incomplete = deepcopy(kwargs["policy"])
    del incomplete["safety"]["min_cooldown_epochs"]
    incomplete["policy_hash"] = policy_content_hash_v1(incomplete)
    kwargs["policy"] = incomplete
    kwargs["expected_policy_hash"] = incomplete["policy_hash"]
    cases.append(
        ("incomplete_safety", kwargs, "incomplete_safety_envelope:min_cooldown_epochs")
    )

    kwargs = _structural_case_kwargs()
    kwargs["trajectory_budget"] = {"fee_bps": 50}
    cases.append(("movable_without_budget", kwargs, "trajectory_budget_missing:buyburn_bps"))

    kwargs = _structural_case_kwargs()
    kwargs["initial_surface_state"] = _surface_state() | {"fee_bps": "30"}
    cases.append(("malformed_initial_state", kwargs, "initial_fee_bps must be an int"))

    kwargs = _structural_case_kwargs()
    kwargs["trajectory_used"] = {"fee_bps": -1}
    cases.append(("negative_carry_used", kwargs, "trajectory_used.fee_bps must be"))

    kwargs = _structural_case_kwargs()
    kwargs["previous_approved_deltas"] = {"fee_bps": True}
    cases.append(
        ("bool_carry_delta", kwargs, "previous_approved_deltas.fee_bps must be an int")
    )

    kwargs = _structural_case_kwargs()
    kwargs["steps"] = [
        _step(_hot_observation(), 100 + index)
        for index in range(MAX_TRAJECTORY_STEPS_V1 + 1)
    ]
    cases.append(("too_many_steps", kwargs, "trajectory_steps_exceed_max"))

    for name, case_kwargs, expected_error in cases:
        receipt = run_autonomous_governance_surface_trajectory_v1(**case_kwargs)
        assert receipt["status"] == STATUS_REJECTED_STRUCTURAL, name
        assert receipt["ok"] is False, name
        assert receipt["steps"] == (), name
        assert receipt["final_state"] == receipt["initial_state"], name
        assert any(expected_error in str(error) for error in receipt["errors"]), (
            name,
            receipt["errors"],
        )


def test_trajectory_is_deterministic() -> None:
    first = _run()
    second = _run()

    assert first["trajectory_hash"] == second["trajectory_hash"]


def test_chain_links_recompute() -> None:
    receipt = _run()

    chain = _chain_genesis(
        policy_hash=receipt["policy_hash"],
        initial_state=receipt["initial_state"],
        carry_in=receipt["carry_in"],
        trajectory_budget=receipt["trajectory_budget"],
    )
    assert chain == receipt["chain_genesis"]
    for record in receipt["steps"]:
        chain = _chain_link(
            prev=chain, index=record["index"], step_hash=record["step_hash"]
        )
        assert chain == record["chain_hash"]
    assert chain == receipt["chain_head"]


# --------------------------------------------------------------------------- #
# Invariant tripwires
# --------------------------------------------------------------------------- #
def _clean_admit_audit_kwargs() -> dict[str, Any]:
    before = _surface_state()
    after = _surface_state(fee_bps=40)
    used_before = {name: 0 for name in before}
    used_after = dict(used_before)
    used_after["fee_bps"] = 10
    return {
        "admitted": True,
        "state_before": before,
        "applied_state": after,
        "proposed_state": dict(after),
        "used_before": used_before,
        "used_after": used_after,
        "trajectory_budget": {"fee_bps": 50},
    }


def test_audit_clean_admitted_transition_has_no_breaches() -> None:
    assert _audit_step_transition(**_clean_admit_audit_kwargs()) == ()


def test_audit_detects_reject_that_mutates_state() -> None:
    kwargs = _clean_admit_audit_kwargs()
    kwargs["admitted"] = False
    kwargs["used_after"] = dict(kwargs["used_before"])

    breaches = _audit_step_transition(**kwargs)

    assert "invariant_breach:reject_not_noop:fee_bps" in breaches


def test_audit_detects_applied_diverging_from_proposed() -> None:
    kwargs = _clean_admit_audit_kwargs()
    kwargs["proposed_state"] = _surface_state(fee_bps=35)

    breaches = _audit_step_transition(**kwargs)

    assert "invariant_breach:admitted_not_proposed:fee_bps" in breaches


def test_audit_detects_fee_step_cap_breach() -> None:
    kwargs = _clean_admit_audit_kwargs()
    jumped = _surface_state(fee_bps=90)
    kwargs["applied_state"] = jumped
    kwargs["proposed_state"] = dict(jumped)
    kwargs["used_after"] = dict(kwargs["used_before"])
    kwargs["used_after"]["fee_bps"] = 60

    breaches = _audit_step_transition(**kwargs)

    assert "invariant_breach:fee_step" in breaches


def test_audit_detects_router_sum_break() -> None:
    kwargs = _clean_admit_audit_kwargs()
    broken = _surface_state(fee_bps=40, buyburn_bps=6_100)
    kwargs["applied_state"] = broken
    kwargs["proposed_state"] = dict(broken)
    kwargs["used_after"] = {
        name: (10 if name == "fee_bps" else 100 if name == "buyburn_bps" else 0)
        for name in broken
    }

    breaches = _audit_step_transition(**kwargs)

    assert "invariant_breach:router_sum" in breaches


def test_audit_detects_used_accounting_drift() -> None:
    kwargs = _clean_admit_audit_kwargs()
    kwargs["used_after"] = dict(kwargs["used_before"])  # forgot to add |delta|

    breaches = _audit_step_transition(**kwargs)

    assert "invariant_breach:used_accounting:fee_bps" in breaches


def test_audit_detects_budget_overrun() -> None:
    kwargs = _clean_admit_audit_kwargs()
    kwargs["trajectory_budget"] = {"fee_bps": 5}

    breaches = _audit_step_transition(**kwargs)

    assert "invariant_breach:budget_exceeded:fee_bps" in breaches


def test_audit_detects_malformed_applied_state() -> None:
    kwargs = _clean_admit_audit_kwargs()
    del kwargs["applied_state"]["fee_bps"]

    breaches = _audit_step_transition(**kwargs)

    assert "invariant_breach:applied_state_shape:fee_bps" in breaches


def test_corrupted_inner_step_halts_trajectory_and_refuses_state(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Simulate semantic drift of the inner commit step (the tripwires' threat
    # model): an "admitted" outcome whose applied state jumps the fee cap. The
    # runner must record the breach, refuse the suspect state, and halt.
    initial = _surface_state()
    jumped = _surface_state(fee_bps=initial["fee_bps"] + 60)

    def corrupted_commit(**_: Any) -> dict[str, Any]:
        return {
            "admitted": True,
            "reason": "admitted",
            "applied_state": jumped,
            "proposed_state": dict(jumped),
            "receipt": {"errors": (), "action_id": "corrupted_jump"},
            "step_hash": "0x" + "11" * 32,
            "receipt_hash": "0x" + "22" * 32,
        }

    monkeypatch.setattr(trajectory_module, "_COMMIT_SURFACE_STEP", corrupted_commit)
    receipt = _run(steps=[_step(_hot_observation(), 100), _step(_hot_observation(), 125)])

    assert receipt["status"] == STATUS_HALTED_INVARIANT_BREACH
    assert receipt["ok"] is False
    assert receipt["halted_early"] is True
    assert receipt["halt_index"] == 0
    assert receipt["step_count"] == 1
    assert "invariant_breach:fee_step" in receipt["errors"]
    assert receipt["final_state"] == initial
    assert receipt["invariant_report"]["surface_caps_ok"] is False


def test_corrupted_runner_output_fails_independent_verification(
    monkeypatch: pytest.MonkeyPatch,
) -> None:
    # Even if a corrupted runner emitted a self-consistent receipt, the
    # verifier replays through the REAL import-bound commit path and refuses it.
    jumped = _surface_state(fee_bps=90)

    def corrupted_commit(**_: Any) -> dict[str, Any]:
        return {
            "admitted": True,
            "reason": "admitted",
            "applied_state": jumped,
            "proposed_state": dict(jumped),
            "receipt": {"errors": (), "action_id": "corrupted_jump"},
            "step_hash": "0x" + "11" * 32,
            "receipt_hash": "0x" + "22" * 32,
        }

    monkeypatch.setattr(trajectory_module, "_COMMIT_SURFACE_STEP", corrupted_commit)
    forged = _run(steps=[_step(_hot_observation(), 100)])
    monkeypatch.undo()

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=forged, policy=_sample_policy()
    )

    assert verification["ok"] is False
    assert "replay_divergence" in verification["errors"]


# --------------------------------------------------------------------------- #
# Verification
# --------------------------------------------------------------------------- #
def _rehash(receipt: dict[str, Any]) -> dict[str, Any]:
    body = dict(receipt)
    body.pop("trajectory_hash", None)
    return {**body, "trajectory_hash": hash_v0(_TRAJECTORY_HASH_TAG, body)}


def _as_json_obj(receipt: dict[str, Any]) -> dict[str, Any]:
    return json.loads(json.dumps(receipt))


def test_verify_accepts_faithful_receipt_and_json_round_trip() -> None:
    policy = _sample_policy()
    receipt = _run(policy=policy)

    direct = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )
    round_tripped = verify_autonomous_governance_surface_trajectory_v1(
        receipt=_as_json_obj(receipt), policy=policy
    )

    assert direct["ok"] is True
    assert direct["errors"] == ()
    assert direct["trajectory_ok"] is True
    assert all(direct["checks"].values())
    assert round_tripped["ok"] is True


def test_verify_accepts_receipt_with_rejected_steps() -> None:
    # Verification proves fidelity, not success: a faithful record of
    # fail-closed rejections verifies.
    policy = _sample_policy()
    receipt = _run(
        policy=policy,
        initial_surface_state=_surface_state(fee_bps=995),
        steps=[_step(_hot_observation(), 100)],
    )
    assert receipt["rejected_count"] == 1

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is True
    assert verification["trajectory_ok"] is True


def test_verify_rejects_tampered_hash() -> None:
    policy = _sample_policy()
    receipt = _run(policy=policy)
    receipt = dict(receipt)
    receipt["trajectory_hash"] = "0x" + "00" * 32

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is False
    assert "trajectory_hash_mismatch" in verification["errors"]


def test_verify_rejects_tampered_body_without_rehash() -> None:
    policy = _sample_policy()
    receipt = _as_json_obj(_run(policy=policy))
    receipt["final_state"]["fee_bps"] = 999

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is False
    assert "trajectory_hash_mismatch" in verification["errors"]


def test_verify_rejects_rehashed_state_forgery_via_replay() -> None:
    # The forger recomputes the receipt hash over the tampered body, so only
    # deterministic replay can catch the lie.
    policy = _sample_policy()
    receipt = _as_json_obj(_run(policy=policy))
    receipt["steps"][2]["state_after"]["fee_bps"] = 45
    receipt["final_state"]["fee_bps"] = 45
    receipt = _rehash(receipt)

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is False
    assert verification["checks"]["trajectory_hash_binds_body"] is True
    assert "replay_divergence" in verification["errors"]


def test_verify_rejects_rehashed_admitted_bit_forgery() -> None:
    policy = _sample_policy()
    receipt = _as_json_obj(
        _run(
            policy=policy,
            initial_surface_state=_surface_state(fee_bps=995),
            steps=[_step(_hot_observation(), 100)],
        )
    )
    receipt["steps"][0]["admitted"] = True
    receipt["admitted_count"] = 1
    receipt["rejected_count"] = 0
    receipt = _rehash(receipt)

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is False
    assert "replay_divergence" in verification["errors"]


def test_verify_rejects_rehashed_input_observation_forgery() -> None:
    policy = _sample_policy()
    receipt = _as_json_obj(_run(policy=policy))
    receipt["input_steps"][0]["observation"]["volatility_bps"] = 9_999
    receipt = _rehash(receipt)

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is False
    assert "replay_divergence" in verification["errors"]


def test_verify_rejects_rehashed_chain_forgery() -> None:
    policy = _sample_policy()
    receipt = _as_json_obj(_run(policy=policy))
    receipt["steps"][1]["chain_hash"] = "0x" + "ab" * 32
    receipt = _rehash(receipt)

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is False
    assert "chain_link_mismatch:1" in verification["errors"]


def test_equal_explicit_and_policy_budgets_yield_identical_receipts() -> None:
    # Codex r1 MED: the receipt must not carry a budget-provenance label a
    # verifier cannot independently re-derive. Resolution: behaviorally
    # identical inputs produce IDENTICAL receipts, so there is no provenance
    # claim left to forge. Whether the budget came from the artifact or an
    # operator argument is answered by comparing the receipt's budget with the
    # policy's — the only verifiable form of that question.
    policy = _sample_policy()
    policy["selection"] = {
        "mode": "first_admissible",
        "trajectory_budget": {"enabled": True, "limits": _budget()},
    }
    policy["policy_hash"] = policy_content_hash_v1(policy)
    steps = [_step(_hot_observation(), 100), _step(_calm_observation(), 125)]

    from_policy = _run(policy=policy, steps=list(steps), trajectory_budget=None)
    from_argument = _run(policy=policy, steps=list(steps), trajectory_budget=_budget())

    assert from_policy["trajectory_hash"] == from_argument["trajectory_hash"]
    assert "trajectory_budget_source" not in from_policy
    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=from_policy, policy=policy
    )
    assert verification["ok"] is True


def test_verify_rejects_injected_budget_source_field() -> None:
    # The removed provenance label must not be reintroducible by a forger: an
    # injected field changes the canonical body, and replay recomputes a body
    # without it.
    policy = _sample_policy()
    receipt = _as_json_obj(_run(policy=policy))
    receipt["trajectory_budget_source"] = "policy_selection"
    receipt = _rehash(receipt)

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is False
    assert "replay_divergence" in verification["errors"]


def test_verify_rejects_wrong_policy_artifact() -> None:
    policy = _sample_policy()
    receipt = _run(policy=policy)
    other_policy = _sample_policy(max_volatility_bps=999)

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=other_policy
    )

    assert verification["ok"] is False
    assert "policy_hash_mismatch" in verification["errors"]


def test_verify_rejects_structural_rejection_receipts() -> None:
    policy = _sample_policy()
    receipt = _run(policy=policy, steps=[])
    assert receipt["status"] == STATUS_REJECTED_STRUCTURAL

    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )

    assert verification["ok"] is False
    assert "structural_rejection_receipt_not_verifiable" in verification["errors"]


def test_verify_fails_closed_on_malformed_receipts() -> None:
    policy = _sample_policy()

    not_mapping = verify_autonomous_governance_surface_trajectory_v1(
        receipt=[], policy=policy  # type: ignore[arg-type]
    )
    assert not_mapping["ok"] is False
    assert "trajectory_receipt_must_be_object" in not_mapping["errors"]

    missing_hash = verify_autonomous_governance_surface_trajectory_v1(
        receipt={"schema": AUTONOMOUS_GOVERNANCE_TRAJECTORY_SCHEMA_V1}, policy=policy
    )
    assert missing_hash["ok"] is False
    assert "trajectory_hash_missing" in missing_hash["errors"]

    wrong_schema = verify_autonomous_governance_surface_trajectory_v1(
        receipt={"schema": "nope", "trajectory_hash": "0x" + "00" * 32}, policy=policy
    )
    assert wrong_schema["ok"] is False
    assert "trajectory_schema_invalid" in wrong_schema["errors"]


# --------------------------------------------------------------------------- #
# Admission / refuse-loop
# --------------------------------------------------------------------------- #
def test_admission_accepts_verified_pinned_trajectory() -> None:
    policy = _sample_policy()
    receipt = _run(policy=policy)

    admission = admit_verified_autonomous_governance_surface_trajectory_v1(
        receipt=receipt,
        policy=policy,
        expected_policy_hash=policy["policy_hash"],
        expected_initial_state=_surface_state(),
        expected_final_state=receipt["final_state"],
    )

    assert admission["schema"] == AUTONOMOUS_GOVERNANCE_TRAJECTORY_ADMISSION_SCHEMA_V1
    assert admission["ok"] is True
    assert admission["accepted"] is True
    assert admission["errors"] == ()
    assert all(admission["checks"].values())
    assert admission["accepted_final_state"] == receipt["final_state"]
    assert admission["trajectory_hash"] == receipt["trajectory_hash"]


def test_admission_rejects_external_policy_pin_mismatch() -> None:
    policy = _sample_policy()
    receipt = _run(policy=policy)

    admission = admit_verified_autonomous_governance_surface_trajectory_v1(
        receipt=receipt,
        policy=policy,
        expected_policy_hash="0x" + "00" * 32,
    )

    assert admission["accepted"] is False
    assert admission["checks"]["verification_ok"] is True
    assert "expected_policy_hash_mismatch:policy" in admission["errors"]
    assert "expected_policy_hash_mismatch:receipt_policy" in admission["errors"]
    assert "expected_policy_hash_mismatch:receipt_expected" in admission["errors"]


def test_admission_rejects_state_anchor_mismatch() -> None:
    policy = _sample_policy()
    receipt = _run(policy=policy)

    admission = admit_verified_autonomous_governance_surface_trajectory_v1(
        receipt=receipt,
        policy=policy,
        expected_policy_hash=policy["policy_hash"],
        expected_initial_state=_surface_state(fee_bps=31),
        expected_final_state=receipt["final_state"],
    )

    assert admission["accepted"] is False
    assert admission["checks"]["verification_ok"] is True
    assert admission["checks"]["initial_state_matches"] is False
    assert "initial_state_mismatch" in admission["errors"]


def test_admission_rejects_rehashed_forgery() -> None:
    policy = _sample_policy()
    receipt = _as_json_obj(_run(policy=policy))
    receipt["final_state"]["fee_bps"] = 45
    receipt = _rehash(receipt)

    admission = admit_verified_autonomous_governance_surface_trajectory_v1(
        receipt=receipt,
        policy=policy,
        expected_policy_hash=policy["policy_hash"],
    )

    assert admission["accepted"] is False
    assert admission["checks"]["verification_ok"] is False
    assert "trajectory_verification_failed" in admission["errors"]
    assert "replay_divergence" in admission["verification"]["errors"]


def test_admission_checks_previous_chain_head_when_expected() -> None:
    policy = _sample_policy()
    previous = "0x" + "12" * 32
    receipt = _run(policy=policy, previous_chain_head=previous)

    accepted = admit_verified_autonomous_governance_surface_trajectory_v1(
        receipt=receipt,
        policy=policy,
        expected_policy_hash=policy["policy_hash"],
        expected_previous_chain_head=previous,
    )
    assert accepted["accepted"] is True

    rejected = admit_verified_autonomous_governance_surface_trajectory_v1(
        receipt=receipt,
        policy=policy,
        expected_policy_hash=policy["policy_hash"],
        expected_previous_chain_head="0x" + "34" * 32,
    )
    assert rejected["accepted"] is False
    assert "previous_chain_head_mismatch" in rejected["errors"]


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def test_cli_trajectory_run_and_verify(tmp_path: Path) -> None:
    import subprocess
    import sys

    bundle_path = tmp_path / "trajectory-bundle.json"
    sample = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "sample",
            "--trajectory",
            "--output",
            str(bundle_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert sample.returncode == 0, sample.stderr

    run = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "trajectory",
            str(bundle_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert run.returncode == 0, run.stderr
    receipt = json.loads(run.stdout)
    assert receipt["status"] == STATUS_COMPLETED
    assert receipt["admitted_count"] == 3
    assert receipt["state_changing_count"] == 2

    bundle = json.loads(bundle_path.read_text(encoding="utf-8"))
    verify_path = tmp_path / "verify-bundle.json"
    verify_path.write_text(
        json.dumps({"policy": bundle["policy"], "trajectory_receipt": receipt}),
        encoding="utf-8",
    )
    verify = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "verify-trajectory",
            str(verify_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert verify.returncode == 0, verify.stderr
    verification = json.loads(verify.stdout)
    assert verification["ok"] is True
    assert verification["trajectory_ok"] is True

    admit_path = tmp_path / "admit-bundle.json"
    admit_path.write_text(
        json.dumps(
            {
                "policy": bundle["policy"],
                "trajectory_receipt": receipt,
                "expected_policy_hash": bundle["expected_policy_hash"],
                "expected_initial_state": bundle["initial_surface_state"],
                "expected_final_state": receipt["final_state"],
            }
        ),
        encoding="utf-8",
    )
    admit = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "admit-trajectory",
            str(admit_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert admit.returncode == 0, admit.stderr
    admission = json.loads(admit.stdout)
    assert admission["accepted"] is True
    assert admission["accepted_final_state"] == receipt["final_state"]

    # Tampered receipt must exit 2 with replay divergence.
    receipt["steps"][0]["state_after"]["fee_bps"] = 31
    forged = dict(receipt)
    forged.pop("trajectory_hash", None)
    forged["trajectory_hash"] = hash_v0(_TRAJECTORY_HASH_TAG, forged)
    verify_path.write_text(
        json.dumps({"policy": bundle["policy"], "trajectory_receipt": forged}),
        encoding="utf-8",
    )
    tampered = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "verify-trajectory",
            str(verify_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert tampered.returncode == 2, tampered.stdout
    assert "replay_divergence" in tampered.stdout

    admit_path.write_text(
        json.dumps(
            {
                "policy": bundle["policy"],
                "trajectory_receipt": forged,
                "expected_policy_hash": bundle["expected_policy_hash"],
            }
        ),
        encoding="utf-8",
    )
    tampered_admit = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "admit-trajectory",
            str(admit_path),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert tampered_admit.returncode == 2, tampered_admit.stdout
    assert "trajectory_verification_failed" in tampered_admit.stdout


# --------------------------------------------------------------------------- #
# Optional differential against a real factory artifact
# --------------------------------------------------------------------------- #
_FACTORY_ARTIFACT = os.environ.get("ZENODEX_FACTORY_POLICY_ARTIFACT", "")


@pytest.mark.skipif(
    not _FACTORY_ARTIFACT or not Path(_FACTORY_ARTIFACT).is_file(),
    reason="set ZENODEX_FACTORY_POLICY_ARTIFACT to a frozen factory policy to run",
)
def test_factory_artifact_trajectory_runs_and_verifies() -> None:
    policy = json.loads(Path(_FACTORY_ARTIFACT).read_text(encoding="utf-8"))

    receipt = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=[
            _step(_hot_observation(), 100),
            _step(_calm_observation(), 125),
            _step(_hot_observation(), 150),
        ],
        expected_policy_hash=str(policy.get("policy_hash", "")),
    )

    assert receipt["status"] == STATUS_COMPLETED
    assert receipt["ok"] is True
    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=receipt, policy=policy
    )
    assert verification["ok"] is True
