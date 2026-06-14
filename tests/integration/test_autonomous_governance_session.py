"""Cross-trajectory session continuity: the boundary is the attack surface.

Coverage map:

- continuation derives carry EXCLUSIVELY from a fully re-verified parent
  (happy path, budget exhaustion across the boundary, cooldown continuity,
  oscillation continuity);
- every refusal is named and fail-closed (tampered parent, non-extendable
  parent, policy-hash mismatch, epoch replay, malformed inputs);
- the session verifier refuses every boundary forgery: naive carry reset,
  linkage-without-carry (true chain head + reset budget), genesis with
  carried-in state, budget swap, policy swap, structural members;
- independent session accounting (drift conservation, used monotonicity,
  drift <= used <= budget) and receipt determinism / JSON round-trips.
"""

from __future__ import annotations

import json
import subprocess
import sys
from copy import deepcopy
from pathlib import Path
from typing import Any

import pytest

import src.integration.autonomous_governance_trajectory as trajectory_module
from src.integration.autonomous_governance_q_policy import (
    policy_content_hash_v1,
)
from src.integration.autonomous_governance_session import (
    continue_autonomous_governance_surface_trajectory_v1,
    verify_autonomous_governance_surface_session_v1,
)
from src.integration.autonomous_governance_trajectory import (
    STATUS_COMPLETED,
    STATUS_REJECTED_STRUCTURAL,
    run_autonomous_governance_surface_trajectory_v1,
    verify_autonomous_governance_surface_trajectory_v1,
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


def _observation(deviation_bps: int = 400, **overrides: int) -> dict[str, int]:
    obs = {
        "observed_price_bps": 10_000 + deviation_bps,
        "target_price_bps": 10_000,
        "volatility_bps": 100,
        "divergence_bps": 10,
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


def _pressure_steps(count: int, first_epoch: int) -> list[dict[str, Any]]:
    return [_step(_observation(), first_epoch + index) for index in range(count)]


def _calm_steps(count: int, first_epoch: int) -> list[dict[str, Any]]:
    return [
        _step(_observation(deviation_bps=0, volatility_bps=20), first_epoch + index)
        for index in range(count)
    ]


_BUDGET = {"fee_bps": 50, "funding_cap_bps": 25, "buyburn_bps": 200, "reserve_bps": 200}


def _policy(**safety_overrides: Any) -> dict[str, Any]:
    policy = {
        "schema": "zenodex.autonomous_governance.q_policy.v1",
        "policy_id": "session_test_policy_v1",
        "version": 1,
        "safety": {
            "max_freshness_lag_epochs": 2,
            "max_divergence_bps": 75,
            "max_volatility_bps": 1_000,
            "min_liquidity_depth_bps": 1_000,
            "min_cooldown_epochs": 1,
            "emergency_pause": False,
            **safety_overrides,
        },
        "selection": {
            "mode": "first_admissible",
            "anti_oscillation": {"enabled": True, "parameters": ["fee_bps"]},
            "trajectory_budget": {"enabled": True, "limits": dict(_BUDGET)},
        },
        "state_bins": {
            "deviation_bps": [25, 100, 300],
            "volatility_bps": [50, 200, 500],
            "liquidity_depth_bps": [1_000, 3_000],
        },
        "actions": [
            {"id": "hold", "deltas": {}},
            {"id": "raise_fee_10", "deltas": {"fee_bps": 10}},
            {"id": "lower_fee_10", "deltas": {"fee_bps": -10}},
        ],
        "q_layers": [
            {
                "id": "price_deviation_pressure",
                "features": ["deviation_bps"],
                "q_table": {
                    "0": {"lower_fee_10": 6, "hold": 3},
                    "1": {"hold": 3},
                    "2": {"raise_fee_10": 5, "hold": 1},
                    "3": {"raise_fee_10": 8, "hold": 1},
                },
            },
        ],
    }
    return {**policy, "policy_hash": policy_content_hash_v1(policy)}


def _genesis(
    policy: dict[str, Any],
    *,
    steps: list[dict[str, Any]] | None = None,
    initial: dict[str, int] | None = None,
) -> dict[str, Any]:
    return run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=initial or _surface_state(),
        steps=steps if steps is not None else _pressure_steps(3, 100),
        expected_policy_hash=str(policy["policy_hash"]),
    )


def _continue(
    policy: dict[str, Any],
    parent: dict[str, Any],
    steps: list[dict[str, Any]],
) -> dict[str, Any]:
    return continue_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        previous_receipt=parent,
        steps=steps,
        expected_policy_hash=str(policy["policy_hash"]),
    )


# ---------------------------------------------------------------------------
# Continuation: carry is derived from the verified parent, nothing else.
# ---------------------------------------------------------------------------


def test_continuation_carries_all_threading_state_and_links_chain() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    child = _continue(policy, genesis, _pressure_steps(3, 103))

    assert child["status"] == STATUS_COMPLETED and child["ok"] is True
    assert child["carry_in"]["previous_chain_head"] == genesis["chain_head"]
    assert child["initial_state"] == genesis["final_state"]
    assert child["carry_in"]["trajectory_used"] == genesis["trajectory_used_final"]
    assert (
        child["carry_in"]["previous_approved_deltas"]
        == genesis["previous_approved_deltas_final"]
    )
    assert child["carry_in"]["last_update_epoch"] == genesis["last_update_epoch_final"]
    assert child["trajectory_budget"] == genesis["trajectory_budget"]

    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, child],
        policy=policy,
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert verification["ok"] is True, verification["errors"]
    assert all(verification["checks"].values())
    assert verification["receipt_count"] == 2
    assert verification["session_chain_head"] == child["chain_head"]


def test_budget_does_not_refill_at_the_boundary() -> None:
    policy = _policy()
    # 5 pressure steps spend the whole 50 bps fee budget in the genesis.
    genesis = _genesis(policy, steps=_pressure_steps(6, 100))
    assert genesis["trajectory_used_final"]["fee_bps"] == _BUDGET["fee_bps"]

    child = _continue(policy, genesis, _pressure_steps(4, 106))
    assert child["ok"] is True
    # Exhausted budget means the continuation can only hold: zero fee movement.
    assert child["cumulative_realized_drift"]["fee_bps"] == 0
    assert child["trajectory_used_final"]["fee_bps"] == _BUDGET["fee_bps"]

    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, child], policy=policy
    )
    assert verification["ok"] is True
    assert verification["session_drift"]["fee_bps"] == _BUDGET["fee_bps"]
    assert verification["session_used_final"]["fee_bps"] == _BUDGET["fee_bps"]


def test_naive_resegmentation_spends_the_budget_twice_and_is_refused() -> None:
    policy = _policy()
    genesis = _genesis(policy, steps=_pressure_steps(6, 100))
    naive_second = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis["final_state"]),
        steps=_pressure_steps(6, 106),
        expected_policy_hash=str(policy["policy_hash"]),
    )
    # The attack is real: both receipts verify individually, and the combined
    # drift is double the per-trajectory budget.
    assert (
        verify_autonomous_governance_surface_trajectory_v1(
            receipt=naive_second, policy=policy
        )["ok"]
        is True
    )
    combined_drift = (
        naive_second["final_state"]["fee_bps"] - genesis["initial_state"]["fee_bps"]
    )
    assert combined_drift == 2 * _BUDGET["fee_bps"]

    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, naive_second], policy=policy
    )
    assert verification["ok"] is False
    assert verification["checks"]["boundary_carry_ok"] is False
    for family in (
        "session_previous_chain_head_mismatch:1",
        "session_carry_used_mismatch:1",
        "session_carry_oscillation_history_mismatch:1",
        "session_carry_cooldown_mismatch:1",
    ):
        assert family in verification["errors"]


def test_linkage_without_carry_is_not_continuity() -> None:
    policy = _policy()
    genesis = _genesis(policy, steps=_pressure_steps(6, 100))
    forged = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis["final_state"]),
        steps=_pressure_steps(6, 106),
        expected_policy_hash=str(policy["policy_hash"]),
        previous_chain_head=str(genesis["chain_head"]),  # true head, reset carry
    )
    assert (
        verify_autonomous_governance_surface_trajectory_v1(
            receipt=forged, policy=policy
        )["ok"]
        is True
    )
    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, forged], policy=policy
    )
    assert verification["ok"] is False
    assert verification["checks"]["boundary_carry_ok"] is False
    assert "session_carry_used_mismatch:1" in verification["errors"]
    # The independent accounting also catches the evasion directly.
    assert "session_drift_exceeds_used:fee_bps" in verification["errors"]


def test_cooldown_carries_across_the_boundary() -> None:
    policy = _policy(min_cooldown_epochs=3)
    genesis = _genesis(policy, steps=_pressure_steps(1, 100))
    assert genesis["last_update_epoch_final"] == 100

    child = _continue(
        policy, genesis, [_step(_observation(), 101), _step(_observation(), 102), _step(_observation(), 103)]
    )
    assert child["ok"] is True
    rejected = [record for record in child["steps"] if record["admitted"] is False]
    assert [record["current_epoch"] for record in rejected] == [101, 102]
    assert all(
        "cooldown_not_elapsed" in record["step_errors"] for record in rejected
    )
    admitted = [record for record in child["steps"] if record["admitted"] is True]
    assert [record["current_epoch"] for record in admitted] == [103]

    # The naive operator who resets the carry trades again immediately.
    naive = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis["final_state"]),
        steps=[_step(_observation(), 101)],
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert naive["steps"][0]["admitted"] is True


def test_oscillation_history_carries_across_the_boundary() -> None:
    policy = _policy()
    genesis = _genesis(policy, steps=_pressure_steps(2, 100))  # raises: +fee
    child = _continue(policy, genesis, _calm_steps(2, 102))  # wants: -fee

    assert child["ok"] is True
    assert child["cumulative_realized_drift"]["fee_bps"] == 0  # reversals screened
    assert all(record["action_id"] == "hold" for record in child["steps"])

    naive = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis["final_state"]),
        steps=_calm_steps(2, 102),
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert naive["cumulative_realized_drift"]["fee_bps"] < 0  # flip admitted


def test_continuation_refuses_epoch_replay() -> None:
    policy = _policy()
    genesis = _genesis(policy, steps=_pressure_steps(3, 100))
    child = _continue(policy, genesis, _pressure_steps(3, 102))  # 102 <= 102
    assert child["status"] == STATUS_REJECTED_STRUCTURAL
    assert "session_epochs_not_strictly_increasing" in child["errors"]

    fresh = _continue(policy, genesis, _pressure_steps(3, 103))
    assert fresh["status"] == STATUS_COMPLETED


def test_continuation_refuses_tampered_parent() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    tampered = dict(genesis)
    tampered["final_state"] = {
        **dict(genesis["final_state"]),
        "fee_bps": int(genesis["final_state"]["fee_bps"]) + 10,
    }
    child = _continue(policy, tampered, _pressure_steps(3, 103))
    assert child["status"] == STATUS_REJECTED_STRUCTURAL
    assert "session_parent_receipt_unverified" in child["errors"]
    assert any(
        error.startswith("session_parent_verification:") for error in child["errors"]
    )


@pytest.mark.parametrize("parent", [None, 42, "receipt", ["receipt"]])
def test_continuation_refuses_non_mapping_parent(parent: object) -> None:
    policy = _policy()
    child = continue_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        previous_receipt=parent,
        steps=_pressure_steps(3, 103),
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert child["status"] == STATUS_REJECTED_STRUCTURAL
    assert "session_parent_receipt_unverified" in child["errors"]


def test_continuation_refuses_halted_parent(monkeypatch: pytest.MonkeyPatch) -> None:
    policy = _policy()
    jumped = _surface_state(fee_bps=_surface_state()["fee_bps"] + 60)

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
    halted = _genesis(policy)
    monkeypatch.undo()
    assert halted["status"] == "halted_invariant_breach"

    child = _continue(policy, halted, _pressure_steps(3, 103))
    assert child["status"] == STATUS_REJECTED_STRUCTURAL
    # A halted receipt replays faithfully only under the corrupted commit; the
    # honest replay diverges, so the parent is refused as unverified.
    assert "session_parent_receipt_unverified" in child["errors"]


def test_continuation_refuses_policy_hash_mismatch() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    other = _policy()
    other.pop("policy_hash")
    other["version"] = 2
    other = {**other, "policy_hash": policy_content_hash_v1(other)}

    child = continue_autonomous_governance_surface_trajectory_v1(
        policy=other,
        previous_receipt=genesis,
        steps=_pressure_steps(3, 103),
        expected_policy_hash=str(other["policy_hash"]),
    )
    assert child["status"] == STATUS_REJECTED_STRUCTURAL
    # The parent does not verify under the other policy artifact.
    assert "session_parent_receipt_unverified" in child["errors"]


def test_continuation_requires_expected_policy_hash() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    child = continue_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        previous_receipt=genesis,
        steps=_pressure_steps(3, 103),
        expected_policy_hash="",
    )
    assert child["status"] == STATUS_REJECTED_STRUCTURAL
    assert "expected_policy_hash_required" in child["errors"]


def test_continuation_is_deterministic() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    first = _continue(policy, genesis, _pressure_steps(3, 103))
    second = _continue(policy, genesis, _pressure_steps(3, 103))
    assert first["trajectory_hash"] == second["trajectory_hash"]
    assert first == second


def test_continuation_receipt_survives_json_round_trip() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    child = _continue(policy, genesis, _pressure_steps(3, 103))
    round_tripped = json.loads(json.dumps(child))
    verification = verify_autonomous_governance_surface_trajectory_v1(
        receipt=round_tripped, policy=policy
    )
    assert verification["ok"] is True
    session_verification = verify_autonomous_governance_surface_session_v1(
        receipts=[json.loads(json.dumps(genesis)), round_tripped], policy=policy
    )
    assert session_verification["ok"] is True


# ---------------------------------------------------------------------------
# The previous_chain_head input binding on the runner itself.
# ---------------------------------------------------------------------------


def test_runner_without_chain_head_is_byte_identical_to_pre_session_format() -> None:
    policy = _policy()
    receipt = _genesis(policy)
    assert "previous_chain_head" not in receipt["carry_in"]
    linked = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=_pressure_steps(3, 100),
        expected_policy_hash=str(policy["policy_hash"]),
        previous_chain_head="0x" + "ab" * 32,
    )
    assert linked["carry_in"]["previous_chain_head"] == "0x" + "ab" * 32
    assert linked["trajectory_hash"] != receipt["trajectory_hash"]
    assert linked["chain_genesis"] != receipt["chain_genesis"]


@pytest.mark.parametrize("bad_head", ["", 42, b"0xab"])
def test_runner_refuses_invalid_previous_chain_head(bad_head: object) -> None:
    policy = _policy()
    receipt = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=_pressure_steps(3, 100),
        expected_policy_hash=str(policy["policy_hash"]),
        previous_chain_head=bad_head,  # type: ignore[arg-type]
    )
    assert receipt["status"] == STATUS_REJECTED_STRUCTURAL
    assert "previous_chain_head_invalid" in receipt["errors"]


# ---------------------------------------------------------------------------
# Session verifier refusals beyond boundary carry.
# ---------------------------------------------------------------------------


def test_session_verifier_accepts_trivial_genesis_session() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis], policy=policy
    )
    assert verification["ok"] is True
    assert verification["checks"]["genesis_fresh_ok"] is True


@pytest.mark.parametrize(
    ("kwargs", "expected_error"),
    [
        (
            {"trajectory_used": {"fee_bps": 10}},
            "session_genesis_used_not_zero",
        ),
        (
            {"previous_approved_deltas": {"fee_bps": 10}},
            "session_genesis_oscillation_history_not_empty",
        ),
        ({"last_update_epoch": 50}, "session_genesis_cooldown_carry_not_none"),
        (
            {"previous_chain_head": "0x" + "ab" * 32},
            "session_genesis_carries_chain_head",
        ),
    ],
)
def test_session_verifier_refuses_non_fresh_genesis(
    kwargs: dict[str, Any], expected_error: str
) -> None:
    policy = _policy()
    receipt = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=_pressure_steps(3, 100),
        expected_policy_hash=str(policy["policy_hash"]),
        **kwargs,
    )
    assert receipt["status"] == STATUS_COMPLETED
    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[receipt], policy=policy
    )
    assert verification["ok"] is False
    assert expected_error in verification["errors"]
    assert verification["checks"]["genesis_fresh_ok"] is False


def test_session_verifier_refuses_budget_swap_midsession() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    inflated = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=dict(genesis["final_state"]),
        steps=_pressure_steps(3, 103),
        expected_policy_hash=str(policy["policy_hash"]),
        last_update_epoch=genesis["last_update_epoch_final"],
        trajectory_budget={**dict(genesis["trajectory_budget"]), "fee_bps": 5_000},
        trajectory_used=dict(genesis["trajectory_used_final"]),
        previous_approved_deltas=dict(genesis["previous_approved_deltas_final"]),
        previous_chain_head=str(genesis["chain_head"]),
    )
    assert (
        verify_autonomous_governance_surface_trajectory_v1(
            receipt=inflated, policy=policy
        )["ok"]
        is True
    )
    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, inflated], policy=policy
    )
    assert verification["ok"] is False
    assert "session_trajectory_budget_inconsistent" in verification["errors"]
    assert verification["checks"]["budget_consistent_ok"] is False



def test_session_verifier_refuses_genesis_budget_above_policy_limit() -> None:
    policy = _policy()
    inflated_budget = {**dict(_BUDGET), "fee_bps": 5_000}
    genesis = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=_pressure_steps(20, 100),
        expected_policy_hash=str(policy["policy_hash"]),
        trajectory_budget=inflated_budget,
    )
    assert genesis["trajectory_budget"]["fee_bps"] == 5_000
    assert genesis["trajectory_used_final"]["fee_bps"] > _BUDGET["fee_bps"]
    assert (
        verify_autonomous_governance_surface_trajectory_v1(
            receipt=genesis, policy=policy
        )["ok"]
        is True
    )

    child = _continue(policy, genesis, _pressure_steps(2, 120))
    assert child["trajectory_budget"] == genesis["trajectory_budget"]

    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, child], policy=policy
    )
    assert verification["ok"] is False
    assert verification["checks"]["budget_consistent_ok"] is True
    assert verification["checks"]["budget_policy_bound_ok"] is False
    assert "session_trajectory_budget_policy_mismatch" in verification["errors"]

def test_session_verifier_refuses_structural_member() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    structural = run_autonomous_governance_surface_trajectory_v1(
        policy=policy,
        initial_surface_state=_surface_state(),
        steps=[],
        expected_policy_hash=str(policy["policy_hash"]),
    )
    assert structural["status"] == STATUS_REJECTED_STRUCTURAL
    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, structural], policy=policy
    )
    assert verification["ok"] is False
    assert "session_receipt_unverified:1" in verification["errors"]


def test_session_verifier_refuses_expected_policy_hash_mismatch() -> None:
    policy = _policy()
    genesis = _genesis(policy)
    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis], policy=policy, expected_policy_hash="0x" + "00" * 32
    )
    assert verification["ok"] is False
    assert "session_expected_policy_hash_mismatch" in verification["errors"]


@pytest.mark.parametrize("receipts", [None, (), [], "receipts", 7])
def test_session_verifier_refuses_malformed_receipt_lists(receipts: object) -> None:
    policy = _policy()
    verification = verify_autonomous_governance_surface_session_v1(
        receipts=receipts, policy=policy
    )
    assert verification["ok"] is False
    assert "session_receipts_must_be_nonempty_sequence" in verification["errors"]


def test_session_verifier_refuses_non_trajectory_members() -> None:
    policy = _policy()
    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[{"schema": "something_else"}, 42], policy=policy
    )
    assert verification["ok"] is False
    assert "session_receipt_malformed:0" in verification["errors"]
    assert "session_receipt_malformed:1" in verification["errors"]


def test_session_accounting_is_re_derived_over_three_segments() -> None:
    policy = _policy()
    genesis = _genesis(policy, steps=_pressure_steps(2, 100))
    second = _continue(policy, genesis, _pressure_steps(2, 102))
    third = _continue(policy, second, _pressure_steps(2, 104))

    verification = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, second, third], policy=policy
    )
    assert verification["ok"] is True, verification["errors"]
    expected_drift = (
        third["final_state"]["fee_bps"] - genesis["initial_state"]["fee_bps"]
    )
    assert verification["session_drift"]["fee_bps"] == expected_drift == 50
    assert verification["session_used_final"]["fee_bps"] == 50
    assert verification["checks"]["session_accounting_ok"] is True

    # Reordering the segments breaks linkage AND accounting, not just hashes.
    shuffled = verify_autonomous_governance_surface_session_v1(
        receipts=[genesis, third, second], policy=policy
    )
    assert shuffled["ok"] is False
    assert shuffled["checks"]["boundary_carry_ok"] is False


def test_cli_continue_trajectory_and_verify_session(tmp_path: Path) -> None:
    policy = _policy()
    genesis = _genesis(policy)

    continue_bundle = tmp_path / "continue-trajectory.json"
    continue_bundle.write_text(
        json.dumps(
            {
                "policy": policy,
                "previous_receipt": genesis,
                "steps": _pressure_steps(2, 103),
                "expected_policy_hash": policy["policy_hash"],
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    continued = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "continue-trajectory",
            str(continue_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert continued.returncode == 0, continued.stderr
    child = json.loads(continued.stdout)
    assert child["ok"] is True
    assert child["carry_in"]["previous_chain_head"] == genesis["chain_head"]

    session_bundle = tmp_path / "verify-session.json"
    session_bundle.write_text(
        json.dumps(
            {
                "policy": policy,
                "trajectory_receipts": [genesis, child],
                "expected_policy_hash": policy["policy_hash"],
            },
            sort_keys=True,
        ),
        encoding="utf-8",
    )
    verified = subprocess.run(
        [
            sys.executable,
            "tools/autonomous_governance_q_policy.py",
            "verify-session",
            str(session_bundle),
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    assert verified.returncode == 0, verified.stderr
    verification = json.loads(verified.stdout)
    assert verification["ok"] is True, verification["errors"]
    assert verification["checks"]["boundary_carry_ok"] is True
    assert verification["session_chain_head"] == child["chain_head"]
