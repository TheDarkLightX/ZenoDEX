"""Parity check: `src/core/curve_selection.py` vs generated ref for the v1 kernel spec.

The reference model is generated from `src/kernels/dex/curve_selection_market_v1.yaml`
and checked into `generated/` so CI can catch semantic drift without requiring the
external verifier/codegen toolchain at runtime.

Notes:
- Our runtime model computes some internal quantities (winner, protocol fee, unstake penalty).
  The bounded kernel ref expects those as command arguments; this test derives them from the
  pre-state so the two models can be compared step-by-step.
"""

from __future__ import annotations

import importlib.util
import random
import sys
from pathlib import Path
from typing import Any

import pytest

from src.core.curve_selection import (
    BPS_DENOM,
    CSAction,
    CSActionParams,
    CSEffect,
    CSState,
    EARLY_EXIT_PENALTY_BPS,
    MAX_AMOUNT,
    MAX_SETTLEMENT_INTERVAL,
    NUM_CURVES,
    step,
)


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "derivatives_python" / "curve_selection_market_v1_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.derivatives_python.curve_selection_market_v1_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def _to_ref_state(s: CSState):
    return REF.State(**vars(s))


def _derive_unstake_penalty(amount: int) -> int:
    return (int(amount) * int(EARLY_EXIT_PENALTY_BPS)) // int(BPS_DENOM)


def _derive_settle_args(pre: CSState) -> tuple[int, int]:
    # Winner: highest revenue, tie-break lowest id.
    best_id = 0
    best_rev = pre.get_revenue(0)
    for cid in range(1, NUM_CURVES):
        rev = pre.get_revenue(cid)
        if rev > best_rev:
            best_id = cid
            best_rev = rev

    winner_stake = pre.get_stake(best_id)
    losing_stakes = pre.total_staked - winner_stake
    protocol_fee = (int(losing_stakes) * int(pre.protocol_fee_bps)) // int(BPS_DENOM)
    return int(best_id), int(protocol_fee)


def _to_ref_cmd(pre: CSState, params: CSActionParams):
    tag = params.action.value
    args: dict[str, Any] = {}

    if params.action is CSAction.STAKE_ON_CURVE:
        args["curve_id"] = int(params.curve_id)
        args["amount"] = int(params.amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is CSAction.UNSTAKE:
        args["curve_id"] = int(params.curve_id)
        args["amount"] = int(params.amount)
        args["penalty_amount"] = _derive_unstake_penalty(int(params.amount))
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is CSAction.ADVANCE_EPOCH:
        deltas = params.revenue_deltas
        assert len(deltas) == NUM_CURVES
        for i in range(NUM_CURVES):
            args[f"revenue_delta_{i}"] = int(deltas[i])
    elif params.action is CSAction.SETTLE_PREDICTION:
        winning_curve_id, protocol_fee = _derive_settle_args(pre)
        args["winning_curve_id"] = int(winning_curve_id)
        args["protocol_fee"] = int(protocol_fee)
    elif params.action is CSAction.ADMIN_SET_INTERVAL:
        args["new_interval"] = int(params.new_interval)
        args["auth_ok"] = bool(params.auth_ok)
    else:
        raise AssertionError(f"unhandled action in parity test: {params.action}")

    return REF.Command(tag=tag, args=args)


def _effect_as_ref_dict(eff: CSEffect) -> dict[str, Any]:
    # Ref only exposes: (event, payout_amount, winning_curve).
    return {
        "event": eff.event.value,
        "payout_amount": int(eff.payout_amount),
        "winning_curve": int(eff.winning_curve),
    }


def _random_action_params(rng: random.Random) -> CSActionParams:
    action = rng.choice(
        [
            CSAction.STAKE_ON_CURVE,
            CSAction.UNSTAKE,
            CSAction.ADVANCE_EPOCH,
            CSAction.SETTLE_PREDICTION,
            CSAction.ADMIN_SET_INTERVAL,
        ]
    )

    if action is CSAction.STAKE_ON_CURVE:
        return CSActionParams(
            action=action,
            curve_id=rng.randint(0, NUM_CURVES - 1),
            amount=rng.randint(1, 50_000),
            auth_ok=True,
        )
    if action is CSAction.UNSTAKE:
        return CSActionParams(
            action=action,
            curve_id=rng.randint(0, NUM_CURVES - 1),
            amount=rng.randint(1, 50_000),
            auth_ok=True,
        )
    if action is CSAction.ADVANCE_EPOCH:
        return CSActionParams(
            action=action,
            revenue_deltas=(
                rng.randint(0, 10_000),
                rng.randint(0, 10_000),
                rng.randint(0, 10_000),
                rng.randint(0, 10_000),
                rng.randint(0, 10_000),
            ),
        )
    if action is CSAction.SETTLE_PREDICTION:
        return CSActionParams(action=action)
    if action is CSAction.ADMIN_SET_INTERVAL:
        return CSActionParams(
            action=action,
            new_interval=rng.randint(1, MAX_SETTLEMENT_INTERVAL),
            auth_ok=True,
        )

    raise AssertionError("unreachable")


class TestCurveSelectionParityWithGeneratedRef:
    def test_initial_state_matches(self) -> None:
        ours = CSState()
        ref = REF.init_state()
        assert vars(ours) == vars(ref)

    @pytest.mark.parametrize(
        "new_interval,expected_ok,reason",
        [
            (0, False, "just below min=1"),
            (1, True, "at min"),
            (2, True, "just above min"),
            (MAX_SETTLEMENT_INTERVAL, True, "at max"),
            (MAX_SETTLEMENT_INTERVAL + 1, False, "just above max"),
        ],
    )
    def test_bva_admin_interval_bounds(self, new_interval: int, expected_ok: bool, reason: str) -> None:
        ours = CSState()
        ref = REF.init_state()
        params = CSActionParams(action=CSAction.ADMIN_SET_INTERVAL, new_interval=new_interval, auth_ok=True)

        our_res = step(ours, params)
        ref_res = REF.step(ref, _to_ref_cmd(ours, params))

        assert our_res.accepted == ref_res.ok, reason
        assert our_res.accepted == expected_ok, reason

    def test_random_trace_parity(self) -> None:
        rng = random.Random(0)
        ours = CSState()
        ref = REF.init_state()

        for _ in range(500):
            params = _random_action_params(rng)
            our_res = step(ours, params)
            ref_res = REF.step(ref, _to_ref_cmd(ours, params))

            assert our_res.accepted == ref_res.ok

            if not our_res.accepted:
                continue

            assert our_res.state is not None
            assert our_res.effect is not None
            assert ref_res.state is not None
            assert ref_res.effects is not None

            assert vars(our_res.state) == vars(ref_res.state)
            assert _effect_as_ref_dict(our_res.effect) == dict(ref_res.effects)

            ours = our_res.state
            ref = ref_res.state

