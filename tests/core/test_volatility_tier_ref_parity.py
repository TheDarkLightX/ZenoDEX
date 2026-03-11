"""Parity check: `src/core/volatility_tier.py` vs generated ref for the v1 kernel.

The reference model is generated from `src/kernels/dex/volatility_tier_controller_v1.yaml`
and checked into `generated/` so this test can catch semantic drift without depending
on a live ESSO export step.
"""

from __future__ import annotations

import importlib.util
import random
import sys
from pathlib import Path
from typing import Any

import pytest

from src.core.volatility_tier import (
    TierAction,
    TierActionParams,
    effective_fee_bps,
    max_trade_amount,
    step,
)
from src.state.volatility import TierState


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[2]
    ref_path = (
        root
        / "generated"
        / "volatility_tier_controller_v1_python_ref"
        / "volatility_tier_controller_v1_ref.py"
    )
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.volatility_tier_controller_v1_python_ref.volatility_tier_controller_v1_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def _to_ref_state(state: TierState):
    return REF.State(
        last_epoch=int(state.last_epoch),
        t1_bps=int(state.t1_bps),
        t2_bps=int(state.t2_bps),
        t3_bps=int(state.t3_bps),
        tier=int(state.tier),
    )


def _to_ref_cmd(params: TierActionParams):
    if params.action is TierAction.OBSERVE:
        return REF.Command(
            tag="observe",
            args={
                "epoch": params.epoch,
                "volatility_bps": params.volatility_bps,
                "data_ok": params.data_ok,
            },
        )
    if params.action is TierAction.CONFIGURE:
        return REF.Command(
            tag="configure",
            args={
                "caller_is_admin": params.caller_is_admin,
                "new_t1_bps": params.new_t1_bps,
                "new_t2_bps": params.new_t2_bps,
                "new_t3_bps": params.new_t3_bps,
            },
        )
    raise AssertionError(f"unhandled action in parity test: {params.action}")


def _rejection_category(our_rejection: str | None, ref_error: str | None) -> tuple[str | None, str | None]:
    our_category = our_rejection
    if our_rejection is not None and our_rejection.startswith("invalid_param:"):
        our_category = our_rejection.split(":", 1)[1]

    ref_category = ref_error
    if ref_error is not None and ref_error.startswith("invalid param "):
        ref_category = ref_error.removeprefix("invalid param ")
    if ref_error is not None and ref_error.startswith("guard failed for "):
        ref_category = "guard"

    return our_category, ref_category


def _assert_step_parity(state: TierState, params: TierActionParams) -> None:
    our_result = step(state, params)
    ref_result = REF.step(_to_ref_state(state), _to_ref_cmd(params))

    assert our_result.accepted == ref_result.ok

    if not our_result.accepted:
        our_rejection, ref_rejection = _rejection_category(our_result.rejection, ref_result.error)
        assert our_rejection == ref_rejection
        return

    assert our_result.state is not None
    assert our_result.effects is not None
    assert ref_result.state is not None
    assert ref_result.effects is not None

    assert vars(_to_ref_state(our_result.state)) == vars(ref_result.state)
    assert vars(our_result.effects) == dict(ref_result.effects)


def _random_action_params(rng: random.Random, state: TierState) -> TierActionParams:
    action = rng.choice([TierAction.OBSERVE, TierAction.CONFIGURE])
    if action is TierAction.OBSERVE:
        epoch = rng.choice(
            [
                max(0, state.last_epoch - 1),
                state.last_epoch,
                min(1_000_000_000, state.last_epoch + 1),
            ]
        )
        return TierActionParams(
            action=action,
            epoch=epoch,
            volatility_bps=rng.randint(0, 10_000),
            data_ok=bool(rng.getrandbits(1)),
        )

    thresholds = sorted(
        [
            rng.randint(0, 10_000),
            rng.randint(0, 10_000),
            rng.randint(0, 10_000),
        ]
    )
    if rng.random() < 0.35:
        thresholds[0], thresholds[2] = thresholds[2], thresholds[0]
    return TierActionParams(
        action=action,
        caller_is_admin=bool(rng.getrandbits(1)),
        new_t1_bps=thresholds[0],
        new_t2_bps=thresholds[1],
        new_t3_bps=thresholds[2],
    )


class TestVolatilityTierParityWithGeneratedRef:
    def test_initial_state_matches(self) -> None:
        assert vars(_to_ref_state(TierState())) == vars(REF.init_state())

    def test_observe_boundary_grid_parity(self) -> None:
        states = [
            TierState(),
            TierState(tier=2, last_epoch=5),
            TierState(tier=1, last_epoch=7, t1_bps=2000, t2_bps=5000, t3_bps=7000),
            TierState(tier=3, last_epoch=11),
        ]
        for state in states:
            epochs = [max(0, state.last_epoch - 1), state.last_epoch, state.last_epoch + 1]
            vols = sorted(
                {
                    0,
                    max(0, state.t1_bps - 1),
                    state.t1_bps,
                    max(0, state.t2_bps - 1),
                    state.t2_bps,
                    max(0, state.t3_bps - 1),
                    state.t3_bps,
                    10_000,
                }
            )
            for epoch in epochs:
                for volatility_bps in vols:
                    for data_ok in (False, True):
                        _assert_step_parity(
                            state,
                            TierActionParams(
                                action=TierAction.OBSERVE,
                                epoch=epoch,
                                volatility_bps=volatility_bps,
                                data_ok=data_ok,
                            ),
                        )

    def test_configure_boundary_grid_parity(self) -> None:
        states = [
            TierState(),
            TierState(tier=2, last_epoch=5),
            TierState(tier=1, last_epoch=7, t1_bps=2000, t2_bps=5000, t3_bps=7000),
        ]
        threshold_cases = [
            (0, 0, 0),
            (2000, 5000, 7000),
            (3000, 6000, 8000),
            (5000, 5000, 5000),
            (7000, 5000, 2000),
            (-1, 5000, 7000),
            (100, 200, 10_001),
        ]
        for state in states:
            for caller_is_admin in (False, True):
                for t1_bps, t2_bps, t3_bps in threshold_cases:
                    _assert_step_parity(
                        state,
                        TierActionParams(
                            action=TierAction.CONFIGURE,
                            caller_is_admin=caller_is_admin,
                            new_t1_bps=t1_bps,
                            new_t2_bps=t2_bps,
                            new_t3_bps=t3_bps,
                        ),
                    )

    @pytest.mark.parametrize(
        ("params", "field"),
        [
            (
                TierActionParams(  # type: ignore[arg-type]
                    action=TierAction.OBSERVE,
                    epoch="1",
                    volatility_bps=1000,
                    data_ok=True,
                ),
                "epoch",
            ),
            (
                TierActionParams(  # type: ignore[arg-type]
                    action=TierAction.OBSERVE,
                    epoch=1,
                    volatility_bps="1000",
                    data_ok=True,
                ),
                "volatility_bps",
            ),
            (
                TierActionParams(  # type: ignore[arg-type]
                    action=TierAction.OBSERVE,
                    epoch=1,
                    volatility_bps=1000,
                    data_ok=1,
                ),
                "data_ok",
            ),
            (
                TierActionParams(  # type: ignore[arg-type]
                    action=TierAction.CONFIGURE,
                    caller_is_admin=1,
                    new_t1_bps=3000,
                    new_t2_bps=6000,
                    new_t3_bps=8000,
                ),
                "caller_is_admin",
            ),
            (
                TierActionParams(  # type: ignore[arg-type]
                    action=TierAction.CONFIGURE,
                    caller_is_admin=True,
                    new_t1_bps="3000",
                    new_t2_bps=6000,
                    new_t3_bps=8000,
                ),
                "new_t1_bps",
            ),
        ],
    )
    def test_invalid_param_parity(self, params: TierActionParams, field: str) -> None:
        our_result = step(TierState(), params)
        ref_result = REF.step(REF.init_state(), _to_ref_cmd(params))

        assert not our_result.accepted
        assert our_result.rejection == f"invalid_param:{field}"
        assert not ref_result.ok
        assert ref_result.error == f"invalid param {field}"

    def test_random_trace_parity(self) -> None:
        rng = random.Random(0)
        our_state = TierState()
        ref_state = REF.init_state()

        for _ in range(500):
            params = _random_action_params(rng, our_state)
            our_result = step(our_state, params)
            ref_result = REF.step(ref_state, _to_ref_cmd(params))

            assert our_result.accepted == ref_result.ok

            if not our_result.accepted:
                our_rejection, ref_rejection = _rejection_category(our_result.rejection, ref_result.error)
                assert our_rejection == ref_rejection
                continue

            assert our_result.state is not None
            assert our_result.effects is not None
            assert ref_result.state is not None
            assert ref_result.effects is not None

            assert vars(_to_ref_state(our_result.state)) == vars(ref_result.state)
            assert vars(our_result.effects) == dict(ref_result.effects)

            our_state = our_result.state
            ref_state = ref_result.state

    def test_convenience_helpers_match_ref_effects(self) -> None:
        base_fee_bps = 30
        reserve = 1_000_000
        for tier in range(4):
            state = TierState(tier=tier)
            ref_effects = dict(REF.step(_to_ref_state(state), REF.Command(tag="configure", args={
                "caller_is_admin": True,
                "new_t1_bps": state.t1_bps,
                "new_t2_bps": state.t2_bps,
                "new_t3_bps": state.t3_bps,
            })).effects)

            expected_fee = -1 if ref_effects["halt"] else (base_fee_bps * ref_effects["fee_mult_bps"]) // 10_000
            expected_trade = (reserve * ref_effects["max_trade_bps"]) // 10_000

            assert effective_fee_bps(base_fee_bps, state) == expected_fee
            assert max_trade_amount(reserve, state) == expected_trade
