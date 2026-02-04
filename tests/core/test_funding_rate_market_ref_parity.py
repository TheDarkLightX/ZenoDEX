"""Parity check: `src/core/funding_rate_market.py` vs generated ref for the v1.1 kernel spec.

The reference model is generated from `src/kernels/dex/funding_rate_market_v1_1.yaml`
and checked into `generated/` so CI can catch semantic drift without requiring the
external verifier/codegen toolchain at runtime.
"""

from __future__ import annotations

import importlib.util
import random
import sys
from pathlib import Path
from typing import Any

import pytest

from src.core.funding_rate_market import (
    FRMAction,
    FRMActionParams,
    FRMEffect,
    FRMState,
    step,
)


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[2]
    ref_path = (
        root / "generated" / "derivatives_python" / "funding_rate_market_v1_1_ref.py"
    )
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.derivatives_python.funding_rate_market_v1_1_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def _to_ref_state(s: FRMState):
    return REF.State(**vars(s))


def _to_ref_cmd(params: FRMActionParams):
    tag = params.action.value
    args: dict[str, Any] = {}

    if params.action in (FRMAction.OPEN_RATE_LONG, FRMAction.OPEN_RATE_SHORT):
        args["amount"] = int(params.amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is FRMAction.SETTLE_RATE_EPOCH:
        args["mark_price_e8"] = int(params.mark_price_e8)
        args["index_price_e8"] = int(params.index_price_e8)
    elif params.action is FRMAction.ADVANCE_RATE_EPOCH:
        args = {}
    elif params.action is FRMAction.EMERGENCY_FREEZE:
        args["auth_ok"] = bool(params.auth_ok)
    else:
        raise AssertionError(f"unhandled action in parity test: {params.action}")

    return REF.Command(tag=tag, args=args)


def _effect_as_dict(eff: FRMEffect) -> dict[str, Any]:
    return {
        "event": eff.event.value,
        "implied_rate_bps": int(eff.implied_rate_bps),
        "realized_rate_bps": int(eff.realized_rate_bps),
        "payout_long": int(eff.payout_long),
        "payout_short": int(eff.payout_short),
    }


def _random_action_params(rng: random.Random) -> FRMActionParams:
    action = rng.choice(
        [
            FRMAction.OPEN_RATE_LONG,
            FRMAction.OPEN_RATE_SHORT,
            FRMAction.SETTLE_RATE_EPOCH,
            FRMAction.ADVANCE_RATE_EPOCH,
            FRMAction.EMERGENCY_FREEZE,
        ]
    )

    if action in (FRMAction.OPEN_RATE_LONG, FRMAction.OPEN_RATE_SHORT):
        return FRMActionParams(
            action=action, amount=rng.randint(1, 50_000), auth_ok=True
        )
    if action is FRMAction.SETTLE_RATE_EPOCH:
        index = rng.randint(1, 2_000_000_000)
        # Allow both positive and negative basis.
        mark = max(1, index + rng.randint(-200_000_000, 200_000_000))
        return FRMActionParams(action=action, mark_price_e8=mark, index_price_e8=index)
    if action is FRMAction.ADVANCE_RATE_EPOCH:
        return FRMActionParams(action=action)
    if action is FRMAction.EMERGENCY_FREEZE:
        return FRMActionParams(action=action, auth_ok=True)

    raise AssertionError("unreachable")


class TestFundingRateMarketParityWithGeneratedRef:
    def test_initial_state_matches(self) -> None:
        ours = FRMState()
        ref = REF.init_state()
        assert vars(ours) == vars(ref)

    def test_random_trace_parity(self) -> None:
        rng = random.Random(0)
        ours = FRMState()
        ref = REF.init_state()

        for _ in range(500):
            params = _random_action_params(rng)
            our_res = step(ours, params)
            ref_res = REF.step(ref, _to_ref_cmd(params))

            assert our_res.accepted == ref_res.ok

            if not our_res.accepted:
                continue

            assert our_res.state is not None
            assert our_res.effect is not None
            assert ref_res.state is not None
            assert ref_res.effects is not None

            assert vars(our_res.state) == vars(ref_res.state)
            assert _effect_as_dict(our_res.effect) == dict(ref_res.effects)

            ours = our_res.state
            ref = ref_res.state
