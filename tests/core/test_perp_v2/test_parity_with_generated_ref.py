"""Parity check: `src/core/perp_v2` vs ESSO-generated Python ref for the YAML spec.

This is the strongest, CI-friendly regression test we can have without running the
ESSO interpreter:
- the generated ref is derived directly from `src/kernels/dex/perp_epoch_isolated_v2.yaml`
- `src/core/perp_v2` is the hand-maintained "production" implementation

If this test fails, it indicates a semantic drift between the implementation and
the spec/codegen artifact.
"""

from __future__ import annotations

import importlib.util
import random
import sys
from dataclasses import replace
from pathlib import Path
from typing import Any

import pytest

from src.core.perp_v2 import Action, ActionParams, initial_state, step
from src.core.perp_v2.state import state_to_dict


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[3]
    ref_path = root / "generated" / "perp_python" / "perp_epoch_isolated_v2_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.perp_python.perp_epoch_isolated_v2_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def _to_ref_state(s) -> Any:
    return REF.State(**state_to_dict(s))


def _to_ref_cmd(params: ActionParams) -> Any:
    tag = params.action.value
    args: dict[str, Any] = {}

    if params.action is Action.ADVANCE_EPOCH:
        args["delta"] = int(params.delta)
    elif params.action is Action.PUBLISH_CLEARING_PRICE:
        args["price_e8"] = int(params.price_e8)
    elif params.action is Action.DEPOSIT_COLLATERAL:
        args["amount"] = int(params.amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.WITHDRAW_COLLATERAL:
        args["amount"] = int(params.amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.SET_POSITION:
        args["new_position_base"] = int(params.new_position_base)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.CLEAR_BREAKER:
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.APPLY_FUNDING:
        args["new_rate_bps"] = int(params.new_rate_bps)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.DEPOSIT_INSURANCE:
        args["amount"] = int(params.amount)
    elif params.action is Action.APPLY_INSURANCE_CLAIM:
        args["claim_amount"] = int(params.claim_amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is Action.SETTLE_EPOCH:
        args = {}
    else:
        raise AssertionError(f"unhandled action in parity test: {params.action}")

    return REF.Command(tag=tag, args=args)


def _effect_as_dict(our_effect) -> dict[str, Any]:
    assert our_effect is not None
    return {
        "event": our_effect.event.value,
        "oracle_fresh": bool(our_effect.oracle_fresh),
        "notional_quote": int(our_effect.notional_quote),
        "effective_maint_bps": int(our_effect.effective_maint_bps),
        "maint_req_quote": int(our_effect.maint_req_quote),
        "init_req_quote": int(our_effect.init_req_quote),
        "margin_ok": bool(our_effect.margin_ok),
        "liquidated": bool(our_effect.liquidated),
        "collateral_after": int(our_effect.collateral_after),
        "fee_pool_after": int(our_effect.fee_pool_after),
        "insurance_after": int(our_effect.insurance_after),
    }


def _random_action_params(rng: random.Random) -> ActionParams:
    # Bias toward "useful" actions, but allow rejections; parity should still hold.
    action = rng.choice(
        [
            Action.ADVANCE_EPOCH,
            Action.PUBLISH_CLEARING_PRICE,
            Action.SETTLE_EPOCH,
            Action.DEPOSIT_COLLATERAL,
            Action.WITHDRAW_COLLATERAL,
            Action.SET_POSITION,
            Action.CLEAR_BREAKER,
            Action.APPLY_FUNDING,
            Action.DEPOSIT_INSURANCE,
            Action.APPLY_INSURANCE_CLAIM,
        ]
    )

    if action is Action.ADVANCE_EPOCH:
        return ActionParams(action=action, delta=rng.randint(1, 3))
    if action is Action.PUBLISH_CLEARING_PRICE:
        return ActionParams(action=action, price_e8=rng.randint(1, 2_000_000_000))
    if action is Action.DEPOSIT_COLLATERAL:
        return ActionParams(action=action, amount=rng.randint(1, 50_000), auth_ok=True)
    if action is Action.WITHDRAW_COLLATERAL:
        return ActionParams(action=action, amount=rng.randint(1, 50_000), auth_ok=True)
    if action is Action.SET_POSITION:
        return ActionParams(action=action, new_position_base=rng.randint(-1000, 1000), auth_ok=True)
    if action is Action.CLEAR_BREAKER:
        return ActionParams(action=action, auth_ok=True)
    if action is Action.APPLY_FUNDING:
        # funding_cap_bps defaults to 100; keep inside to reduce trivial rejections.
        return ActionParams(action=action, new_rate_bps=rng.randint(-100, 100), auth_ok=True)
    if action is Action.DEPOSIT_INSURANCE:
        return ActionParams(action=action, amount=rng.randint(1, 100_000))
    if action is Action.APPLY_INSURANCE_CLAIM:
        # Most claims will be rejected (no insurance deposited), which is fine.
        return ActionParams(action=action, claim_amount=rng.randint(1, 50_000), auth_ok=True)
    if action is Action.SETTLE_EPOCH:
        return ActionParams(action=action)

    raise AssertionError("unreachable")


class TestPerpV2ParityWithGeneratedRef:
    def test_initial_state_matches(self) -> None:
        ours = initial_state()
        ref = REF.init_state()
        assert state_to_dict(ours) == vars(ref)

    def test_random_trace_parity(self) -> None:
        rng = random.Random(0)
        ours = initial_state()
        ref = REF.init_state()

        # Make sure oracle is seen early so we exercise more actions.
        ours = replace(ours, oracle_seen=True, oracle_last_update_epoch=0, index_price_e8=100_000_000)
        ref = replace(ref, oracle_seen=True, oracle_last_update_epoch=0, index_price_e8=100_000_000)

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

            assert state_to_dict(our_res.state) == vars(ref_res.state)
            assert _effect_as_dict(our_res.effect) == dict(ref_res.effects)

            ours = our_res.state
            ref = ref_res.state
