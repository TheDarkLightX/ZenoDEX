"""Parity check: `src/core/il_futures.py` vs generated ref for the v1 kernel spec.

The reference model is generated from `src/kernels/dex/il_futures_market_v1.yaml`
and checked into `generated/` so CI can catch semantic drift without requiring the
external verifier/codegen toolchain at runtime.

Notes:
- Our runtime model is a refinement: it takes pool reserves as inputs for settlement,
  while the bounded kernel ref expects derived values (`il_bps`, `capped_payout`, `protocol_fee`).
- This test derives those values from the pre-state + our settlement inputs, and then
  checks step-by-step parity on the shared state fields and effects.
"""

from __future__ import annotations

import importlib.util
import random
import sys
from pathlib import Path
from typing import Any

import pytest

from src.core.il_futures import (
    BPS_DENOM,
    ILFAction,
    ILFActionParams,
    ILFEffect,
    ILFState,
    MAX_AMOUNT,
    MAX_PREMIUM_AMOUNT,
    step,
)
from src.core.il_futures_math import compute_il_bps, compute_payout


def _import_generated_ref() -> Any:
    root = Path(__file__).resolve().parents[2]
    ref_path = root / "generated" / "derivatives_python" / "il_futures_market_v1_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = "generated.derivatives_python.il_futures_market_v1_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


REF = _import_generated_ref()


def _to_ref_state(s: ILFState):
    return REF.State(
        coverage_ratio_bps=int(s.coverage_ratio_bps),
        epoch=int(s.epoch),
        long_exposure=int(s.long_exposure),
        margin_pool=int(s.margin_pool),
        max_leverage_bps=int(s.max_leverage_bps),
        pool_snapshot_reserve_x=int(s.pool_snapshot_reserve_x),
        pool_snapshot_reserve_y=int(s.pool_snapshot_reserve_y),
        premium_pool=int(s.premium_pool),
        protocol_fee_bps=int(s.protocol_fee_bps),
        protocol_fee_pool=int(s.protocol_fee_pool),
        realized_il_bps=int(s.realized_il_bps),
        settled_this_epoch=bool(s.settled_this_epoch),
        short_exposure=int(s.short_exposure),
        snapshot_taken=bool(s.snapshot_taken),
    )


def _derive_settle_args(pre: ILFState, params: ILFActionParams) -> tuple[int, int, int]:
    il_bps = compute_il_bps(
        pre.pool_snapshot_reserve_x,
        pre.pool_snapshot_reserve_y,
        params.current_reserve_x,
        params.current_reserve_y,
    )
    total_long_payout = compute_payout(il_bps, pre.long_exposure, pre.coverage_ratio_bps)
    capped_payout = min(int(total_long_payout), int(pre.margin_pool))
    protocol_fee = (int(capped_payout) * int(pre.protocol_fee_bps)) // int(BPS_DENOM)
    return int(il_bps), int(capped_payout), int(protocol_fee)


def _to_ref_cmd(pre: ILFState, params: ILFActionParams):
    tag: str
    args: dict[str, Any] = {}

    if params.action is ILFAction.OPEN_LONG_IL:
        tag = "open_long_il"
        args["amount"] = int(params.amount)
        args["premium_amount"] = int(params.premium_amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is ILFAction.OPEN_SHORT_IL:
        tag = "open_short_il"
        args["amount"] = int(params.amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is ILFAction.CLOSE_POSITION:
        if params.close_long:
            tag = "close_long"
        elif params.close_short:
            tag = "close_short"
        else:
            # Our model rejects this; pick a deterministic tag to keep cmd well-formed.
            tag = "close_long"
        args["amount"] = int(params.amount)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is ILFAction.SNAPSHOT_EPOCH_START:
        tag = "snapshot_epoch_start"
        args["reserve_x"] = int(params.reserve_x)
        args["reserve_y"] = int(params.reserve_y)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is ILFAction.SETTLE_IL_EPOCH:
        tag = "settle_il_epoch"
        il_bps, capped_payout, protocol_fee = _derive_settle_args(pre, params)
        args["il_bps"] = int(il_bps)
        args["capped_payout"] = int(capped_payout)
        args["protocol_fee"] = int(protocol_fee)
        args["auth_ok"] = bool(params.auth_ok)
    elif params.action is ILFAction.ADVANCE_EPOCH:
        tag = "advance_epoch"
        args = {}
    else:
        raise AssertionError(f"unhandled action in parity test: {params.action}")

    return REF.Command(tag=tag, args=args)


def _effect_as_ref_dict(eff: ILFEffect) -> dict[str, Any]:
    # Ref only exposes: (event, il_bps_out, payout_out).
    return {
        "event": eff.event.value,
        "il_bps_out": int(eff.il_bps),
        "payout_out": int(eff.net_payout),
    }


def _random_action_params(rng: random.Random, s: ILFState) -> ILFActionParams:
    # Drive to "interesting" accepted steps: keep a mild preference toward progressing the epoch.
    actions = [
        ILFAction.OPEN_SHORT_IL,
        ILFAction.OPEN_LONG_IL,
        ILFAction.CLOSE_POSITION,
        ILFAction.SNAPSHOT_EPOCH_START,
        ILFAction.SETTLE_IL_EPOCH,
        ILFAction.ADVANCE_EPOCH,
    ]
    action = rng.choice(actions)

    if action is ILFAction.OPEN_SHORT_IL:
        return ILFActionParams(action=action, amount=rng.randint(1, 50_000), auth_ok=True)

    if action is ILFAction.OPEN_LONG_IL:
        # Keep amount small so leverage checks are more likely to pass.
        amount = rng.randint(1, 20_000)
        premium = rng.randint(1, min(10_000, MAX_PREMIUM_AMOUNT))
        return ILFActionParams(action=action, amount=amount, premium_amount=premium, auth_ok=True)

    if action is ILFAction.CLOSE_POSITION:
        close_long = bool(rng.getrandbits(1))
        close_short = not close_long
        # Let guards decide; this will often reject when exposure is 0.
        amount = rng.randint(1, 50_000)
        return ILFActionParams(
            action=action,
            amount=amount,
            close_long=close_long,
            close_short=close_short,
            auth_ok=True,
        )

    if action is ILFAction.SNAPSHOT_EPOCH_START:
        # Bound reserves to the kernel domain.
        rx = rng.randint(1, 2_000_000_000)
        ry = rng.randint(1, 2_000_000_000)
        return ILFActionParams(action=action, reserve_x=rx, reserve_y=ry, auth_ok=True)

    if action is ILFAction.SETTLE_IL_EPOCH:
        # Our model requires current reserves; the kernel ref consumes derived args.
        # Keep within the bounded domain.
        cx = rng.randint(1, 2_000_000_000)
        cy = rng.randint(1, 2_000_000_000)
        return ILFActionParams(action=action, current_reserve_x=cx, current_reserve_y=cy, auth_ok=True)

    if action is ILFAction.ADVANCE_EPOCH:
        return ILFActionParams(action=action)

    raise AssertionError("unreachable")


class TestILFuturesParityWithGeneratedRef:
    def test_initial_state_matches(self) -> None:
        ours = ILFState()
        ref = REF.init_state()
        assert vars(_to_ref_state(ours)) == vars(ref)

    @pytest.mark.parametrize(
        "amount,expected_ok,reason",
        [
            (-1, False, "negative amount"),
            (0, False, "just below min=1"),
            (1, True, "at min"),
            (2, True, "just above min"),
            (MAX_AMOUNT, True, "at max"),
            (MAX_AMOUNT + 1, False, "just above max"),
        ],
    )
    def test_bva_open_short_amount(self, amount: int, expected_ok: bool, reason: str) -> None:
        ours = ILFState()
        ref = REF.init_state()
        params = ILFActionParams(action=ILFAction.OPEN_SHORT_IL, amount=amount, auth_ok=True)

        our_res = step(ours, params)
        ref_res = REF.step(ref, _to_ref_cmd(ours, params))

        assert our_res.accepted == ref_res.ok, reason
        assert our_res.accepted == expected_ok, reason

    @pytest.mark.parametrize(
        "premium,expected_ok,reason",
        [
            (0, False, "just below min=1"),
            (1, True, "at min"),
            (2, True, "just above min"),
            (MAX_PREMIUM_AMOUNT, True, "at max"),
            (MAX_PREMIUM_AMOUNT + 1, False, "just above max"),
        ],
    )
    def test_bva_open_long_premium(self, premium: int, expected_ok: bool, reason: str) -> None:
        # Ensure shorts exist so leverage is defined.
        ours = ILFState(short_exposure=50_000, margin_pool=50_000)
        ref = _to_ref_state(ours)
        params = ILFActionParams(
            action=ILFAction.OPEN_LONG_IL,
            amount=1,
            premium_amount=premium,
            auth_ok=True,
        )

        our_res = step(ours, params)
        ref_res = REF.step(ref, _to_ref_cmd(ours, params))

        assert our_res.accepted == ref_res.ok, reason
        assert our_res.accepted == expected_ok, reason

    @pytest.mark.parametrize(
        "reserve,expected_ok,reason",
        [
            (0, False, "just below min=1"),
            (1, True, "at min"),
            (2, True, "just above min"),
            (MAX_AMOUNT, True, "at max"),
            (MAX_AMOUNT + 1, False, "just above max"),
        ],
    )
    def test_bva_snapshot_reserve_bounds(self, reserve: int, expected_ok: bool, reason: str) -> None:
        ours = ILFState()
        ref = REF.init_state()
        params = ILFActionParams(
            action=ILFAction.SNAPSHOT_EPOCH_START,
            reserve_x=reserve,
            reserve_y=reserve,
            auth_ok=True,
        )

        our_res = step(ours, params)
        ref_res = REF.step(ref, _to_ref_cmd(ours, params))

        assert our_res.accepted == ref_res.ok, reason
        assert our_res.accepted == expected_ok, reason

    def test_random_trace_parity(self) -> None:
        rng = random.Random(0)
        ours = ILFState()
        ref = REF.init_state()

        for _ in range(500):
            params = _random_action_params(rng, ours)
            our_res = step(ours, params)
            ref_res = REF.step(ref, _to_ref_cmd(ours, params))

            assert our_res.accepted == ref_res.ok

            if not our_res.accepted:
                continue

            assert our_res.state is not None
            assert our_res.effect is not None
            assert ref_res.state is not None
            assert ref_res.effects is not None

            assert vars(_to_ref_state(our_res.state)) == vars(ref_res.state)
            assert _effect_as_ref_dict(our_res.effect) == dict(ref_res.effects)

            ours = our_res.state
            ref = ref_res.state

