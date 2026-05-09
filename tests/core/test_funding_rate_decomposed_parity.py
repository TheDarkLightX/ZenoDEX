"""Conditional parity for the decomposed funding-rate assurance lane.

The published release-backed lane is:

1. ``funding_rate_market_v1`` for the phase/state shell.
2. ``funding_rate_settlement_witness_v1_1`` for deterministic settlement math.

The older monolithic ``funding_rate_market_v1_1`` generated reference remains a
parity artifact. These tests check that the decomposed lane matches that
monolith when the v1 shell is supplied with the deterministic witness values.
They also pin the reason v1 alone remains disputed for authorization semantics.
"""

from __future__ import annotations

import importlib.util
import random
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Literal

import pytest

from src.core.funding_rate_market import compute_implied_rate_bps
from src.kernels.python.funding_rate_settlement_runtime_v1_1 import (
    compute_funding_rate_settlement,
)

ROOT = Path(__file__).resolve().parents[2]


def _load_generated_ref(model_id: str) -> Any:
    ref_path = ROOT / "generated" / "derivatives_python" / f"{model_id}_ref.py"
    if not ref_path.exists():
        pytest.skip(f"generated ref not found at {ref_path}", allow_module_level=True)

    module_name = f"generated.derivatives_python.{model_id}_ref"
    spec = importlib.util.spec_from_file_location(module_name, ref_path)
    assert spec and spec.loader, f"could not load spec from {ref_path}"
    module = importlib.util.module_from_spec(spec)
    sys.modules[module_name] = module
    spec.loader.exec_module(module)
    return module


V1 = _load_generated_ref("funding_rate_market_v1")
V1_1 = _load_generated_ref("funding_rate_market_v1_1")


Action = Literal["open_rate_long", "open_rate_short", "settle_rate_epoch", "advance_rate_epoch"]


@dataclass(frozen=True)
class ActionSpec:
    tag: Action
    amount: int = 0
    mark_price_e8: int = 0
    index_price_e8: int = 0


PROJECTED_STATE_FIELDS = (
    "frozen",
    "funding_cap_bps",
    "implied_rate_bps",
    "index_price_e8",
    "long_payout",
    "mark_price_e8",
    "premium_pool",
    "protocol_fee_bps",
    "protocol_fee_pool",
    "rate_long_exposure",
    "rate_market_epoch",
    "rate_short_exposure",
    "realized_rate_bps",
    "settled_this_epoch",
    "settlement_epoch",
    "short_payout",
)


def _project_state(state: Any) -> dict[str, Any]:
    return {field: getattr(state, field) for field in PROJECTED_STATE_FIELDS}


def _project_monolithic_effect(effects: dict[str, Any]) -> dict[str, Any]:
    return {
        "event": effects["event"],
        "implied_rate_bps": effects.get("implied_rate_bps", effects.get("implied_rate_out")),
        "realized_rate_bps": effects.get("realized_rate_bps", effects.get("realized_rate_out")),
        "payout_long": effects.get("payout_long", 0),
        "payout_short": effects.get("payout_short", 0),
    }


def _project_decomposed_effect(effects: dict[str, Any], state: Any) -> dict[str, Any]:
    event = effects["event"]
    settled = event == "RateEpochSettled"
    return {
        "event": event,
        "implied_rate_bps": effects.get("implied_rate_out", effects.get("implied_rate_bps")),
        "realized_rate_bps": effects.get("realized_rate_out", effects.get("realized_rate_bps")),
        "payout_long": state.long_payout if settled else 0,
        "payout_short": state.short_payout if settled else 0,
    }


def _v1_command_from_witness(state: Any, action: ActionSpec) -> Any:
    if action.tag == "open_rate_long":
        implied = compute_implied_rate_bps(
            state.rate_long_exposure + action.amount,
            state.rate_short_exposure,
            state.funding_cap_bps,
        )
        return V1.Command(
            tag=action.tag,
            args={"amount": action.amount, "new_implied_rate_bps": implied, "auth_ok": True},
        )
    if action.tag == "open_rate_short":
        implied = compute_implied_rate_bps(
            state.rate_long_exposure,
            state.rate_short_exposure + action.amount,
            state.funding_cap_bps,
        )
        return V1.Command(
            tag=action.tag,
            args={"amount": action.amount, "new_implied_rate_bps": implied, "auth_ok": True},
        )
    if action.tag == "settle_rate_epoch":
        settlement = compute_funding_rate_settlement(
            rate_long_exposure=state.rate_long_exposure,
            rate_short_exposure=state.rate_short_exposure,
            premium_pool=state.premium_pool,
            implied_rate_bps=state.implied_rate_bps,
            funding_cap_bps=state.funding_cap_bps,
            protocol_fee_bps=state.protocol_fee_bps,
            mark_price_e8=action.mark_price_e8,
            index_price_e8=action.index_price_e8,
        )
        return V1.Command(
            tag=action.tag,
            args={
                "auth_ok": True,
                "realized_rate_bps": settlement.realized_rate_bps,
                "settle_long_payout": settlement.long_payout,
                "settle_short_payout": settlement.short_payout,
                "settle_protocol_fee": settlement.protocol_fee,
                "settle_mark_price_e8": action.mark_price_e8,
                "settle_index_price_e8": action.index_price_e8,
            },
        )
    if action.tag == "advance_rate_epoch":
        return V1.Command(tag=action.tag, args={})
    raise AssertionError(f"unhandled action: {action.tag}")


def _v1_1_command(action: ActionSpec) -> Any:
    if action.tag in ("open_rate_long", "open_rate_short"):
        return V1_1.Command(
            tag=action.tag,
            args={"amount": action.amount, "auth_ok": True},
        )
    if action.tag == "settle_rate_epoch":
        return V1_1.Command(
            tag=action.tag,
            args={
                "auth_ok": True,
                "mark_price_e8": action.mark_price_e8,
                "index_price_e8": action.index_price_e8,
            },
        )
    if action.tag == "advance_rate_epoch":
        return V1_1.Command(tag=action.tag, args={})
    raise AssertionError(f"unhandled action: {action.tag}")


def _assert_decomposed_matches_monolith(trace: list[ActionSpec]) -> None:
    decomposed = V1.init_state()
    monolith = V1_1.init_state()

    for step_index, action in enumerate(trace):
        decomposed_result = V1.step(decomposed, _v1_command_from_witness(decomposed, action))
        monolith_result = V1_1.step(monolith, _v1_1_command(action))

        assert decomposed_result.ok is True, (step_index, action, decomposed_result.error)
        assert monolith_result.ok is True, (step_index, action, monolith_result.error)
        assert decomposed_result.state is not None
        assert monolith_result.state is not None
        assert decomposed_result.effects is not None
        assert monolith_result.effects is not None

        assert _project_state(decomposed_result.state) == _project_state(monolith_result.state)
        assert _project_decomposed_effect(
            dict(decomposed_result.effects),
            decomposed_result.state,
        ) == _project_monolithic_effect(
            dict(monolith_result.effects)
        )

        decomposed = decomposed_result.state
        monolith = monolith_result.state


def test_decomposed_funding_rate_lane_matches_monolithic_v1_1_reference_examples() -> None:
    traces = [
        [
            ActionSpec("open_rate_long", amount=50_000),
            ActionSpec("open_rate_short", amount=50_000),
            ActionSpec("settle_rate_epoch", mark_price_e8=101_000_000, index_price_e8=100_000_000),
        ],
        [
            ActionSpec("open_rate_short", amount=75_001),
            ActionSpec("open_rate_long", amount=12_345),
            ActionSpec("settle_rate_epoch", mark_price_e8=99_000_000, index_price_e8=100_000_000),
            ActionSpec("advance_rate_epoch"),
            ActionSpec("open_rate_long", amount=100_000),
            ActionSpec("open_rate_short", amount=25_000),
            ActionSpec("settle_rate_epoch", mark_price_e8=100_000_001, index_price_e8=100_000_000),
        ],
        [
            ActionSpec("open_rate_long", amount=999_999_999),
            ActionSpec("open_rate_short", amount=1),
            ActionSpec("settle_rate_epoch", mark_price_e8=1, index_price_e8=1_000_000_000_000),
        ],
    ]

    for trace in traces:
        _assert_decomposed_matches_monolith(trace)


def test_decomposed_funding_rate_lane_matches_monolithic_v1_1_reference_randomized() -> None:
    rng = random.Random(20260509)

    for _ in range(80):
        first_long = rng.choice((True, False))
        amount_a = rng.randint(1, 10_000_000)
        amount_b = rng.randint(1, 10_000_000)
        mark = rng.randint(1, 2_000_000_000)
        index = rng.randint(1, 2_000_000_000)
        trace = [
            ActionSpec("open_rate_long" if first_long else "open_rate_short", amount=amount_a),
            ActionSpec("open_rate_short" if first_long else "open_rate_long", amount=amount_b),
            ActionSpec("settle_rate_epoch", mark_price_e8=mark, index_price_e8=index),
        ]
        if rng.choice((True, False)):
            trace.extend(
                [
                    ActionSpec("advance_rate_epoch"),
                    ActionSpec("open_rate_long", amount=rng.randint(1, 1_000_000)),
                    ActionSpec("open_rate_short", amount=rng.randint(1, 1_000_000)),
                    ActionSpec(
                        "settle_rate_epoch",
                        mark_price_e8=rng.randint(1, 2_000_000_000),
                        index_price_e8=rng.randint(1, 2_000_000_000),
                    ),
                ]
            )

        _assert_decomposed_matches_monolith(trace)


def test_v1_shell_alone_accepts_unbound_settlement_witness_values() -> None:
    """Pin the reason the v1 shell remains disputed for settlement authorization."""

    shell_state = V1.State(
        frozen=False,
        funding_cap_bps=100,
        implied_rate_bps=0,
        index_price_e8=0,
        long_payout=0,
        mark_price_e8=0,
        premium_pool=100_000,
        protocol_fee_bps=100,
        protocol_fee_pool=0,
        rate_long_exposure=50_000,
        rate_market_epoch=0,
        rate_short_exposure=50_000,
        realized_rate_bps=0,
        settled_this_epoch=False,
        settlement_epoch=0,
        short_payout=0,
    )
    false_but_conserved = V1.Command(
        tag="settle_rate_epoch",
        args={
            "auth_ok": True,
            "realized_rate_bps": -100,
            "settle_long_payout": 1,
            "settle_short_payout": 98_999,
            "settle_protocol_fee": 1_000,
            "settle_mark_price_e8": 101_000_000,
            "settle_index_price_e8": 100_000_000,
        },
    )

    shell_result = V1.step(shell_state, false_but_conserved)
    deterministic = compute_funding_rate_settlement(
        rate_long_exposure=shell_state.rate_long_exposure,
        rate_short_exposure=shell_state.rate_short_exposure,
        premium_pool=shell_state.premium_pool,
        implied_rate_bps=shell_state.implied_rate_bps,
        funding_cap_bps=shell_state.funding_cap_bps,
        protocol_fee_bps=shell_state.protocol_fee_bps,
        mark_price_e8=false_but_conserved.args["settle_mark_price_e8"],
        index_price_e8=false_but_conserved.args["settle_index_price_e8"],
    )

    assert shell_result.ok is True
    assert shell_result.state is not None
    assert (
        false_but_conserved.args["settle_long_payout"]
        + false_but_conserved.args["settle_short_payout"]
        + false_but_conserved.args["settle_protocol_fee"]
        == shell_state.premium_pool
    )
    assert shell_result.state.realized_rate_bps == false_but_conserved.args["realized_rate_bps"]
    assert shell_result.state.long_payout == false_but_conserved.args["settle_long_payout"]
    assert shell_result.state.short_payout == false_but_conserved.args["settle_short_payout"]
    assert shell_result.state.realized_rate_bps != deterministic.realized_rate_bps
    assert shell_result.state.long_payout != deterministic.long_payout
    assert shell_result.state.short_payout != deterministic.short_payout
