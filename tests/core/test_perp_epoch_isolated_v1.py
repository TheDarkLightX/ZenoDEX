"""Tests for the v1 kernel via the spec-interpreter backend.

These tests are optional and only run when the kernel-spec toolchain is available
(Python package `ESSO`, either installed or present under `external/ESSO`).
"""

from __future__ import annotations

import importlib.util

import pytest

from src.core.perp_epoch import perp_epoch_isolated_v1_apply, perp_epoch_isolated_v1_initial_state


if importlib.util.find_spec("ESSO") is None:  # pragma: no cover
    pytest.skip(
        "kernel toolchain package not installed (Python package `ESSO`; expected via external/ESSO or site package)",
        allow_module_level=True,
    )


def _apply_ok(state: dict, *, action: str, params: dict | None = None) -> tuple[dict, dict]:
    res = perp_epoch_isolated_v1_apply(state=state, action=action, params=params or {})
    assert res.ok is True, f"{action} failed: code={res.code} err={res.error}"
    assert res.state is not None
    assert res.effects is not None
    return res.state, res.effects


def test_perp_epoch_isolated_v1_initial_state_shape() -> None:
    st = perp_epoch_isolated_v1_initial_state()
    assert st["now_epoch"] == 0
    assert st["position_base"] == 0
    assert st["collateral_quote"] == 0
    assert st["oracle_seen"] is False


def test_perp_epoch_isolated_v1_set_position_requires_oracle() -> None:
    st = perp_epoch_isolated_v1_initial_state()
    res = perp_epoch_isolated_v1_apply(
        state=st,
        action="set_position",
        params={"new_position_base": 1, "auth_ok": True},
    )
    assert res.ok is False
    assert res.code == "GuardFalse"


def test_perp_epoch_isolated_v1_one_step_bounded_move_keeps_collateral_nonnegative() -> None:
    st = perp_epoch_isolated_v1_initial_state()

    # Epoch 1: establish oracle/index price at 1.00 and open a position.
    st, _ = _apply_ok(st, action="advance_epoch", params={"delta": 1})
    st, _ = _apply_ok(st, action="publish_clearing_price", params={"price_e8": 100_000_000})
    st, _ = _apply_ok(st, action="settle_epoch")

    st, _ = _apply_ok(st, action="deposit_collateral", params={"amount": 10, "auth_ok": True})
    st, _ = _apply_ok(st, action="set_position", params={"new_position_base": 100, "auth_ok": True})
    assert st["position_base"] == 100
    assert st["collateral_quote"] == 10

    # Epoch 2: 5% down move (max_oracle_move_bps default is 500).
    st, _ = _apply_ok(st, action="advance_epoch", params={"delta": 1})
    st, _ = _apply_ok(st, action="publish_clearing_price", params={"price_e8": 95_000_000})
    st, eff = _apply_ok(st, action="settle_epoch")

    assert st["index_price_e8"] == 95_000_000
    assert st["position_base"] == 100
    assert st["collateral_quote"] >= 0
    assert eff.get("event") == "EpochSettled"
    assert eff.get("collateral_after") == st["collateral_quote"]
