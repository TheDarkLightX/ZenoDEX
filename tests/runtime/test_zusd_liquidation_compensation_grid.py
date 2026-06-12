"""zUSD liquidation compensation accounting grid.

Kani covers BigInt-free zUSD helpers. This test targets a value-moving BigInt
slice outside Kani: liquidation splits the vault collateral between stability
pool collateral and liquidator compensation.
"""

from __future__ import annotations

import os
import sys
from dataclasses import asdict
from pathlib import Path
from typing import Any

import pytest

REPO = Path(__file__).resolve().parents[2]
TOOLS_RUNTIME = REPO / "tools" / "runtime"
for _path in (str(REPO), str(TOOLS_RUNTIME)):
    if _path not in sys.path:
        sys.path.insert(0, _path)

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.core import zusd  # noqa: E402
from src.runtime.rust_invoker import zusd_op  # noqa: E402

E8 = zusd.E8
BPS = zusd.BPS_SCALE
MAX = zusd.MAX_AMOUNT_E8


def _cmd(tag: str, **args: Any) -> zusd.ZUSDCommand:
    return zusd.ZUSDCommand(tag=tag, args=args)


def _tx(tag: str, **args: Any) -> dict[str, Any]:
    return {"kind": tag, **args}


def _ceil_div(num: int, den: int) -> int:
    assert den > 0
    return (num + den - 1) // den


def _state(
    *,
    collateral_e8: int,
    debt_e8: int,
    fixed_comp_e8: int,
    variable_comp_bps: int,
    sp_coll_e8: int = 0,
    max_sp_coll_e8: int = MAX,
) -> zusd.ZUSDState:
    return zusd.ZUSDState(
        now_epoch=20,
        oracle_seen=True,
        oracle_last_update_epoch=20,
        price_e8=E8,
        price_pending_e8=E8,
        max_oracle_staleness_epochs=100,
        collateral_e8=collateral_e8,
        debt_e8=debt_e8,
        free_debt_e8=0,
        sp_debt_e8=debt_e8,
        sp_coll_e8=sp_coll_e8,
        protocol_collateral_e8=0,
        protocol_revenue_zusd_cum_e8=0,
        liquidator_compensation_collateral_cum_e8=3 * E8,
        mcr_bps=11_000,
        ccr_bps=11_000,
        min_debt_open_e8=1,
        max_debt_e8=MAX,
        max_debt_supply_e8=MAX,
        max_sp_coll_e8=max_sp_coll_e8,
        max_protocol_coll_e8=MAX,
        base_rate_bps=0,
        base_rate_last_epoch=20,
        base_rate_decay_per_epoch_bps=0,
        base_rate_borrow_bump_bps=0,
        base_rate_redeem_bump_bps=0,
        borrow_fee_floor_bps=0,
        borrow_fee_max_bps=1_000,
        redemption_fee_floor_bps=0,
        redemption_fee_max_bps=1_000,
        liquidation_gas_comp_fixed_collateral_e8=fixed_comp_e8,
        liquidation_gas_comp_bps=variable_comp_bps,
    )


def _expected_split(state: zusd.ZUSDState) -> tuple[int, int]:
    variable = _ceil_div(
        state.collateral_e8 * state.liquidation_gas_comp_bps,
        BPS,
    )
    requested = state.liquidation_gas_comp_fixed_collateral_e8 + variable
    liquidator_comp = min(state.collateral_e8, requested)
    sp_gain = state.collateral_e8 - liquidator_comp
    return liquidator_comp, sp_gain


def test_liquidation_compensation_grid_matches_integer_oracle():
    cases = [
        _state(collateral_e8=100 * E8, debt_e8=200 * E8, fixed_comp_e8=0, variable_comp_bps=0),
        _state(collateral_e8=100 * E8 + 1, debt_e8=200 * E8, fixed_comp_e8=E8, variable_comp_bps=0),
        _state(collateral_e8=123 * E8 + 1, debt_e8=250 * E8, fixed_comp_e8=0, variable_comp_bps=1),
        _state(collateral_e8=123 * E8 + 1, debt_e8=250 * E8, fixed_comp_e8=2 * E8, variable_comp_bps=5_000),
        _state(collateral_e8=50 * E8, debt_e8=200 * E8, fixed_comp_e8=100 * E8, variable_comp_bps=10_000),
    ]

    for state in cases:
        liquidator_comp, sp_gain = _expected_split(state)
        result = zusd._step_python(state, _cmd("liquidate"))
        assert result.ok, (state, result)
        assert result.state is not None
        assert result.state.debt_e8 == 0
        assert result.state.collateral_e8 == 0
        assert result.state.sp_debt_e8 == 0
        assert result.state.sp_coll_e8 == state.sp_coll_e8 + sp_gain
        assert (
            result.state.liquidator_compensation_collateral_cum_e8
            == state.liquidator_compensation_collateral_cum_e8 + liquidator_comp
        )
        assert liquidator_comp + sp_gain == state.collateral_e8


def test_liquidation_compensation_sp_cap_rejects_noop():
    state = _state(
        collateral_e8=100 * E8,
        debt_e8=200 * E8,
        fixed_comp_e8=0,
        variable_comp_bps=0,
        sp_coll_e8=10 * E8,
        max_sp_coll_e8=10 * E8 + 100 * E8 - 1,
    )
    result = zusd._step_python(state, _cmd("liquidate"))
    assert not result.ok
    assert result.error == "stability pool collateral cap exceeded"
    assert result.state is None


@pytest.fixture(scope="module")
def rust_env():
    try:
        rust_bin = locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"Rust shadow runtime unavailable: {exc}")
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(rust_bin)
    yield
    if old is None:
        os.environ.pop("ZENODEX_RUNTIME_BIN", None)
    else:
        os.environ["ZENODEX_RUNTIME_BIN"] = old


def _assert_rust_doc_matches_python(state: zusd.ZUSDState, tag: str, **args: Any) -> None:
    cmd = _cmd(tag, **args)
    tx = _tx(tag, **args)
    py_result = zusd._step_python(state, cmd)
    py_doc = zusd._result_to_authority_doc(state, cmd, py_result)
    rust_doc = zusd_op(state=zusd._state_json(state), tx=tx)
    assert rust_doc == py_doc
    if py_result.ok:
        assert py_result.state is not None
        assert asdict(py_result.state) == {
            k: (v if k == "oracle_seen" else int(v))
            for k, v in rust_doc["post_state"].items()
        }


def test_curated_liquidation_compensation_cases_match_rust_zusd_op(rust_env):
    for state in [
        _state(collateral_e8=100 * E8, debt_e8=200 * E8, fixed_comp_e8=0, variable_comp_bps=0),
        _state(collateral_e8=123 * E8 + 1, debt_e8=250 * E8, fixed_comp_e8=2 * E8, variable_comp_bps=5_000),
        _state(collateral_e8=50 * E8, debt_e8=200 * E8, fixed_comp_e8=100 * E8, variable_comp_bps=10_000),
        _state(
            collateral_e8=100 * E8,
            debt_e8=200 * E8,
            fixed_comp_e8=0,
            variable_comp_bps=0,
            sp_coll_e8=10 * E8,
            max_sp_coll_e8=10 * E8 + 100 * E8 - 1,
        ),
    ]:
        _assert_rust_doc_matches_python(state, "liquidate")
