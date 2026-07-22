"""zUSD CDP threshold grid against an independent integer oracle.

This targets the part Kani intentionally does not cover: the BigInt CDP ratio
checks around MCR, redemption floors, and liquidation eligibility. The oracle
below is deliberately small and formula-shaped; it does not call the zUSD
implementation for the admission decision.
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


def _mcr_ok_ref(*, collateral_e8: int, debt_e8: int, price_e8: int, mcr_bps: int) -> bool:
    if debt_e8 == 0:
        return True
    return collateral_e8 * price_e8 * BPS >= debt_e8 * mcr_bps * E8


def _ceil_div(num: int, den: int) -> int:
    assert den > 0
    return (num + den - 1) // den


def _state(
    *,
    collateral_e8: int,
    debt_e8: int,
    price_e8: int,
    mcr_bps: int = 11_000,
    ccr_bps: int | None = None,
    free_debt_e8: int | None = None,
    sp_debt_e8: int = 0,
    sp_coll_e8: int = 0,
    max_sp_coll_e8: int = MAX,
) -> zusd.ZUSDState:
    if free_debt_e8 is None:
        free_debt_e8 = debt_e8 - sp_debt_e8
    return zusd.ZUSDState(
        now_epoch=10,
        oracle_seen=True,
        oracle_last_update_epoch=10,
        price_e8=price_e8,
        price_pending_e8=price_e8,
        max_oracle_staleness_epochs=100,
        collateral_e8=collateral_e8,
        debt_e8=debt_e8,
        free_debt_e8=free_debt_e8,
        sp_debt_e8=sp_debt_e8,
        sp_coll_e8=sp_coll_e8,
        protocol_collateral_e8=0,
        protocol_revenue_zusd_cum_e8=0,
        liquidator_compensation_collateral_cum_e8=0,
        mcr_bps=mcr_bps,
        ccr_bps=mcr_bps if ccr_bps is None else ccr_bps,
        min_debt_open_e8=1,
        max_debt_e8=MAX,
        max_debt_supply_e8=MAX,
        max_sp_coll_e8=max_sp_coll_e8,
        max_protocol_coll_e8=MAX,
        base_rate_bps=0,
        base_rate_last_epoch=10,
        base_rate_decay_per_epoch_bps=0,
        base_rate_borrow_bump_bps=0,
        base_rate_redeem_bump_bps=0,
        borrow_fee_floor_bps=0,
        borrow_fee_max_bps=1_000,
        redemption_fee_floor_bps=0,
        redemption_fee_max_bps=1_000,
        liquidation_gas_comp_fixed_collateral_e8=0,
        liquidation_gas_comp_bps=0,
    )


def _step(state: zusd.ZUSDState, tag: str, **args: Any) -> zusd.ZUSDStepResult:
    return zusd._step_python(state, _cmd(tag, **args))


def _max_debt_at_mcr(collateral_e8: int, price_e8: int, mcr_bps: int) -> int:
    return collateral_e8 * price_e8 * BPS // (mcr_bps * E8)


def test_mint_mcr_threshold_grid_matches_integer_oracle():
    seen_accept = seen_reject = 0
    for mcr_bps in (10_000, 11_000, 15_000):
        for price_e8 in (E8 // 2, E8, E8 + 1, 2 * E8):
            for collateral_e8 in (100 * E8, 101 * E8, 150 * E8):
                max_debt = _max_debt_at_mcr(collateral_e8, price_e8, mcr_bps)
                debt_cases = {1, max_debt - 2, max_debt - 1, max_debt}
                for debt_e8 in sorted(d for d in debt_cases if d > 0):
                    assert _mcr_ok_ref(
                        collateral_e8=collateral_e8,
                        debt_e8=debt_e8,
                        price_e8=price_e8,
                        mcr_bps=mcr_bps,
                    )
                    state = _state(
                        collateral_e8=collateral_e8,
                        debt_e8=debt_e8,
                        price_e8=price_e8,
                        mcr_bps=mcr_bps,
                    )
                    amount_cases = {1, 2, max(1, max_debt - debt_e8), max(1, max_debt - debt_e8 + 1)}
                    for amount_e8 in sorted(amount_cases):
                        result = _step(state, "mint_zusd", amount_e8=amount_e8)
                        expected_ok = _mcr_ok_ref(
                            collateral_e8=collateral_e8,
                            debt_e8=debt_e8 + amount_e8,
                            price_e8=price_e8,
                            mcr_bps=mcr_bps,
                        )
                        assert result.ok is expected_ok, (mcr_bps, price_e8, collateral_e8, debt_e8, amount_e8, result)
                        if expected_ok:
                            seen_accept += 1
                            assert result.state is not None
                            assert result.state.debt_e8 == debt_e8 + amount_e8
                            assert result.state.free_debt_e8 == debt_e8 + amount_e8
                        else:
                            seen_reject += 1
                            assert result.error == "mint would violate MCR"
                            assert result.state is None
    assert (seen_accept, seen_reject) == (216, 180)


def test_withdraw_mcr_threshold_grid_matches_integer_oracle():
    seen_accept = seen_reject = 0
    for mcr_bps in (10_000, 11_000, 15_000):
        for price_e8 in (E8 // 2, E8, 2 * E8):
            for debt_e8 in (25 * E8, 50 * E8, 75 * E8):
                min_collateral = _ceil_div(debt_e8 * mcr_bps * E8, price_e8 * BPS)
                for excess in (0, 1, 2, E8):
                    collateral_e8 = min_collateral + excess
                    state = _state(
                        collateral_e8=collateral_e8,
                        debt_e8=debt_e8,
                        price_e8=price_e8,
                        mcr_bps=mcr_bps,
                    )
                    max_withdraw = collateral_e8 - min_collateral
                    amount_cases = {1, max(1, max_withdraw), max_withdraw + 1}
                    for amount_e8 in sorted(a for a in amount_cases if 0 < a <= collateral_e8):
                        result = _step(state, "withdraw_collateral", amount_e8=amount_e8)
                        expected_ok = _mcr_ok_ref(
                            collateral_e8=collateral_e8 - amount_e8,
                            debt_e8=debt_e8,
                            price_e8=price_e8,
                            mcr_bps=mcr_bps,
                        )
                        assert result.ok is expected_ok, (
                            mcr_bps,
                            price_e8,
                            debt_e8,
                            collateral_e8,
                            amount_e8,
                            result,
                        )
                        if expected_ok:
                            seen_accept += 1
                            assert result.state is not None
                            assert result.state.collateral_e8 == collateral_e8 - amount_e8
                        else:
                            seen_reject += 1
                            assert result.error == "withdraw would violate MCR"
                            assert result.state is None
    assert (seen_accept, seen_reject) == (135, 108)


def test_redeem_floor_and_accounting_grid_matches_integer_oracle():
    seen_accept = seen_reject = 0
    for price_e8 in (E8 // 2, E8, 2 * E8, 3 * E8):
        for debt_e8 in (100 * E8, 250 * E8, 500 * E8):
            collateral_e8 = _ceil_div(debt_e8 * 15_000 * E8, price_e8 * BPS) + 10 * E8
            state = _state(
                collateral_e8=collateral_e8,
                debt_e8=debt_e8,
                price_e8=price_e8,
                mcr_bps=11_000,
                ccr_bps=11_000,
            )
            amount_cases = {1, debt_e8 // 2, debt_e8, debt_e8 + 1}
            for amount_e8 in sorted(amount_cases):
                result = _step(state, "redeem_zusd", amount_e8=amount_e8)
                gross_collateral = amount_e8 * E8 // price_e8
                if amount_e8 > debt_e8:
                    expected_ok = False
                    expected_reason = "redemption exceeds debt"
                elif gross_collateral == 0:
                    expected_ok = False
                    expected_reason = "redemption amount too small at current price"
                elif gross_collateral > collateral_e8:
                    expected_ok = False
                    expected_reason = "insufficient vault collateral for redemption"
                else:
                    post_debt = debt_e8 - amount_e8
                    post_collateral = collateral_e8 - gross_collateral
                    expected_ok = _mcr_ok_ref(
                        collateral_e8=post_collateral,
                        debt_e8=post_debt,
                        price_e8=price_e8,
                        mcr_bps=11_000,
                    )
                    expected_reason = "redemption would violate MCR"
                assert result.ok is expected_ok, (price_e8, debt_e8, collateral_e8, amount_e8, result)
                if expected_ok:
                    seen_accept += 1
                    assert result.state is not None
                    assert result.state.debt_e8 == debt_e8 - amount_e8
                    assert result.state.free_debt_e8 == debt_e8 - amount_e8
                    assert result.state.collateral_e8 == collateral_e8 - gross_collateral
                    assert result.effects is not None
                    assert result.effects["redeemed_collateral_gross_e8"] == gross_collateral
                else:
                    seen_reject += 1
                    assert result.error == expected_reason
                    assert result.state is None
    assert (seen_accept, seen_reject) == (30, 18)


def test_liquidation_mcr_boundary_grid_matches_integer_oracle():
    seen_accept = seen_reject = 0
    for mcr_bps in (11_000, 15_000):
        for price_e8 in (E8 // 2, E8, 2 * E8):
            for collateral_e8 in (100 * E8, 150 * E8):
                max_mcr_debt = _max_debt_at_mcr(collateral_e8, price_e8, mcr_bps)
                max_solvent_debt = collateral_e8 * price_e8 // E8
                for debt_e8 in sorted({max_mcr_debt, max_mcr_debt + 1, max_solvent_debt}):
                    if not (0 < debt_e8 <= max_solvent_debt):
                        continue
                    state = _state(
                        collateral_e8=collateral_e8,
                        debt_e8=debt_e8,
                        free_debt_e8=0,
                        sp_debt_e8=debt_e8,
                        price_e8=price_e8,
                        mcr_bps=mcr_bps,
                    )
                    result = _step(state, "liquidate")
                    expected_ok = not _mcr_ok_ref(
                        collateral_e8=collateral_e8,
                        debt_e8=debt_e8,
                        price_e8=price_e8,
                        mcr_bps=mcr_bps,
                    )
                    assert result.ok is expected_ok, (mcr_bps, price_e8, collateral_e8, debt_e8, result)
                    if expected_ok:
                        seen_accept += 1
                        assert result.state is not None
                        assert result.state.debt_e8 == 0
                        assert result.state.collateral_e8 == 0
                        assert result.state.sp_debt_e8 == 0
                        assert result.state.sp_coll_e8 == collateral_e8
                    else:
                        seen_reject += 1
                        assert result.error == "vault not under MCR at finalized price"
                        assert result.state is None
    assert (seen_accept, seen_reject) == (24, 12)


def test_cdp_threshold_oracle_has_teeth():
    collateral_e8 = 110 * E8
    debt_e8 = 100 * E8
    assert _mcr_ok_ref(
        collateral_e8=collateral_e8,
        debt_e8=debt_e8,
        price_e8=E8,
        mcr_bps=11_000,
    )

    # A strict > comparator would reject the exact-boundary safe vault. This is
    # the planted violation the grid is meant to catch.
    strict_ok = collateral_e8 * E8 * BPS > debt_e8 * 11_000 * E8
    assert strict_ok is False


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


def test_curated_threshold_cases_match_rust_zusd_op(rust_env):
    exact_safe = _state(
        collateral_e8=110 * E8,
        debt_e8=100 * E8,
        price_e8=E8,
        mcr_bps=11_000,
    )
    under_after_mint = _state(
        collateral_e8=110 * E8,
        debt_e8=100 * E8,
        price_e8=E8,
        mcr_bps=11_000,
    )
    under_liquidatable = _state(
        collateral_e8=110 * E8,
        debt_e8=100 * E8 + 1,
        free_debt_e8=0,
        sp_debt_e8=100 * E8 + 1,
        price_e8=E8,
        mcr_bps=11_000,
    )
    redeem_small = _state(
        collateral_e8=200 * E8,
        debt_e8=100 * E8,
        price_e8=2 * E8,
        mcr_bps=11_000,
    )

    _assert_rust_doc_matches_python(exact_safe, "mint_zusd", amount_e8=1)
    _assert_rust_doc_matches_python(under_after_mint, "withdraw_collateral", amount_e8=1)
    _assert_rust_doc_matches_python(under_liquidatable, "liquidate")
    _assert_rust_doc_matches_python(redeem_small, "redeem_zusd", amount_e8=1)
    _assert_rust_doc_matches_python(redeem_small, "redeem_zusd", amount_e8=50 * E8)
