"""Deterministic CPMM arithmetic grids for the division-heavy swap formulas."""

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
_TOOLS_RUNTIME = _REPO / "tools" / "runtime"
for _path in (str(_REPO), str(_TOOLS_RUNTIME)):
    if _path not in sys.path:
        sys.path.insert(0, _path)

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.kernels.python.settlement_swap_runtime_v1 import (  # noqa: E402
    BPS_DENOM,
    SettlementSwapExactInQuote,
    SettlementSwapExactOutQuote,
    _quote_cpmm_swap_exact_in_python,
    _quote_cpmm_swap_exact_out_python,
    _quote_error_code,
)
from src.runtime.rust_invoker import cpmm_op  # noqa: E402


FEE_GRID = [0, 1, 30, 5_000, 9_999, BPS_DENOM]


def _ceil_div(numerator: int, denominator: int) -> int:
    assert numerator >= 0 and denominator > 0
    return (numerator + denominator - 1) // denominator


def _ref_exact_in(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_in: int,
    fee_bps: int,
) -> tuple[bool, str, dict]:
    fee_paid = _ceil_div(amount_in * fee_bps, BPS_DENOM)
    if fee_paid >= amount_in:
        return False, "trade_too_small", {}
    net_in = amount_in - fee_paid
    amount_out = (reserve_out * net_in) // (reserve_in + net_in)
    if amount_out <= 0:
        return False, "trade_too_small", {}
    reserve_in_after = reserve_in + amount_in
    reserve_out_after = reserve_out - amount_out
    k_before = reserve_in * reserve_out
    k_after = reserve_in_after * reserve_out_after
    assert k_after >= k_before
    return (
        True,
        "ok",
        {
            "amount_in": amount_in,
            "amount_out": amount_out,
            "fee_paid": fee_paid,
            "net_in": net_in,
            "reserve_in_before": reserve_in,
            "reserve_out_before": reserve_out,
            "reserve_in_after": reserve_in_after,
            "reserve_out_after": reserve_out_after,
            "k_before": k_before,
            "k_after": k_after,
        },
    )


def _ref_exact_out(
    *,
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_overdelivery_gap_bps: int,
) -> tuple[bool, str, dict]:
    if amount_out >= reserve_out:
        return False, "amount_out_ge_reserve", {}
    if fee_bps == BPS_DENOM:
        return False, "fee_full", {}

    net_in_required = _ceil_div(reserve_in * amount_out, reserve_out - amount_out)
    amount_in = _ceil_div(net_in_required * BPS_DENOM, BPS_DENOM - fee_bps)
    fee_paid = _ceil_div(amount_in * fee_bps, BPS_DENOM)
    net_in_actual = amount_in - fee_paid
    amount_out_quote = (reserve_out * net_in_actual) // (reserve_in + net_in_actual)
    if amount_out_quote < amount_out:
        return False, "invariant_violation", {}
    overdelivery_gap = max(0, amount_out_quote - amount_out)
    gap_bps = _ceil_div(overdelivery_gap * BPS_DENOM, amount_out)
    if gap_bps > max_overdelivery_gap_bps:
        return False, "overdelivery_gap", {}

    reserve_in_after = reserve_in + amount_in
    reserve_out_after = reserve_out - amount_out
    k_before = reserve_in * reserve_out
    k_after = reserve_in_after * reserve_out_after
    assert k_after >= k_before
    return (
        True,
        "ok",
        {
            "amount_in": amount_in,
            "amount_out": amount_out,
            "amount_out_quote": amount_out_quote,
            "overdelivery_gap": overdelivery_gap,
            "gap_bps": gap_bps,
            "fee_paid": fee_paid,
            "net_in_actual": net_in_actual,
            "reserve_in_before": reserve_in,
            "reserve_out_before": reserve_out,
            "reserve_in_after": reserve_in_after,
            "reserve_out_after": reserve_out_after,
            "k_before": k_before,
            "k_after": k_after,
        },
    )


def _quote_exact_in_doc(
    reserve_in: int, reserve_out: int, amount_in: int, fee_bps: int
) -> tuple[bool, str, dict]:
    try:
        q = _quote_cpmm_swap_exact_in_python(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_in=amount_in,
            fee_bps=fee_bps,
        )
    except (TypeError, ValueError) as exc:
        return False, _quote_error_code(str(exc)), {}
    assert isinstance(q, SettlementSwapExactInQuote)
    return True, "ok", q.__dict__


def _quote_exact_out_doc(
    reserve_in: int,
    reserve_out: int,
    amount_out: int,
    fee_bps: int,
    max_overdelivery_gap_bps: int,
) -> tuple[bool, str, dict]:
    try:
        q = _quote_cpmm_swap_exact_out_python(
            reserve_in=reserve_in,
            reserve_out=reserve_out,
            amount_out=amount_out,
            fee_bps=fee_bps,
            max_overdelivery_gap_bps=max_overdelivery_gap_bps,
        )
    except (TypeError, ValueError) as exc:
        return False, _quote_error_code(str(exc)), {}
    assert isinstance(q, SettlementSwapExactOutQuote)
    return True, "ok", q.__dict__


def test_exact_in_small_domain_grid_matches_independent_reference() -> None:
    accepted = rejected = 0
    for reserve_in in range(1, 13):
        for reserve_out in range(1, 13):
            for amount_in in range(1, 13):
                for fee_bps in FEE_GRID:
                    expected = _ref_exact_in(
                        reserve_in=reserve_in,
                        reserve_out=reserve_out,
                        amount_in=amount_in,
                        fee_bps=fee_bps,
                    )
                    actual = _quote_exact_in_doc(
                        reserve_in, reserve_out, amount_in, fee_bps
                    )
                    assert actual == expected
                    if actual[0]:
                        accepted += 1
                    else:
                        rejected += 1
    assert accepted == 5_196
    assert rejected == 5_172


def test_exact_out_small_domain_grid_matches_independent_reference() -> None:
    max_gap_bps = BPS_DENOM
    accepted = rejected = 0
    for reserve_in in range(1, 13):
        for reserve_out in range(2, 13):
            for amount_out in range(1, reserve_out):
                for fee_bps in FEE_GRID:
                    expected = _ref_exact_out(
                        reserve_in=reserve_in,
                        reserve_out=reserve_out,
                        amount_out=amount_out,
                        fee_bps=fee_bps,
                        max_overdelivery_gap_bps=max_gap_bps,
                    )
                    actual = _quote_exact_out_doc(
                        reserve_in,
                        reserve_out,
                        amount_out,
                        fee_bps,
                        max_gap_bps,
                    )
                    assert actual == expected
                    if actual[0]:
                        accepted += 1
                    else:
                        rejected += 1
    assert accepted == 3_885
    assert rejected == 867


def test_exact_out_fee_inverse_is_z3_checked_on_bounded_domain() -> None:
    z3 = pytest.importorskip("z3")

    net_in, fee_bps = z3.Ints("net_in fee_bps")
    fee_den = BPS_DENOM - fee_bps
    gross_in = (net_in * BPS_DENOM + fee_den - 1) / fee_den
    fee_paid = (gross_in * fee_bps + BPS_DENOM - 1) / BPS_DENOM

    solver = z3.Solver()
    solver.set(timeout=5_000)
    solver.add(1 <= net_in, net_in <= 200)
    solver.add(0 <= fee_bps, fee_bps < BPS_DENOM)
    solver.add(gross_in - fee_paid != net_in)

    assert solver.check() == z3.unsat


@pytest.fixture(scope="module")
def rust_env():
    try:
        bin_path = locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"rust runtime unavailable: {exc}")
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(bin_path)
    yield
    if old is None:
        os.environ.pop("ZENODEX_RUNTIME_BIN", None)
    else:
        os.environ["ZENODEX_RUNTIME_BIN"] = old


def _pool_doc(reserve_in: int, reserve_out: int, fee_bps: int) -> dict:
    return {
        "initialized": True,
        "reserve0": reserve_in,
        "reserve1": reserve_out,
        "fee_bps": fee_bps,
    }


def _assert_rust_exact_in_case(
    reserve_in: int, reserve_out: int, amount_in: int, fee_bps: int
) -> None:
    expected = _ref_exact_in(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_in=amount_in,
        fee_bps=fee_bps,
    )
    out = cpmm_op(
        pool=_pool_doc(reserve_in, reserve_out, fee_bps),
        tx={
            "kind": "swap_exact_in",
            "zero_for_one": True,
            "amount_in": amount_in,
            "min_amount_out": 0,
        },
    )
    if not expected[0]:
        assert out["accept"] is False
        assert out["reject_reason"] == expected[1]
        return

    quote = expected[2]
    receipt = out["receipt"]
    assert out["accept"] is True
    assert int(receipt["amount_in"]) == quote["amount_in"]
    assert int(receipt["amount_out"]) == quote["amount_out"]
    assert int(receipt["fee_total"]) == quote["fee_paid"]
    assert int(receipt["new_reserve0"]) == quote["reserve_in_after"]
    assert int(receipt["new_reserve1"]) == quote["reserve_out_after"]


def _assert_rust_exact_out_case(
    reserve_in: int, reserve_out: int, amount_out: int, fee_bps: int
) -> None:
    expected = _ref_exact_out(
        reserve_in=reserve_in,
        reserve_out=reserve_out,
        amount_out=amount_out,
        fee_bps=fee_bps,
        max_overdelivery_gap_bps=BPS_DENOM,
    )
    out = cpmm_op(
        pool=_pool_doc(reserve_in, reserve_out, fee_bps),
        tx={
            "kind": "swap_exact_out",
            "zero_for_one": True,
            "amount_out": amount_out,
            "max_amount_in": 2**128 - 1,
            "max_overdelivery_gap_bps": BPS_DENOM,
        },
    )
    if not expected[0]:
        assert out["accept"] is False
        assert out["reject_reason"] == expected[1]
        return

    quote = expected[2]
    receipt = out["receipt"]
    assert out["accept"] is True
    assert int(receipt["amount_in"]) == quote["amount_in"]
    assert int(receipt["amount_out"]) == quote["amount_out"]
    assert int(receipt["amount_out_quote"]) == quote["amount_out_quote"]
    assert int(receipt["overdelivery_gap"]) == quote["overdelivery_gap"]
    assert int(receipt["gap_bps"]) == quote["gap_bps"]
    assert int(receipt["fee_total"]) == quote["fee_paid"]
    assert int(receipt["new_reserve0"]) == quote["reserve_in_after"]
    assert int(receipt["new_reserve1"]) == quote["reserve_out_after"]


def test_curated_exact_grid_cases_match_rust(rust_env) -> None:
    exact_in_cases = [
        (1, 2, 1, 0),
        (1, 4, 1, 30),
        (2, 5, 2, 5_000),
        (12, 12, 1, 9_999),
        (12, 12, 12, BPS_DENOM),
        (3, 12, 2, 1),
        (12, 3, 6, 30),
        (3, 3, 1, 9_999),
    ]
    exact_out_cases = [
        (1, 2, 1, 0),
        (1, 4, 1, 30),
        (2, 5, 2, 5_000),
        (12, 12, 1, 9_999),
        (12, 12, 11, BPS_DENOM),
        (3, 12, 2, 1),
        (12, 3, 1, 30),
        (3, 3, 1, 9_999),
    ]

    for case in exact_in_cases:
        _assert_rust_exact_in_case(*case)
    for case in exact_out_cases:
        _assert_rust_exact_out_case(*case)
