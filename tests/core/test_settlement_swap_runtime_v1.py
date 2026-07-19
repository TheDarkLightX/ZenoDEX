# [TESTER] v1

from __future__ import annotations

import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from src.kernels.python import settlement_swap_runtime_v1 as runtime_mod
from src.kernels.python.settlement_swap_runtime_v1 import (
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)


def _load_ml_bva_cases(filename: str) -> list[dict[str, object]]:
    path = Path("tests/kernels/data") / filename
    obj = json.loads(path.read_text(encoding="utf-8"))
    cases = obj.get("cases")
    assert isinstance(cases, list) and cases
    return [row for row in cases if isinstance(row, dict)]


def test_quote_cpmm_swap_exact_in_matches_accepting_ml_bva_cases() -> None:
    success_rows = 0
    for row in _load_ml_bva_cases("settlement_swap_apply_witness_v1_ml_bva_cases.json"):
        expected = row.get("expected")
        if not isinstance(expected, dict) or not expected.get("ok", False):
            continue
        pre_state = row.get("pre_state")
        params = row.get("params")
        state = expected.get("state")
        effects = expected.get("effects")
        assert isinstance(pre_state, dict)
        assert isinstance(params, dict)
        assert isinstance(state, dict)
        assert isinstance(effects, dict)

        quote = quote_cpmm_swap_exact_in(
            reserve_in=int(pre_state["reserve_in"]),
            reserve_out=int(pre_state["reserve_out"]),
            amount_in=int(params["amount_in"]),
            fee_bps=int(pre_state["fee_bps"]),
        )

        assert quote.amount_in == int(params["amount_in"])
        assert quote.amount_out == int(effects["amount_out"])
        assert quote.fee_paid == int(effects["fee_paid"])
        assert quote.net_in == int(effects["net_in"])
        assert quote.reserve_in_before == int(pre_state["reserve_in"])
        assert quote.reserve_out_before == int(pre_state["reserve_out"])
        assert quote.reserve_in_after == int(state["reserve_in"])
        assert quote.reserve_out_after == int(state["reserve_out"])
        assert quote.k_before == int(effects["k_before"])
        assert quote.k_after == int(effects["k_after"])
        success_rows += 1

    assert success_rows > 0


def test_quote_cpmm_swap_exact_out_matches_accepting_ml_bva_cases() -> None:
    success_rows = 0
    for row in _load_ml_bva_cases("settlement_swap_exact_out_apply_witness_v1_ml_bva_cases.json"):
        expected = row.get("expected")
        if not isinstance(expected, dict) or not expected.get("ok", False):
            continue
        pre_state = row.get("pre_state")
        params = row.get("params")
        state = expected.get("state")
        effects = expected.get("effects")
        assert isinstance(pre_state, dict)
        assert isinstance(params, dict)
        assert isinstance(state, dict)
        assert isinstance(effects, dict)

        quote = quote_cpmm_swap_exact_out(
            reserve_in=int(pre_state["reserve_in"]),
            reserve_out=int(pre_state["reserve_out"]),
            amount_out=int(params["amount_out"]),
            fee_bps=int(pre_state["fee_bps"]),
        )

        assert quote.amount_in == int(effects["amount_in"])
        assert quote.amount_out == int(effects["amount_out"])
        assert quote.amount_out_quote == int(effects["amount_out_quote"])
        assert quote.overdelivery_gap == int(effects["overdelivery_gap"])
        assert quote.gap_bps == int(effects["gap_bps"])
        assert quote.fee_paid == int(effects["fee_paid"])
        assert quote.net_in_actual == int(effects["net_in_actual"])
        assert quote.reserve_in_before == int(pre_state["reserve_in"])
        assert quote.reserve_out_before == int(pre_state["reserve_out"])
        assert quote.reserve_in_after == int(state["reserve_in"])
        assert quote.reserve_out_after == int(state["reserve_out"])
        assert quote.k_before == int(effects["k_before"])
        assert quote.k_after == int(effects["k_after"])
        success_rows += 1

    assert success_rows > 0


def test_quote_cpmm_swap_exact_in_rejects_domain_overflow() -> None:
    with pytest.raises(ValueError, match="swap would exceed reserve_in domain max"):
        quote_cpmm_swap_exact_in(
            reserve_in=3_000_000_000,
            reserve_out=3_000_000_000,
            amount_in=2,
            fee_bps=0,
        )


def test_quote_cpmm_swap_exact_in_accepts_fee_adjusted_post_reserve_boundary() -> None:
    quote = quote_cpmm_swap_exact_in(
        reserve_in=3_000_000_000 - 1,
        reserve_out=3_000_000_000,
        amount_in=2,
        fee_bps=5_000,
        protocol_fee_share_bps=10_000,
    )

    assert quote.fee_paid == 1
    assert quote.protocol_fee_paid == 1
    assert quote.amount_out == 1
    assert quote.reserve_in_after == 3_000_000_000


def test_quote_cpmm_swap_exact_out_rejects_post_reserve_overflow() -> None:
    with pytest.raises(ValueError, match="swap would exceed reserve_in domain max"):
        quote_cpmm_swap_exact_out(
            reserve_in=3_000_000_000,
            reserve_out=3_000_000_000,
            amount_out=1,
            fee_bps=0,
        )


def test_quote_cpmm_swap_exact_out_accepts_fee_adjusted_post_reserve_boundary() -> None:
    quote = quote_cpmm_swap_exact_out(
        reserve_in=3_000_000_000 - 1,
        reserve_out=3_000_000_000,
        amount_out=1,
        fee_bps=5_000,
        protocol_fee_share_bps=10_000,
    )

    assert quote.amount_in == 2
    assert quote.fee_paid == 1
    assert quote.protocol_fee_paid == 1
    assert quote.reserve_in_after == 3_000_000_000
    assert quote.reserve_out_after == 3_000_000_000 - 1


def test_quote_cpmm_swap_exact_out_rejects_computed_amount_in_overflow() -> None:
    with pytest.raises(ValueError, match="amount_in exceeds kernel domain max 3000000000"):
        quote_cpmm_swap_exact_out(
            reserve_in=3_000_000_000,
            reserve_out=2,
            amount_out=1,
            fee_bps=30,
        )


class _ExecutableInt(int):
    def __mul__(self, _other: object) -> int:
        return 0


def test_settlement_runtime_rejects_executable_int_subclasses() -> None:
    with pytest.raises(TypeError, match="amount_in must be an int"):
        quote_cpmm_swap_exact_in(
            reserve_in=1_000,
            reserve_out=1_000,
            amount_in=_ExecutableInt(100),
            fee_bps=30,
        )


@pytest.mark.parametrize(
    ("kwargs", "exc_type", "pattern"),
    [
        (
            {"reserve_in": False, "reserve_out": 10, "amount_in": 1, "fee_bps": 30},
            TypeError,
            "reserve_in must be an int",
        ),
        (
            {"reserve_in": 10, "reserve_out": 10, "amount_in": 0, "fee_bps": 30},
            ValueError,
            "amount_in must be >= 1",
        ),
        (
            {"reserve_in": 10, "reserve_out": 10, "amount_in": 1, "fee_bps": 10001},
            ValueError,
            "fee_bps exceeds kernel domain max 10000",
        ),
    ],
)
def test_quote_cpmm_swap_exact_in_rejects_bad_types_and_bounds(kwargs, exc_type, pattern) -> None:
    with pytest.raises(exc_type, match=pattern):
        quote_cpmm_swap_exact_in(**kwargs)


def test_quote_cpmm_swap_exact_out_rejects_known_overdelivery_policy_case() -> None:
    with pytest.raises(ValueError, match="overdelivery gap exceeds bps policy"):
        quote_cpmm_swap_exact_out(
            reserve_in=1,
            reserve_out=4,
            amount_out=1,
            fee_bps=30,
        )


@pytest.mark.parametrize(
    ("kwargs", "exc_type", "pattern"),
    [
        (
            {"reserve_in": 10, "reserve_out": 10, "amount_out": 1, "fee_bps": 30, "max_overdelivery_gap_bps": False},
            TypeError,
            "max_overdelivery_gap_bps must be an int",
        ),
        (
            {"reserve_in": 10, "reserve_out": 10, "amount_out": 0, "fee_bps": 30},
            ValueError,
            "amount_out must be >= 1",
        ),
        (
            {"reserve_in": 10, "reserve_out": 10, "amount_out": 1, "fee_bps": 30, "max_overdelivery_gap_bps": 10001},
            ValueError,
            "max_overdelivery_gap_bps exceeds kernel domain max 10000",
        ),
    ],
)
def test_quote_cpmm_swap_exact_out_rejects_bad_types_and_bounds(kwargs, exc_type, pattern) -> None:
    with pytest.raises(exc_type, match=pattern):
        quote_cpmm_swap_exact_out(**kwargs)


def test_quote_cpmm_swap_exact_in_rejects_k_regression(monkeypatch) -> None:
    monkeypatch.setattr(
        runtime_mod,
        "_kernel_swap_exact_in_v8",
        lambda **_kwargs: SimpleNamespace(
            amount_out=1,
            fee_total=0,
            net_in=1,
            new_reserve_in=11,
            new_reserve_out=9,
            k_before=100,
            k_after=99,
        ),
    )

    with pytest.raises(ValueError, match="Invariant violation"):
        quote_cpmm_swap_exact_in(
            reserve_in=10,
            reserve_out=10,
            amount_in=1,
            fee_bps=30,
        )


def test_quote_cpmm_swap_exact_out_rejects_k_regression(monkeypatch) -> None:
    monkeypatch.setattr(
        runtime_mod,
        "_kernel_swap_exact_out_v8",
        lambda **_kwargs: SimpleNamespace(
            amount_in=2,
            amount_out=1,
            amount_out_quote=1,
            overdelivery_gap=0,
            fee_total=1,
            net_in=1,
            new_reserve_in=12,
            new_reserve_out=9,
            k_before=100,
            k_after=99,
        ),
    )

    with pytest.raises(ValueError, match="Invariant violation"):
        quote_cpmm_swap_exact_out(
            reserve_in=10,
            reserve_out=10,
            amount_out=1,
            fee_bps=30,
        )
