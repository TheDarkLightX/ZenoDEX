"""Replay Julia-generated CPMM arithmetic witnesses.

Julia is used here as an offline mechanical-scientist lane: generate exact
integer witnesses, then replay them against the Python quote authority and the
Rust `cpmm-op` bridge. The generator is not imported by runtime code.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path
from typing import Any

import pytest

_REPO = Path(__file__).resolve().parents[2]
_TOOLS_RUNTIME = _REPO / "tools" / "runtime"
for _path in (str(_REPO), str(_TOOLS_RUNTIME)):
    if _path not in sys.path:
        sys.path.insert(0, _path)

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.kernels.python.settlement_swap_runtime_v1 import (  # noqa: E402
    _quote_cpmm_swap_exact_in_python,
    _quote_cpmm_swap_exact_out_python,
    _quote_error_code,
)
from src.runtime.rust_invoker import cpmm_op  # noqa: E402


def _load_julia_witnesses() -> dict[str, Any]:
    julia = shutil.which("julia")
    if julia is None:
        pytest.skip("Julia is not available")
    raw = subprocess.check_output(
        [julia, str(_REPO / "tools/runtime/cpmm_julia_witnesses.jl")],
        cwd=_REPO,
        text=True,
    )
    doc = json.loads(raw)
    assert doc["schema"] == "zenodex.cpmm_julia_witnesses.v1"
    assert doc["case_count"] == len(doc["cases"]) == 14
    return doc


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


def _assert_receipt_fields(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    for key, value in expected.items():
        assert int(actual[key]) == value, key


def _assert_post_pool(actual: dict[str, Any], expected: dict[str, Any]) -> None:
    assert actual["initialized"] is expected["initialized"]
    for key in ("reserve0", "reserve1", "fee_bps"):
        assert int(actual[key]) == expected[key], key


def _assert_rust_matches(case: dict[str, Any]) -> None:
    out = cpmm_op(pool=case["pool"], tx=case["tx"])
    expected = case["expect"]
    assert out["accept"] is expected["accept"], case["name"]
    if not expected["accept"]:
        assert out["reject_reason"] == expected["reject_reason"], case["name"]
        return

    assert out["reject_reason"] is None
    _assert_receipt_fields(out["receipt"], expected["receipt"])
    _assert_post_pool(out["post_pool"], expected["post_pool"])


def _assert_python_quote_matches(case: dict[str, Any]) -> None:
    pool = case["pool"]
    tx = case["tx"]
    expected = case["expect"]
    reject_reason = expected.get("reject_reason")

    if case["op"] == "swap_exact_in":
        try:
            quote = _quote_cpmm_swap_exact_in_python(
                reserve_in=pool["reserve0"],
                reserve_out=pool["reserve1"],
                amount_in=tx["amount_in"],
                fee_bps=pool["fee_bps"],
            )
        except (TypeError, ValueError) as exc:
            assert not expected["accept"], case["name"]
            assert _quote_error_code(str(exc)) == reject_reason, case["name"]
            return

        if reject_reason == "slippage":
            assert quote.amount_out < tx["min_amount_out"], case["name"]
            return
        assert expected["accept"], case["name"]
        receipt = expected["receipt"]
        assert quote.amount_in == receipt["amount_in"]
        assert quote.amount_out == receipt["amount_out"]
        assert quote.fee_paid == receipt["fee_total"]
        assert quote.reserve_in_after == receipt["new_reserve0"]
        assert quote.reserve_out_after == receipt["new_reserve1"]
        return

    try:
        quote = _quote_cpmm_swap_exact_out_python(
            reserve_in=pool["reserve0"],
            reserve_out=pool["reserve1"],
            amount_out=tx["amount_out"],
            fee_bps=pool["fee_bps"],
            max_overdelivery_gap_bps=tx["max_overdelivery_gap_bps"],
        )
    except (TypeError, ValueError) as exc:
        assert not expected["accept"], case["name"]
        assert _quote_error_code(str(exc)) == reject_reason, case["name"]
        return

    if reject_reason == "slippage":
        assert quote.amount_in > tx["max_amount_in"], case["name"]
        return
    assert expected["accept"], case["name"]
    receipt = expected["receipt"]
    assert quote.amount_in == receipt["amount_in"]
    assert quote.amount_out == receipt["amount_out"]
    assert quote.amount_out_quote == receipt["amount_out_quote"]
    assert quote.overdelivery_gap == receipt["overdelivery_gap"]
    assert quote.gap_bps == receipt["gap_bps"]
    assert quote.fee_paid == receipt["fee_total"]
    assert quote.reserve_in_after == receipt["new_reserve0"]
    assert quote.reserve_out_after == receipt["new_reserve1"]


def test_julia_cpmm_witnesses_match_python_and_rust(rust_env) -> None:
    doc = _load_julia_witnesses()
    accepted = rejected = 0
    for case in doc["cases"]:
        _assert_python_quote_matches(case)
        _assert_rust_matches(case)
        if case["expect"]["accept"]:
            accepted += 1
        else:
            rejected += 1

    assert accepted == 6
    assert rejected == 8
