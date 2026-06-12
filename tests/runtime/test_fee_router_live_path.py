"""Live-path wiring tests for fee-router Rust authority."""

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
_TOOLS_RUNTIME = _REPO / "tools" / "runtime"
for _p in (str(_REPO), str(_TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

import src.core.fee_router as fee_router  # noqa: E402
from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.core.fee_router import (  # noqa: E402
    FeeAccumulator,
    FeeSplitTable,
    RouteAccepted,
    RouteRejected,
    _result_to_authority_doc,
    _route_fee_python,
    canonical_split_table,
    route_fee,
)
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"fee_router": mode},
        promoted_surfaces=frozenset({"fee_router"}),
    )


@pytest.fixture(autouse=True)
def _reset_policy_after():
    yield
    reset_active_authority_policy()


@pytest.fixture(scope="module")
def rust_env():
    try:
        bin_path = locate_or_build_cli(allow_build=True)
    except ShadowError as exc:  # pragma: no cover - environment dependent
        pytest.skip(f"rust runtime unavailable: {exc}")
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(bin_path)
    yield bin_path
    if old is None:
        os.environ.pop("ZENODEX_RUNTIME_BIN", None)
    else:
        os.environ["ZENODEX_RUNTIME_BIN"] = old


def _assert_same(pre: FeeAccumulator, left, right) -> None:
    assert _result_to_authority_doc(pre, left) == _result_to_authority_doc(pre, right)


def test_default_python_authority_is_byte_identical():
    acc = FeeAccumulator()
    table = canonical_split_table("dex")
    expected = _route_fee_python(
        source="dex", asset="zUSD", amount=12_347, split_table=table, accumulator=acc
    )
    observed = route_fee(
        source="dex", asset="zUSD", amount=12_347, split_table=table, accumulator=acc
    )
    _assert_same(acc, expected, observed)


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    acc = FeeAccumulator()
    txs = [
        ("dex", "zUSD", 1_000_000, canonical_split_table("dex")),
        ("perps", "zUSD", 12_347, canonical_split_table("perps")),
        ("borrow", "zUSD", 10_000, canonical_split_table("borrow")),
        ("redemption", "AGRS", 10_000, canonical_split_table("redemption")),
        ("dex", "zUSD", 3, canonical_split_table("dex")),
        ("dex", "zUSD", 9_999, canonical_split_table("dex")),
        ("dex", "zUSD", -1, canonical_split_table("dex")),
        ("redemption", "AGRS", 1_000, FeeSplitTable(1, 5_999, 4_000, 0)),
    ]
    for source, asset, amount, table in txs:
        expected = _route_fee_python(
            source=source, asset=asset, amount=amount, split_table=table, accumulator=acc
        )
        observed = route_fee(
            source=source, asset=asset, amount=amount, split_table=table, accumulator=acc
        )
        _assert_same(acc, expected, observed)
        if isinstance(observed, RouteAccepted):
            acc = observed.accumulator


def test_rust_shadow_mode_keeps_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    acc = FeeAccumulator()
    table = canonical_split_table("dex")
    observed = route_fee(
        source="dex", asset="zUSD", amount=100, split_table=table, accumulator=acc
    )
    expected = _route_fee_python(
        source="dex", asset="zUSD", amount=100, split_table=table, accumulator=acc
    )
    assert isinstance(observed, RouteAccepted)
    assert observed.accumulator.state_root() == expected.accumulator.state_root()


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def fake_route(**kwargs):
        return RouteRejected("unknown_domain")

    monkeypatch.setattr(fee_router, "_route_fee_python", fake_route)
    with pytest.raises(AuthorityError):
        route_fee(
            source="dex",
            asset="zUSD",
            amount=100,
            split_table=canonical_split_table("dex"),
            accumulator=FeeAccumulator(),
        )


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            route_fee(
                source="dex",
                asset="zUSD",
                amount=1,
                split_table=canonical_split_table("dex"),
                accumulator=FeeAccumulator(),
            )
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old


def test_rust_shadow_unavailable_keeps_python():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
        result = route_fee(
            source="dex",
            asset="zUSD",
            amount=1,
            split_table=canonical_split_table("dex"),
            accumulator=FeeAccumulator(),
        )
        assert isinstance(result, RouteAccepted)
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
