"""Live-path wiring tests for stateless perps-math Rust authority."""

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

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.core.perp_v2 import math as m  # noqa: E402
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
        per_surface={"perp_math": mode},
        promoted_surfaces=frozenset({"perp_math"}),
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


def test_default_python_authority_is_byte_identical():
    assert m.pnl_quote(1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE) == m._pnl_quote_python(
        1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE
    )
    assert m.funding_payment(-1_000, 100 * m.PRICE_SCALE, 50) == m._funding_payment_python(
        -1_000, 100 * m.PRICE_SCALE, 50
    )
    assert m.is_liquidatable(1_000_000, 0, 100 * m.PRICE_SCALE, 500, 0) == m._is_liquidatable_python(
        1_000_000, 0, 100 * m.PRICE_SCALE, 500, 0
    )


def test_perp_math_doc_parity_rejects_non_exact_shapes():
    value_doc = {"ok": True, "value": "10"}
    flag_doc = {"ok": True, "flag": True}
    reject_doc = {"ok": False, "code": "amount_out_of_domain"}
    assert m._perp_math_docs_agree(value_doc, dict(value_doc))
    assert m._perp_math_docs_agree(flag_doc, dict(flag_doc))
    assert m._perp_math_docs_agree(reject_doc, dict(reject_doc))

    assert not m._perp_math_docs_agree(value_doc, {**value_doc, "extra": "metadata"})
    assert not m._perp_math_docs_agree(flag_doc, {**flag_doc, "value": "1"})
    assert not m._perp_math_docs_agree(reject_doc, {**reject_doc, "value": "0"})
    assert not m._perp_math_docs_agree({"ok": 1, "value": "10"}, value_doc)


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    assert m.is_oracle_fresh(5, 0, 10, True) is True
    assert m.oracle_move_violated(110, 100, 500, True) is True
    assert m.settle_price(1_000_000, 100, 1, True) == 101
    assert m.notional_quote(-5_000, 100 * m.PRICE_SCALE) == 500_000
    assert m.maint_margin_req(-5_000, 100 * m.PRICE_SCALE, 500, 100) == 30_000
    assert m.init_margin_req(5_000, 100 * m.PRICE_SCALE, 1_000) == 50_000
    assert m.pnl_quote(1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE) == 10_000
    assert m.is_liquidatable(1_000_000, 0, 100 * m.PRICE_SCALE, 500, 0) is True
    assert m.funding_payment(-1_000, 100 * m.PRICE_SCALE, 50) == -500


def test_rust_shadow_mode_keeps_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    assert m.pnl_quote(-1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE) == -10_000


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    real = m._pnl_quote_python

    def fake_pnl(*args):
        return real(*args) + 1

    monkeypatch.setattr(m, "_pnl_quote_python", fake_pnl)
    with pytest.raises(AuthorityError):
        m.pnl_quote(1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE)


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            m.pnl_quote(1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE)
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
        assert m.pnl_quote(1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE) == 10_000
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
