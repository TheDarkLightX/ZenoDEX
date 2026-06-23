"""Live-path wiring tests for CPMM settlement Rust authority."""

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
from src.kernels.python import settlement_swap_runtime_v1 as cpmm_runtime  # noqa: E402
from src.kernels.python.settlement_swap_runtime_v1 import (  # noqa: E402
    CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
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
        per_surface={"cpmm_settlement": mode},
        promoted_surfaces=frozenset({"cpmm_settlement"}),
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
    assert quote_cpmm_swap_exact_in(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
    ) == cpmm_runtime._quote_cpmm_swap_exact_in_python(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
    )
    assert quote_cpmm_swap_exact_out(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_out=5_000,
        fee_bps=30,
    ) == cpmm_runtime._quote_cpmm_swap_exact_out_python(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_out=5_000,
        fee_bps=30,
    )


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    exact_in = quote_cpmm_swap_exact_in(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
    )
    assert exact_in.amount_out == 9_871
    assert exact_in.k_after >= exact_in.k_before

    exact_out = quote_cpmm_swap_exact_out(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_out=5_000,
        fee_bps=30,
    )
    assert exact_out.amount_in == 5_042
    assert exact_out.k_after >= exact_out.k_before

    with pytest.raises(ValueError, match="overdelivery gap exceeds bps policy"):
        quote_cpmm_swap_exact_out(
            reserve_in=1,
            reserve_out=4,
            amount_out=1,
            fee_bps=30,
            max_overdelivery_gap_bps=CPMM_EXACT_OUT_MAX_OVERDELIVERY_GAP_BPS_DEFAULT,
        )


def test_rust_authority_with_python_shadow_agrees_on_allowed_overdelivery(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    quote = quote_cpmm_swap_exact_out(
        reserve_in=1,
        reserve_out=4,
        amount_out=1,
        fee_bps=30,
        max_overdelivery_gap_bps=10_000,
    )
    assert quote.amount_in == 2
    assert quote.amount_out_quote == 2
    assert quote.overdelivery_gap == 1
    assert quote.gap_bps == 10_000


def test_rust_shadow_mode_keeps_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    observed = quote_cpmm_swap_exact_in(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
    )
    expected = cpmm_runtime._quote_cpmm_swap_exact_in_python(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
    )
    assert observed == expected


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    real = cpmm_runtime._quote_cpmm_swap_exact_in_python

    def fake_python(**kwargs):
        quote = real(**kwargs)
        return type(quote)(**{**quote.__dict__, "amount_out": quote.amount_out + 1})

    monkeypatch.setattr(cpmm_runtime, "_quote_cpmm_swap_exact_in_python", fake_python)
    with pytest.raises(AuthorityError):
        quote_cpmm_swap_exact_in(
            reserve_in=1_000_000,
            reserve_out=1_000_000,
            amount_in=10_000,
            fee_bps=30,
        )


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            quote_cpmm_swap_exact_in(
                reserve_in=1_000_000,
                reserve_out=1_000_000,
                amount_in=10_000,
                fee_bps=30,
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
        quote = quote_cpmm_swap_exact_in(
            reserve_in=1_000_000,
            reserve_out=1_000_000,
            amount_in=10_000,
            fee_bps=30,
        )
        assert quote.amount_out == 9_871
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
