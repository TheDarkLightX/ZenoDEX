"""Live-path wiring tests for balances Rust authority."""

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

import src.core.balance_kernel as balances  # noqa: E402
from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.core.balance_kernel import (  # noqa: E402
    BalanceAccepted,
    BalanceRejected,
    BalanceState,
    _credit_python,
    _result_to_authority_doc,
    _transfer_python,
    credit,
    transfer,
)
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)

A = "0x" + "11" * 48
B = "0x" + "22" * 48
C = "0x" + "33" * 48
X = "0x" + "aa" * 32
Y = "0x" + "bb" * 32


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"balances": mode},
        promoted_surfaces=frozenset({"balances"}),
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


def _assert_same(pre: BalanceState, left, right) -> None:
    assert _result_to_authority_doc(pre, left) == _result_to_authority_doc(pre, right)


def test_default_python_authority_is_byte_identical():
    state = BalanceState()
    expected = _credit_python(state=state, recipient=A, asset=X, amount=100)
    observed = credit(state=state, recipient=A, asset=X, amount=100)
    _assert_same(state, expected, observed)


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = BalanceState()

    ops = [
        ("credit", A, X, 1000),
        ("credit", B, Y, 500),
        ("transfer", A, B, X, 300),
        ("transfer", A, C, X, 700),
        ("transfer", A, B, X, 1),
        ("transfer", B, A, Y, 100),
    ]
    for op in ops:
        if op[0] == "credit":
            _, recipient, asset, amount = op
            expected = _credit_python(state=state, recipient=recipient, asset=asset, amount=amount)
            observed = credit(state=state, recipient=recipient, asset=asset, amount=amount)
        else:
            _, sender, recipient, asset, amount = op
            expected = _transfer_python(
                state=state, sender=sender, recipient=recipient, asset=asset, amount=amount
            )
            observed = transfer(
                state=state, sender=sender, recipient=recipient, asset=asset, amount=amount
            )
        _assert_same(state, expected, observed)
        if isinstance(observed, BalanceAccepted):
            state = observed.state


def test_rust_shadow_mode_keeps_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    state = BalanceState()
    observed = credit(state=state, recipient=A, asset=X, amount=100)
    assert isinstance(observed, BalanceAccepted)
    expected = _credit_python(state=state, recipient=A, asset=X, amount=100)
    assert observed.state.state_root() == expected.state.state_root()


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def fake_credit(*, state, recipient, asset, amount):
        return BalanceRejected("insufficient_balance")

    monkeypatch.setattr(balances, "_credit_python", fake_credit)
    with pytest.raises(AuthorityError):
        credit(state=BalanceState(), recipient=A, asset=X, amount=100)


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            credit(state=BalanceState(), recipient=A, asset=X, amount=1)
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
        result = credit(state=BalanceState(), recipient=A, asset=X, amount=1)
        assert isinstance(result, BalanceAccepted)
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
