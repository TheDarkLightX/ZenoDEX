"""Live-path wiring tests for the state-root v5 Rust authority surface."""

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

import src.state.state_root as state_root_mod  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from src.state.state_root import compute_state_root  # noqa: E402
from tools.runtime import state_root_lib as lib  # noqa: E402


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"state_root": mode},
        promoted_surfaces=frozenset({"state_root"}),
    )


@pytest.fixture(autouse=True)
def _reset_policy_after():
    yield
    reset_active_authority_policy()


@pytest.fixture(scope="module")
def rust_env():
    try:
        bin_path = lib.locate_or_build_cli()
    except lib.StateRootShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(bin_path)
    yield bin_path
    if old is None:
        os.environ.pop("ZENODEX_RUNTIME_BIN", None)
    else:
        os.environ["ZENODEX_RUNTIME_BIN"] = old


def _domain_state():
    return lib.build_tables(lib.static_states()[-1])


def _compute_with_active_policy() -> str:
    balances, pools, lp, nonces, fee_accumulator = _domain_state()
    return compute_state_root(
        balances=balances,
        pools=pools,
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=fee_accumulator,
    )


def _compute_python_only() -> str:
    balances, pools, lp, nonces, fee_accumulator = _domain_state()
    return state_root_mod._compute_state_root_python(  # pylint: disable=protected-access
        balances=balances,
        pools=pools,
        lp_balances=lp,
        nonces=nonces,
        fee_accumulator=fee_accumulator,
    )


def test_default_python_authority_is_byte_identical():
    assert _compute_with_active_policy() == _compute_python_only()


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    assert _compute_with_active_policy() == _compute_python_only()


def test_rust_shadow_mode_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    assert _compute_with_active_policy() == _compute_python_only()


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    monkeypatch.setattr(state_root_mod, "_compute_state_root_python", lambda **kwargs: "0x" + "11" * 32)
    with pytest.raises(AuthorityError):
        _compute_with_active_policy()


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            _compute_with_active_policy()
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
        assert _compute_with_active_policy() == _compute_python_only()
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
