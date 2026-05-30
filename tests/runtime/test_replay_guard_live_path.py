"""Live-path wiring tests for replay/idempotency Rust authority."""

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

import src.core.replay_guard as replay_guard  # noqa: E402
from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.core.replay_guard import (  # noqa: E402
    AdmitAccepted,
    AdmitRejected,
    ReplayGuardState,
    _admit_python,
    _result_to_authority_doc,
    admit,
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


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"replay_guard": mode},
        promoted_surfaces=frozenset({"replay_guard"}),
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


def _assert_same_result(pre: ReplayGuardState, left, right) -> None:
    assert _result_to_authority_doc(pre, left) == _result_to_authority_doc(pre, right)


def test_default_python_authority_is_byte_identical():
    state = ReplayGuardState()
    expected = _admit_python(state=state, sender=A, nonce=1)
    observed = admit(state=state, sender=A, nonce=1)
    _assert_same_result(state, expected, observed)


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = ReplayGuardState()

    for sender, nonce in [(A, 1), (B, 1), (A, 2), (B, 2), (A, 2), (A, 4), (A, 3)]:
        expected = _admit_python(state=state, sender=sender, nonce=nonce)
        observed = admit(state=state, sender=sender, nonce=nonce)
        _assert_same_result(state, expected, observed)
        if isinstance(observed, AdmitAccepted):
            state = observed.state


def test_rust_shadow_mode_keeps_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    state = ReplayGuardState()
    observed = admit(state=state, sender=A, nonce=1)
    assert isinstance(observed, AdmitAccepted)
    assert observed.state.state_root() == _admit_python(state=state, sender=A, nonce=1).state.state_root()


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def fake_python(*, state, sender, nonce):
        return AdmitRejected("stale_nonce")

    monkeypatch.setattr(replay_guard, "_admit_python", fake_python)
    with pytest.raises(AuthorityError):
        admit(state=ReplayGuardState(), sender=A, nonce=1)


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            admit(state=ReplayGuardState(), sender=A, nonce=1)
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
        result = admit(state=ReplayGuardState(), sender=A, nonce=1)
        assert isinstance(result, AdmitAccepted)
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
