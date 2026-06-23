"""Live-path wiring tests for burn-rail Rust authority."""

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

import src.core.burn_receipts as burn_receipts  # noqa: E402
from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.core.burn_receipts import (  # noqa: E402
    _verify_burn_rails_authority,
    _verify_burn_rails_python,
    make_burn_receipt,
    verify_burn_receipt,
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
        per_surface={"burn_receipts": mode},
        promoted_surfaces=frozenset({"burn_receipts"}),
    )


def _receipt(**overrides):
    args = dict(
        asset_id="zDEX",
        batch_id="batch-1",
        nullifier="n-1",
        tx_ref="tx-1",
        policy_version="v1",
        do_burn=1,
        receipt_bound=1,
        nullifier_unused=1,
        policy_ok=1,
        burn_amount=10,
        receipt_amount=10,
        burn_budget=10,
        supply_before=100,
        supply_after=90,
        batch_burn_sum_before=0,
        batch_burn_sum_after=10,
    )
    args.update(overrides)
    return make_burn_receipt(**args)


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
    args = dict(
        do_burn=1,
        receipt_bound=1,
        nullifier_unused=1,
        policy_ok=1,
        burn_amount=10,
        receipt_amount=10,
        burn_budget=10,
        supply_before=100,
        supply_after=90,
        batch_burn_sum_before=0,
        batch_burn_sum_after=10,
    )
    assert _verify_burn_rails_authority(**args) == _verify_burn_rails_python(**args)
    assert verify_burn_receipt(_receipt()) == (True, "ok")


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    assert verify_burn_receipt(_receipt()) == (True, "ok")
    assert verify_burn_receipt(_receipt(burn_budget=5)) == (False, "amount_guard_failed")
    assert verify_burn_receipt(_receipt(supply_after=95)) == (False, "supply_guard_failed")
    assert verify_burn_receipt(_receipt(batch_burn_sum_after=5)) == (
        False,
        "batch_sum_guard_failed",
    )


def test_rust_shadow_mode_keeps_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    assert verify_burn_receipt(_receipt()) == (True, "ok")


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def fake_python(**kwargs):
        return False, "amount_guard_failed"

    monkeypatch.setattr(burn_receipts, "_verify_burn_rails_python", fake_python)
    with pytest.raises(AuthorityError):
        verify_burn_receipt(_receipt())


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            verify_burn_receipt(_receipt())
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
        assert verify_burn_receipt(_receipt()) == (True, "ok")
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
