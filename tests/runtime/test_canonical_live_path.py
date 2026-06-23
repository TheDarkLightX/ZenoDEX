"""Live-path wiring tests for the first canonical Rust-authority call site."""

from __future__ import annotations

import os
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
if str(_REPO) not in sys.path:
    sys.path.insert(0, str(_REPO))

import src.core.burn_receipts as burn_receipts  # noqa: E402
from src.core.burn_receipts import _burn_receipt_hash_python, burn_receipt_hash  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from tools.runtime import canonical_primitives_lib as canon  # noqa: E402

_BODY = {"do_burn": 1, "amount": 12_345, "epoch": 7, "batch": [3, 1, 2], "z": "y"}


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"canonical": mode},
        promoted_surfaces=frozenset({"canonical"}),
    )


@pytest.fixture(autouse=True)
def _reset_policy_after():
    yield
    reset_active_authority_policy()


@pytest.fixture(scope="module")
def rust_env():
    try:
        bin_path = canon.locate_or_build_cli()
    except canon.CanonicalShadowError as exc:  # pragma: no cover - env dependent
        pytest.skip(f"rust shadow unavailable: {exc}")
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(bin_path)
    yield bin_path
    if old is None:
        os.environ.pop("ZENODEX_RUNTIME_BIN", None)
    else:
        os.environ["ZENODEX_RUNTIME_BIN"] = old


def test_default_python_authority_is_byte_identical():
    assert burn_receipt_hash(_BODY) == _burn_receipt_hash_python(_BODY)


def test_rust_authority_with_python_shadow_agrees_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    assert burn_receipt_hash(_BODY) == _burn_receipt_hash_python(_BODY)


def test_rust_shadow_mode_python_authoritative_live(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    assert burn_receipt_hash(_BODY) == _burn_receipt_hash_python(_BODY)


def test_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    monkeypatch.setattr(burn_receipts, "canonical_domain_json_hash", lambda *args, **kwargs: "0xdeadbeef")
    with pytest.raises(AuthorityError):
        burn_receipt_hash(_BODY)


def test_fails_closed_when_rust_unavailable_under_authority():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        with pytest.raises(AuthorityError):
            burn_receipt_hash(_BODY)
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
        assert burn_receipt_hash(_BODY) == _burn_receipt_hash_python(_BODY)
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
