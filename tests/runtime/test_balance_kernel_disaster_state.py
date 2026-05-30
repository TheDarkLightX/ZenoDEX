"""Disaster-state suite for balance accounting promotion."""

from __future__ import annotations

import os
import random
import sys
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
_TOOLS_RUNTIME = _REPO / "tools" / "runtime"
for _p in (str(_REPO), str(_TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from src.core.balance_kernel import (  # noqa: E402
    MAX_BALANCE,
    BalanceAccepted,
    BalanceRejected,
    BalanceState,
    credit,
    transfer,
)
from src.core.replay_guard import AdmitAccepted, AdmitRejected, ReplayGuardState, admit  # noqa: E402
from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    load_authority_policy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from src.runtime.rust_invoker import RustInvocationError, balance_op  # noqa: E402

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


def test_public_testnet_profile_promotes_balances():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.mode_for("balances") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
    assert "balances" in policy.promoted_surfaces

    broken = dict(profile)
    broken["runtime_authority_policy"] = dict(profile["runtime_authority_policy"])
    broken["runtime_authority_policy"]["promoted_surfaces"] = [
        "burn_receipts",
        "canonical",
        "cpmm_settlement",
        "fee_router",
        "perp_math",
        "replay_guard",
        "state_root",
        "zusd",
    ]
    conflicts = evaluate_deploy_profile_consistency(broken, {})
    assert any("balances" in conflict and "half-configured Rust authority" in conflict for conflict in conflicts)


def test_copied_transaction_boundary_is_blocked_by_promoted_replay_guard(rust_env):
    # Balance transitions are replay-naive by design; the nonce guard owns
    # copied-transaction rejection. Exercise the composed boundary explicitly.
    set_active_authority_policy(
        AuthorityPolicy(
            default=AuthorityMode.PYTHON_AUTHORITY,
            per_surface={
                "balances": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
                "replay_guard": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            },
            promoted_surfaces=frozenset({"balances", "replay_guard"}),
        )
    )
    nonce_state = ReplayGuardState()
    balance_state = credit(state=BalanceState(), recipient=A, asset=X, amount=100).state

    first_nonce = admit(state=nonce_state, sender=A, nonce=1)
    assert isinstance(first_nonce, AdmitAccepted)
    first_transfer = transfer(state=balance_state, sender=A, recipient=B, asset=X, amount=40)
    assert isinstance(first_transfer, BalanceAccepted)

    copied_nonce = admit(state=first_nonce.state, sender=A, nonce=1)
    assert isinstance(copied_nonce, AdmitRejected)
    assert copied_nonce.reason == "duplicate_nonce"
    assert balance_state.state_root() != first_transfer.state.state_root()


def test_stale_snapshot_replay_is_deterministic(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = BalanceState()
    state = credit(state=state, recipient=A, asset=X, amount=100).state
    root_before = state.state_root()

    a = transfer(state=state, sender=A, recipient=B, asset=X, amount=25)
    b = transfer(state=state, sender=A, recipient=B, asset=X, amount=25)

    assert isinstance(a, BalanceAccepted)
    assert isinstance(b, BalanceAccepted)
    assert a.state.state_root() == b.state.state_root()
    assert state.state_root() == root_before


def test_duplicate_balance_keys_in_rust_state_fail_closed(rust_env):
    with pytest.raises(RustInvocationError):
        balance_op(
            state_entries=[
                {"pubkey": A, "asset": X, "amount": 1},
                {"pubkey": A[2:].upper(), "asset": "0X" + X[2:].upper(), "amount": 2},
            ],
            tx={"kind": "credit", "recipient": A, "asset": X, "amount": 1},
        )


@pytest.mark.parametrize(
    ("tx", "reason"),
    [
        ({"kind": "credit", "recipient": "0x11", "asset": X, "amount": 1}, "invalid_recipient"),
        ({"kind": "credit", "recipient": A, "asset": "0xaa", "amount": 1}, "invalid_asset"),
        ({"kind": "credit", "recipient": A, "asset": X, "amount": 0}, "invalid_amount"),
        ({"kind": "credit", "recipient": A, "asset": X, "amount": -1}, "invalid_amount"),
        ({"kind": "credit", "recipient": A, "asset": X, "amount": MAX_BALANCE + 1}, "invalid_amount"),
        ({"kind": "credit", "recipient": A, "asset": X, "amount": True}, "invalid_amount"),
        ({"kind": "transfer", "sender": "0x11", "recipient": B, "asset": X, "amount": 1}, "invalid_sender"),
    ],
)
def test_malformed_and_boundary_inputs_reject_without_mutation(rust_env, tx, reason):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = BalanceState()
    root_before = state.state_root()

    if tx["kind"] == "credit":
        result = credit(state=state, recipient=tx["recipient"], asset=tx["asset"], amount=tx["amount"])
    else:
        result = transfer(
            state=state,
            sender=tx["sender"],
            recipient=tx["recipient"],
            asset=tx["asset"],
            amount=tx["amount"],
        )

    assert isinstance(result, BalanceRejected)
    assert result.reason == reason
    assert state.state_root() == root_before


def test_no_op_on_reject_and_cross_asset_isolation(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = credit(state=BalanceState(), recipient=A, asset=X, amount=100).state
    state = credit(state=state, recipient=A, asset=Y, amount=77).state
    root_before = state.state_root()

    rejected = transfer(state=state, sender=A, recipient=A, asset=X, amount=1)
    assert isinstance(rejected, BalanceRejected)
    assert rejected.reason == "self_transfer"
    assert state.state_root() == root_before

    moved = transfer(state=state, sender=A, recipient=B, asset=X, amount=40)
    assert isinstance(moved, BalanceAccepted)
    assert moved.state.balance_of(A, Y) == 77
    assert moved.state.balance_of(B, Y) == 0


def test_deterministic_fuzz_sequences_match_python_rust_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    rng = random.Random(20260530)
    accounts = [A, B, C]
    assets = [X, Y]
    state = BalanceState()
    accepted = rejected = 0

    for _ in range(240):
        before = state.state_root()
        if rng.random() < 0.45:
            result = credit(
                state=state,
                recipient=rng.choice(accounts),
                asset=rng.choice(assets),
                amount=rng.choice([1, 5, 20, 0, MAX_BALANCE + 1]),
            )
        else:
            result = transfer(
                state=state,
                sender=rng.choice(accounts),
                recipient=rng.choice(accounts),
                asset=rng.choice(assets),
                amount=rng.choice([1, 5, 20, 0, MAX_BALANCE + 1]),
            )
        if isinstance(result, BalanceAccepted):
            accepted += 1
            state = result.state
        else:
            rejected += 1
            assert state.state_root() == before

    assert accepted > 0
    assert rejected > 0


def test_selector_fails_closed_on_malformed_rust_output(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def malformed_output(**kwargs):
        return {"version": 1, "kernel": "balances", "accept": True}

    monkeypatch.setattr("src.runtime.rust_invoker.balance_op", malformed_output)
    with pytest.raises(AuthorityError):
        credit(state=BalanceState(), recipient=A, asset=X, amount=1)
