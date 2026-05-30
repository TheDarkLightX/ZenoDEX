"""Disaster-state suite for replay/idempotency guard promotion.

This fills the replay_guard row in the Rust authority promotion catalog:
copied transaction replay, stale snapshot, duplicate stored sender IDs,
malformed sender bytes, nonce over/underflow, cross-sender mutation isolation,
and no-op-on-reject.
"""

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
from src.core.replay_guard import (  # noqa: E402
    U32_MAX,
    AdmitAccepted,
    AdmitRejected,
    ReplayGuardState,
    admit,
)
from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile  # noqa: E402
from src.runtime.authority import AuthorityError, AuthorityMode, AuthorityPolicy, load_authority_policy, set_active_authority_policy, reset_active_authority_policy  # noqa: E402
from src.runtime.rust_invoker import RustInvocationError, replay_guard_admit  # noqa: E402

A = "0x" + "11" * 48
B = "0x" + "22" * 48
C = "0x" + "33" * 48


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


def test_public_testnet_profile_promotes_replay_guard():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.mode_for("replay_guard") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
    assert "replay_guard" in policy.promoted_surfaces

    broken = dict(profile)
    broken["runtime_authority_policy"] = dict(profile["runtime_authority_policy"])
    broken["runtime_authority_policy"]["promoted_surfaces"] = [
        "balances",
        "canonical",
        "fee_router",
        "state_root",
    ]
    conflicts = evaluate_deploy_profile_consistency(broken, {})
    assert any("replay_guard" in conflict and "half-configured Rust authority" in conflict for conflict in conflicts)


def test_copied_transaction_replay_rejected_and_noop_under_rust_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = ReplayGuardState()
    accepted = admit(state=state, sender=A, nonce=1)
    assert isinstance(accepted, AdmitAccepted)

    root_before = accepted.state.state_root()
    duplicate = admit(state=accepted.state, sender=A, nonce=1)

    assert isinstance(duplicate, AdmitRejected)
    assert duplicate.reason == "duplicate_nonce"
    assert accepted.state.state_root() == root_before


def test_stale_snapshot_replay_is_deterministic_and_rejected(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = ReplayGuardState()
    for nonce in (1, 2, 3):
        result = admit(state=state, sender=A, nonce=nonce)
        assert isinstance(result, AdmitAccepted)
        state = result.state

    root_before = state.state_root()
    stale_a = admit(state=state, sender=A, nonce=2)
    stale_b = admit(state=state, sender=A, nonce=2)

    assert isinstance(stale_a, AdmitRejected)
    assert isinstance(stale_b, AdmitRejected)
    assert stale_a.reason == stale_b.reason == "stale_nonce"
    assert state.state_root() == root_before


def test_duplicate_sender_ids_in_rust_state_fail_closed(rust_env):
    raw_a = A[2:].upper()
    with pytest.raises(RustInvocationError):
        replay_guard_admit(
            state_entries=[
                {"sender": A, "last_nonce": 1},
                {"sender": raw_a, "last_nonce": 2},
            ],
            sender=A,
            nonce=3,
        )


@pytest.mark.parametrize(
    ("sender", "nonce", "reason"),
    [
        ("0xzz" + "11" * 47, 1, "invalid_sender"),
        ("0x" + "11" * 47, 1, "invalid_sender"),
        (A, 0, "invalid_nonce"),
        (A, -1, "invalid_nonce"),
        (A, U32_MAX + 1, "invalid_nonce"),
        (A, True, "invalid_nonce"),
    ],
)
def test_malformed_and_boundary_inputs_reject_without_mutation(rust_env, sender, nonce, reason):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = ReplayGuardState()
    root_before = state.state_root()

    result = admit(state=state, sender=sender, nonce=nonce)

    assert isinstance(result, AdmitRejected)
    assert result.reason == reason
    assert state.state_root() == root_before


def test_unauthorized_cross_sender_mutation_blocked(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    state = admit(state=ReplayGuardState(), sender=A, nonce=1).state
    root_before = state.state_root()

    gap_for_b = admit(state=state, sender=B, nonce=2)
    assert isinstance(gap_for_b, AdmitRejected)
    assert gap_for_b.reason == "nonce_gap"
    assert state.state_root() == root_before

    first_for_b = admit(state=state, sender=B, nonce=1)
    assert isinstance(first_for_b, AdmitAccepted)
    assert first_for_b.state.last_for(A) == 1
    assert first_for_b.state.last_for(B) == 1


def test_deterministic_fuzz_sequences_match_python_rust_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    rng = random.Random(20260530)
    senders = [A, B, C]
    state = ReplayGuardState()
    accepted = rejected = 0

    for _ in range(220):
        sender = rng.choice(senders)
        nonce = rng.choice([1, 2, 3, 4, 5, 6, 0, U32_MAX + 1])
        before = state.state_root()
        result = admit(state=state, sender=sender, nonce=nonce)
        if isinstance(result, AdmitAccepted):
            accepted += 1
            assert result.state.last_for(sender) == nonce
            state = result.state
        else:
            rejected += 1
            assert state.state_root() == before

    assert accepted > 0
    assert rejected > 0


def test_selector_fails_closed_on_malformed_rust_output(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def malformed_output(**kwargs):
        return {"version": 1, "kernel": "replay_guard", "accept": True}

    monkeypatch.setattr("src.runtime.rust_invoker.replay_guard_admit", malformed_output)
    with pytest.raises(AuthorityError):
        admit(state=ReplayGuardState(), sender=A, nonce=1)
