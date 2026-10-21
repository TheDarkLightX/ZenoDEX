"""Disaster-state suite for zUSD single-vault Rust authority promotion."""

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
from src.core import zusd  # noqa: E402
from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    load_authority_policy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from src.runtime.rust_invoker import RustInvocationError, zusd_op  # noqa: E402


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"zusd": mode},
        promoted_surfaces=frozenset({"zusd"}),
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


def _cmd(tag: str, **args) -> zusd.ZUSDCommand:
    return zusd.ZUSDCommand(tag, args)


def test_public_testnet_profile_demotes_semantically_stale_zusd():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.mode_for("zusd") is AuthorityMode.PYTHON_AUTHORITY
    assert "zusd" not in policy.promoted_surfaces

    broken = dict(profile)
    broken["runtime_authority_policy"] = dict(profile["runtime_authority_policy"])
    broken["runtime_authority_policy"]["per_surface"] = dict(
        profile["runtime_authority_policy"]["per_surface"]
    )
    broken["runtime_authority_policy"]["per_surface"]["zusd"] = (
        "rust_authority_with_python_shadow"
    )
    broken["runtime_authority_policy"]["promoted_surfaces"] = [
        *profile["runtime_authority_policy"]["promoted_surfaces"],
        "zusd",
    ]
    conflicts = evaluate_deploy_profile_consistency(broken, {})
    assert any("zusd" in c and "partial-CBC surfaces" in c for c in conflicts)


def test_stale_snapshot_replay_is_deterministic(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    s = zusd.init_state()
    cmd = _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8)
    first = zusd.step(s, cmd)
    second = zusd.step(s, cmd)
    assert first == second


def test_rejected_transition_is_no_op_under_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    s = zusd.init_state()
    result = zusd.step(s, _cmd("mint_zusd", amount_e8=500 * zusd.E8))
    assert result.ok is False
    assert result.state is None
    assert s == zusd.init_state()


def test_oracle_auth_gates_reject_without_mutation(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    s = zusd.init_state()
    rejected = zusd.step(s, _cmd("bootstrap_oracle", auth_ok=False, price_e8=zusd.E8))
    assert rejected.ok is False
    assert rejected.state is None
    assert s == zusd.init_state()

    boot = zusd.step(s, _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8))
    assert boot.ok is True
    assert boot.state is not None
    report = zusd.step(boot.state, _cmd("oracle_report", auth_ok=False, price_e8=zusd.E8 // 2))
    commit = zusd.step(boot.state, _cmd("oracle_commit", auth_ok=False))
    assert report.ok is False and report.state is None
    assert commit.ok is False and commit.state is None


@pytest.mark.parametrize(
    "state_mutation",
    [
        {"extra": "x"},
        {"oracle_seen": "true"},
        {"now_epoch": -1},
    ],
)
def test_malformed_state_rejects_fail_closed(rust_env, state_mutation):
    state = zusd._state_json(zusd.init_state())
    state.update(state_mutation)
    with pytest.raises(RustInvocationError):
        zusd_op(state=state, tx={"kind": "advance_epoch", "delta": 1})


def test_huge_command_rejection_agrees_under_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    s = zusd.init_state()
    result = zusd.step(s, _cmd("advance_epoch", delta=10**40))
    assert result.ok is False
    assert result.error == "now_epoch exceeds MAX_AMOUNT_E8"


def test_malformed_rust_output_fails_closed(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def malformed_op(*args, **kwargs):
        return {"version": 1, "kernel": "zusd", "accept": True}

    monkeypatch.setattr("src.runtime.rust_invoker.zusd_op", malformed_op)
    with pytest.raises(AuthorityError):
        zusd.step(zusd.init_state(), _cmd("bootstrap_oracle", auth_ok=True, price_e8=zusd.E8))


def test_rust_invoker_rejects_reject_with_receipt(rust_env, monkeypatch):
    from src.runtime import rust_invoker

    def malformed_invoke(*args, **kwargs):
        state = {k: str(v) if k != "oracle_seen" else v for k, v in zusd._state_json(zusd.init_state()).items()}
        return {
            "version": 1,
            "kernel": "zusd",
            "accept": False,
            "reject_reason": "bad",
            "receipt_hash": "0x" + "00" * 32,
            "receipt": {"tag": "advance_epoch"},
            "pre_state_root": "0x" + "00" * 32,
            "post_state_root": "0x" + "00" * 32,
            "post_state": state,
        }

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError):
        zusd_op(state=zusd._state_json(zusd.init_state()), tx={"kind": "advance_epoch", "delta": 0})


def test_deterministic_fuzz_accepts_and_rejects_under_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    rng = random.Random(20260530)
    s = zusd.init_state()
    accepted = rejected = 0
    for _ in range(200):
        tag = rng.choice(
            [
                "advance_epoch",
                "bootstrap_oracle",
                "oracle_report",
                "oracle_commit",
                "deposit_collateral",
                "withdraw_collateral",
                "mint_zusd",
                "repay_zusd",
                "deposit_sp",
                "withdraw_sp",
                "redeem_zusd",
                "liquidate",
            ]
        )
        if tag == "advance_epoch":
            cmd = _cmd(tag, delta=rng.choice([1, 0, 10**40]))
        elif tag in {"bootstrap_oracle", "oracle_report"}:
            cmd = _cmd(tag, auth_ok=rng.choice([True, False]), price_e8=rng.choice([zusd.E8, zusd.E8 // 2, 0]))
        elif tag == "oracle_commit":
            cmd = _cmd(tag, auth_ok=rng.choice([True, False]))
        elif tag == "liquidate":
            cmd = _cmd(tag)
        else:
            cmd = _cmd(tag, amount_e8=rng.choice([1, 50 * zusd.E8, 500 * zusd.E8, 0, 10**40]))
        result = zusd.step(s, cmd)
        if result.ok:
            accepted += 1
            assert result.state is not None
            s = result.state
        else:
            rejected += 1

    assert accepted > 0
    assert rejected > 0
