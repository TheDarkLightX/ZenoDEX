"""Disaster-state suite for burn-rail Rust authority promotion."""

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
from src.core.burn_receipts import (  # noqa: E402
    _verify_burn_rails_authority,
    make_burn_receipt,
    verify_burn_receipt,
)
from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    load_authority_policy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from src.runtime.rust_invoker import RustInvocationError, burn_rails_verify  # noqa: E402


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"burn_receipts": mode},
        promoted_surfaces=frozenset({"burn_receipts"}),
    )


def _rail_tx(**overrides) -> dict:
    tx = {
        "do_burn": 1,
        "receipt_bound": 1,
        "nullifier_unused": 1,
        "policy_ok": 1,
        "burn_amount": 10,
        "receipt_amount": 10,
        "burn_budget": 10,
        "supply_before": 100,
        "supply_after": 90,
        "batch_burn_sum_before": 0,
        "batch_burn_sum_after": 10,
    }
    tx.update(overrides)
    return tx


def _receipt(**overrides):
    tx = _rail_tx(**overrides)
    return make_burn_receipt(
        asset_id="zDEX",
        batch_id="batch-1",
        nullifier="n-1",
        tx_ref="tx-1",
        policy_version="v1",
        **tx,
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


def test_public_testnet_profile_promotes_burn_receipts():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.mode_for("burn_receipts") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
    assert "burn_receipts" in policy.promoted_surfaces

    broken = dict(profile)
    broken["runtime_authority_policy"] = dict(profile["runtime_authority_policy"])
    broken["runtime_authority_policy"]["promoted_surfaces"] = [
        "balances",
        "canonical",
        "cpmm_settlement",
        "fee_router",
        "perp_math",
        "replay_guard",
        "state_root",
        "zusd",
    ]
    conflicts = evaluate_deploy_profile_consistency(broken, {})
    assert any("burn_receipts" in conflict and "half-configured Rust authority" in conflict for conflict in conflicts)


def test_copied_burn_receipt_boundary_is_host_replay_flag(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    assert verify_burn_receipt(_receipt()) == (True, "ok")
    copied = _receipt(nullifier_unused=0)
    assert verify_burn_receipt(copied) == (False, "replay_guard_failed")


def test_stateless_stale_replay_is_deterministic(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    receipt = _receipt()
    assert verify_burn_receipt(receipt) == (True, "ok")
    assert verify_burn_receipt(receipt) == (True, "ok")


def test_structural_bridge_rejections_are_stateless_noops(rust_env):
    out = burn_rails_verify(tx={k: v for k, v in _rail_tx().items() if k != "burn_budget"})
    assert out["accept"] is False
    assert out["reject_reason"] == "bad_numeric_field"
    assert out["pre_state_root"] == out["post_state_root"]


@pytest.mark.parametrize(
    ("overrides", "reason"),
    [
        ({"do_burn": 2}, "replay_guard_failed"),
        ({"receipt_bound": 0}, "replay_guard_failed"),
        ({"burn_budget": 5}, "amount_guard_failed"),
        ({"burn_amount": -1, "receipt_amount": -1}, "amount_guard_failed"),
        ({"burn_amount": 0x8000, "receipt_amount": 0x8000}, "amount_guard_failed"),
        ({"supply_after": 95}, "supply_guard_failed"),
        ({"supply_before": 5, "supply_after": -5}, "supply_guard_failed"),
        ({"batch_burn_sum_after": 5}, "batch_sum_guard_failed"),
    ],
)
def test_boundary_inputs_reject_fail_closed(rust_env, overrides, reason):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    assert verify_burn_receipt(_receipt(**overrides)) == (False, reason)


def test_hash_mismatch_rejects_before_rails(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    receipt = _receipt()
    receipt["receipt_hash"] = "0x" + "00" * 32
    assert verify_burn_receipt(receipt) == (False, "hash_mismatch")


def test_deterministic_fuzz_sequences_match_python_rust_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    rng = random.Random(20260530)
    accepted = rejected = 0
    for _ in range(240):
        tx = _rail_tx()
        field = rng.choice(list(tx))
        tx[field] = rng.choice([0, 1, 2, -1, 10, 100, 0x8000, 1 << 40])
        result = _verify_burn_rails_authority(**tx)
        if result == (True, "ok"):
            accepted += 1
        else:
            rejected += 1

    assert accepted > 0
    assert rejected > 0


def test_selector_fails_closed_on_malformed_rust_output(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def malformed_output(**kwargs):
        return {"version": 1, "kernel": "burn_receipts", "accept": True}

    monkeypatch.setattr("src.core.burn_receipts.burn_rails_verify", malformed_output)
    with pytest.raises(AuthorityError):
        verify_burn_receipt(_receipt())


def test_rust_invoker_rejects_malformed_rust_result_shape(rust_env, monkeypatch):
    from src.runtime import rust_invoker

    def malformed_invoke(*args, **kwargs):
        return {"version": 1, "kernel": "burn_receipts", "results": []}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError):
        burn_rails_verify(tx=_rail_tx())
