"""Disaster-state suite for CPMM settlement Rust authority promotion."""

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
from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile  # noqa: E402
from src.kernels.python.settlement_swap_runtime_v1 import (  # noqa: E402
    DEX_POOL_RESERVE_MAX,
    quote_cpmm_swap_exact_in,
    quote_cpmm_swap_exact_out,
)
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    load_authority_policy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from src.runtime.rust_invoker import RustInvocationError, cpmm_op  # noqa: E402


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"cpmm_settlement": mode},
        promoted_surfaces=frozenset({"cpmm_settlement"}),
    )


def _pool(**overrides) -> dict:
    pool = {
        "initialized": True,
        "reserve0": 1_000_000,
        "reserve1": 1_000_000,
        "fee_bps": 30,
    }
    pool.update(overrides)
    return pool


def _pool_out(pool: dict) -> dict:
    return {
        "initialized": bool(pool["initialized"]),
        "reserve0": str(pool["reserve0"]),
        "reserve1": str(pool["reserve1"]),
        "fee_bps": str(pool["fee_bps"]),
    }


def _empty_pool() -> dict:
    return {"initialized": False, "reserve0": 0, "reserve1": 0, "fee_bps": 0}


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


def test_public_testnet_profile_demotes_partial_cbc_cpmm_settlement():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.mode_for("cpmm_settlement") is AuthorityMode.PYTHON_AUTHORITY
    assert "cpmm_settlement" not in policy.promoted_surfaces

    broken = dict(profile)
    broken["runtime_authority_policy"] = dict(profile["runtime_authority_policy"])
    broken["runtime_authority_policy"]["per_surface"] = dict(
        profile["runtime_authority_policy"]["per_surface"]
    )
    broken["runtime_authority_policy"]["per_surface"]["cpmm_settlement"] = (
        "rust_authority_with_python_shadow"
    )
    broken["runtime_authority_policy"]["promoted_surfaces"] = [
        *profile["runtime_authority_policy"]["promoted_surfaces"],
        "cpmm_settlement",
    ]
    conflicts = evaluate_deploy_profile_consistency(broken, {})
    assert any(
        "cpmm_settlement" in c and "partial-CBC surfaces" in c for c in conflicts
    )


def test_stateless_stale_quote_replay_is_deterministic(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    a = quote_cpmm_swap_exact_in(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
    )
    b = quote_cpmm_swap_exact_in(
        reserve_in=1_000_000,
        reserve_out=1_000_000,
        amount_in=10_000,
        fee_bps=30,
    )
    assert a == b


@pytest.mark.parametrize(
    ("tx", "reason"),
    [
        ({"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 0, "min_amount_out": 0}, "invalid_amount"),
        (
            {"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 10_000, "min_amount_out": 1_000_000_000},
            "slippage",
        ),
        (
            {"kind": "swap_exact_out", "zero_for_one": True, "amount_out": 1_000_000, "max_amount_in": 10**18},
            "amount_out_ge_reserve",
        ),
        (
            {"kind": "swap_exact_out", "zero_for_one": True, "amount_out": 5_000, "max_amount_in": 1},
            "slippage",
        ),
        (
            {
                "kind": "swap_exact_out",
                "zero_for_one": True,
                "amount_out": 1,
                "max_amount_in": 10**18,
                "max_overdelivery_gap_bps": 200,
            },
            "overdelivery_gap",
        ),
    ],
)
def test_boundary_inputs_reject_without_mutation(rust_env, tx, reason):
    pool = _pool()
    if reason == "overdelivery_gap":
        pool = _pool(reserve0=1, reserve1=4)
    out = cpmm_op(pool=pool, tx=tx)
    assert out["accept"] is False
    assert out["reject_reason"] == reason
    assert out["pre_state_root"] == out["post_state_root"]
    assert out["post_pool"] == _pool_out(pool)


def test_structural_bridge_rejections_are_no_op(rust_env):
    out = cpmm_op(
        pool=_pool(),
        tx={"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 1},
    )
    assert out["accept"] is False
    assert out["reject_reason"] == "malformed_tx"
    assert out["pre_state_root"] == out["post_state_root"]


def test_cpmm_op_accepts_canonical_init_and_rejects_hidden_junk_state(rust_env):
    out = cpmm_op(
        pool=_empty_pool(),
        tx={"kind": "init_pool", "reserve0": 1_000_000, "reserve1": 1_000_000, "fee_bps": 30},
    )
    assert out["accept"] is True
    assert out["post_pool"] == _pool_out(_pool())

    with pytest.raises(RustInvocationError):
        cpmm_op(
            pool={"initialized": False, "reserve0": 1, "reserve1": 0, "fee_bps": 0},
            tx={"kind": "init_pool", "reserve0": 1_000_000, "reserve1": 1_000_000, "fee_bps": 30},
        )


def test_rust_invoker_rejects_malformed_output_shape(rust_env, monkeypatch):
    from src.runtime import rust_invoker

    def malformed_invoke(*args, **kwargs):
        return {"version": 1, "kernel": "cpmm_settlement", "accept": True}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError):
        cpmm_op(
            pool=_pool(),
            tx={"kind": "swap_exact_in", "zero_for_one": True, "amount_in": 1, "min_amount_out": 0},
        )


def test_selector_fails_closed_on_malformed_rust_output(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def malformed_cpmm_op(**kwargs):
        return {
            "version": 1,
            "kernel": "cpmm_settlement",
            "accept": True,
            "reject_reason": None,
            "receipt_hash": "0x0",
            "receipt": {"kind": "swap_exact_in"},
            "pre_state_root": "0x0",
            "post_state_root": "0x1",
            "post_pool": _pool(),
        }

    monkeypatch.setattr("src.runtime.rust_invoker.cpmm_op", malformed_cpmm_op)
    with pytest.raises(AuthorityError):
        quote_cpmm_swap_exact_in(
            reserve_in=1_000_000,
            reserve_out=1_000_000,
            amount_in=10_000,
            fee_bps=30,
        )


def test_deterministic_fuzz_accepts_and_rejects_under_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    rng = random.Random(20260530)
    accepted = rejected = 0
    for _ in range(200):
        reserve_in = rng.randint(1, 2_000_000)
        reserve_out = rng.randint(1, 2_000_000)
        fee_bps = rng.choice([0, 1, 30, 100, 1_000, 10_000])
        if rng.random() < 0.5:
            try:
                quote_cpmm_swap_exact_in(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_in=rng.choice([0, 1, 10, 10_000, DEX_POOL_RESERVE_MAX]),
                    fee_bps=fee_bps,
                )
                accepted += 1
            except (AuthorityError, TypeError, ValueError):
                rejected += 1
        else:
            try:
                quote_cpmm_swap_exact_out(
                    reserve_in=reserve_in,
                    reserve_out=reserve_out,
                    amount_out=rng.choice([0, 1, max(1, reserve_out - 1), reserve_out, DEX_POOL_RESERVE_MAX]),
                    fee_bps=fee_bps,
                    max_overdelivery_gap_bps=200,
                )
                accepted += 1
            except (AuthorityError, TypeError, ValueError):
                rejected += 1

    assert accepted > 0
    assert rejected > 0
