"""Disaster-state suite for stateless perps-math Rust authority promotion."""

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
from src.core.perp_v2 import math as m  # noqa: E402
from src.integration.deploy_profile import evaluate_deploy_profile_consistency, load_deploy_profile  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityError,
    AuthorityMode,
    AuthorityPolicy,
    load_authority_policy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from src.runtime.rust_invoker import RustInvocationError, perp_math_eval  # noqa: E402


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"perp_math": mode},
        promoted_surfaces=frozenset({"perp_math"}),
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


def test_public_testnet_profile_demotes_partial_cbc_perp_math():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.mode_for("perp_math") is AuthorityMode.PYTHON_AUTHORITY
    assert "perp_math" not in policy.promoted_surfaces

    broken = dict(profile)
    broken["runtime_authority_policy"] = dict(profile["runtime_authority_policy"])
    broken["runtime_authority_policy"]["per_surface"] = dict(
        profile["runtime_authority_policy"]["per_surface"]
    )
    broken["runtime_authority_policy"]["per_surface"]["perp_math"] = (
        "rust_authority_with_python_shadow"
    )
    broken["runtime_authority_policy"]["promoted_surfaces"] = [
        *profile["runtime_authority_policy"]["promoted_surfaces"],
        "perp_math",
    ]
    conflicts = evaluate_deploy_profile_consistency(broken, {})
    assert any("perp_math" in c and "partial-CBC surfaces" in c for c in conflicts)


def test_stateless_stale_replay_is_deterministic(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    args = (1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE)
    assert m.pnl_quote(*args) == m.pnl_quote(*args)


@pytest.mark.parametrize(
    ("case", "code"),
    [
        ({"op": "notional_quote", "position_base": 10**30, "price_e8": 100 * m.PRICE_SCALE}, "out_of_domain"),
        (
            {
                "op": "maint_margin_req",
                "position_base": 1000,
                "price_e8": 100 * m.PRICE_SCALE,
                "maint_bps": 10**9,
                "depeg_bps": 0,
            },
            "out_of_domain",
        ),
        ({"op": "notional_quote", "position_base": -(2**127), "price_e8": 100 * m.PRICE_SCALE}, "out_of_domain"),
        ({"op": "pnl_quote", "position_base": 1, "settle_price_e8": 2}, "malformed_case"),
        ({"op": "unknown_op"}, "unknown_op"),
    ],
)
def test_boundary_inputs_reject_fail_closed(rust_env, case, code):
    out = perp_math_eval(case)
    assert out["ok"] is False
    assert out["code"] == code


def test_out_of_domain_disagreement_fails_closed_under_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    with pytest.raises(AuthorityError):
        m.notional_quote(10**30, 100 * m.PRICE_SCALE)


def test_malformed_rust_output_fails_closed(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def malformed_eval(*args, **kwargs):
        return {"index": 0, "ok": True}

    monkeypatch.setattr("src.runtime.rust_invoker.perp_math_eval", malformed_eval)
    with pytest.raises(AuthorityError):
        m.pnl_quote(1_000, 110 * m.PRICE_SCALE, 100 * m.PRICE_SCALE)


def test_rust_invoker_rejects_malformed_result_shape(rust_env, monkeypatch):
    from src.runtime import rust_invoker

    def malformed_invoke(*args, **kwargs):
        return {"version": 1, "results": [{"index": 0, "ok": True, "value": "1", "flag": True}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError):
        perp_math_eval({"op": "pnl_quote", "position_base": 1, "settle_price_e8": 2, "index_price_e8": 1})


def test_rust_invoker_rejects_extra_result_fields(rust_env, monkeypatch):
    from src.runtime import rust_invoker

    def malformed_invoke(*args, **kwargs):
        return {"version": 1, "results": [{"index": 0, "ok": True, "value": "1", "extra": "x"}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError):
        perp_math_eval({"op": "pnl_quote", "position_base": 1, "settle_price_e8": 2, "index_price_e8": 1})


def test_rust_invoker_rejects_reject_with_success_payload(rust_env, monkeypatch):
    from src.runtime import rust_invoker

    def malformed_invoke(*args, **kwargs):
        return {"version": 1, "results": [{"index": 0, "ok": False, "code": "bad", "value": "1"}]}

    monkeypatch.setattr(rust_invoker, "invoke", malformed_invoke)
    with pytest.raises(RustInvocationError):
        perp_math_eval({"op": "pnl_quote", "position_base": 1, "settle_price_e8": 2, "index_price_e8": 1})


def test_deterministic_fuzz_accepts_and_rejects_under_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    rng = random.Random(20260530)
    accepted = rejected = 0
    for _ in range(200):
        op = rng.choice(["pnl_quote", "funding_payment", "is_liquidatable", "notional_quote"])
        try:
            if op == "pnl_quote":
                m.pnl_quote(
                    rng.choice([0, 1_000, -1_000, 10**30]),
                    rng.randint(1, 120) * m.PRICE_SCALE,
                    rng.randint(1, 120) * m.PRICE_SCALE,
                )
            elif op == "funding_payment":
                m.funding_payment(
                    rng.choice([0, 1_000, -1_000, 10**30]),
                    rng.randint(1, 120) * m.PRICE_SCALE,
                    rng.randint(-5_000, 5_000),
                )
            elif op == "is_liquidatable":
                m.is_liquidatable(
                    rng.choice([0, 1_000_000, -1_000_000]),
                    rng.randint(-10**12, 10**12),
                    rng.randint(1, 120) * m.PRICE_SCALE,
                    rng.randint(0, 5_000),
                    rng.randint(0, 5_000),
                )
            else:
                m.notional_quote(rng.choice([1_000, -1_000, 10**30]), rng.randint(1, 120) * m.PRICE_SCALE)
            accepted += 1
        except (AuthorityError, TypeError, ValueError):
            rejected += 1

    assert accepted > 0
    assert rejected > 0
