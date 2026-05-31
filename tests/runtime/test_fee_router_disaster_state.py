"""Disaster-state suite for fee-router Rust authority promotion."""

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
from src.core.fee_router import (  # noqa: E402
    MAX_FEE_AMOUNT,
    FeeAccumulator,
    FeeAssetAmount,
    RouteAccepted,
    RouteRejected,
    canonical_split_table,
    route_fee,
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
from src.runtime.rust_invoker import RustInvocationError, fee_route  # noqa: E402


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"fee_router": mode},
        promoted_surfaces=frozenset({"fee_router"}),
    )


def _split(source: str) -> dict[str, int]:
    table = canonical_split_table(source)
    return {
        "buyburn_bps": table.buyburn_bps,
        "stakers_bps": table.stakers_bps,
        "reserve_bps": table.reserve_bps,
        "hosts_bps": table.hosts_bps,
    }


def _empty_acc_doc() -> dict[str, list[dict]]:
    return {
        "dust_by_stream": [],
        "cum_buyburn": [],
        "cum_stakers": [],
        "cum_reserve": [],
        "cum_hosts": [],
    }


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


def test_public_testnet_profile_promotes_fee_router():
    profile = load_deploy_profile("public-testnet")
    policy = load_authority_policy(profile)

    assert policy.mode_for("fee_router") is AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW
    assert "fee_router" in policy.promoted_surfaces

    broken = dict(profile)
    broken["runtime_authority_policy"] = dict(profile["runtime_authority_policy"])
    broken["runtime_authority_policy"]["promoted_surfaces"] = [
        "balances",
        "burn_receipts",
        "canonical",
        "cpmm_settlement",
        "perp_math",
        "perp_stateful",
        "replay_guard",
        "state_root",
        "zusd",
    ]
    conflicts = evaluate_deploy_profile_consistency(broken, {})
    assert any("fee_router" in conflict and "half-configured Rust authority" in conflict for conflict in conflicts)


def test_copied_transaction_boundary_is_blocked_by_promoted_replay_guard(rust_env):
    # Fee routing is replay-naive by design; the nonce guard owns copied
    # transaction rejection. Exercise the composed boundary explicitly.
    set_active_authority_policy(
        AuthorityPolicy(
            default=AuthorityMode.PYTHON_AUTHORITY,
            per_surface={
                "fee_router": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
                "replay_guard": AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW,
            },
            promoted_surfaces=frozenset({"fee_router", "replay_guard"}),
        )
    )
    sender = "0x" + "11" * 48
    nonce_state = ReplayGuardState()
    acc = FeeAccumulator()

    first_nonce = admit(state=nonce_state, sender=sender, nonce=1)
    assert isinstance(first_nonce, AdmitAccepted)
    first_fee = route_fee(
        source="dex",
        asset="zUSD",
        amount=100,
        split_table=canonical_split_table("dex"),
        accumulator=acc,
    )
    assert isinstance(first_fee, RouteAccepted)

    copied_nonce = admit(state=first_nonce.state, sender=sender, nonce=1)
    assert isinstance(copied_nonce, AdmitRejected)
    assert copied_nonce.reason == "duplicate_nonce"
    assert acc.state_root() != first_fee.accumulator.state_root()


def test_stale_snapshot_replay_is_deterministic(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    acc = FeeAccumulator()
    root_before = acc.state_root()

    a = route_fee(
        source="dex", asset="zUSD", amount=12_347, split_table=canonical_split_table("dex"), accumulator=acc
    )
    b = route_fee(
        source="dex", asset="zUSD", amount=12_347, split_table=canonical_split_table("dex"), accumulator=acc
    )

    assert isinstance(a, RouteAccepted)
    assert isinstance(b, RouteAccepted)
    assert a.accumulator.state_root() == b.accumulator.state_root()
    assert acc.state_root() == root_before


def test_duplicate_fee_accumulator_keys_in_rust_state_fail_closed(rust_env):
    with pytest.raises(RustInvocationError):
        fee_route(
            accumulator={
                **_empty_acc_doc(),
                "cum_buyburn": [
                    {"asset": "zUSD", "amount": 1},
                    {"asset": "zUSD", "amount": 2},
                ],
            },
            tx={"kind": "route_fee", "source": "dex", "asset": "zUSD", "amount": 1, "split_table": _split("dex")},
        )
    with pytest.raises(RustInvocationError):
        fee_route(
            accumulator={
                **_empty_acc_doc(),
                "dust_by_stream": [
                    {"source": "dex", "asset": "zUSD", "amount": 1},
                    {"source": "dex", "asset": "zUSD", "amount": 2},
                ],
            },
            tx={"kind": "route_fee", "source": "dex", "asset": "zUSD", "amount": 1, "split_table": _split("dex")},
        )


@pytest.mark.parametrize(
    ("source", "asset", "amount", "table", "reason"),
    [
        ("dex", "zUSD", -1, canonical_split_table("dex"), "negative_amount"),
        ("dex", "zUSD", MAX_FEE_AMOUNT + 1, canonical_split_table("dex"), "amount_too_large"),
        (
            "dex",
            "zUSD",
            1_000,
            type(canonical_split_table("dex"))(10_001, 0, 0, 0),
            "split_component_out_of_range",
        ),
        (
            "dex",
            "zUSD",
            1_000,
            type(canonical_split_table("dex"))(6_000, 0, 2_000, 1_999),
            "split_does_not_sum_to_10000",
        ),
        ("lending", "zUSD", 1_000, type(canonical_split_table("dex"))(2_500, 2_500, 2_500, 2_500), "unknown_domain"),
        (
            "redemption",
            "AGRS",
            1_000,
            type(canonical_split_table("dex"))(1, 5_999, 4_000, 0),
            "domain_constraint_violated",
        ),
    ],
)
def test_boundary_inputs_reject_without_mutation(rust_env, source, asset, amount, table, reason):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    acc = FeeAccumulator()
    root_before = acc.state_root()
    result = route_fee(source=source, asset=asset, amount=amount, split_table=table, accumulator=acc)
    assert isinstance(result, RouteRejected)
    assert result.reason == reason
    assert acc.state_root() == root_before


def test_no_op_on_reject_and_cross_stream_isolation(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    acc = FeeAccumulator()
    first = route_fee(
        source="dex", asset="zUSD", amount=1, split_table=canonical_split_table("dex"), accumulator=acc
    )
    assert isinstance(first, RouteAccepted)
    assert first.accumulator.dust_for("dex", "zUSD") == 1
    root_before = first.accumulator.state_root()

    rejected = route_fee(
        source="dex",
        asset="zUSD",
        amount=1_000,
        split_table=type(canonical_split_table("dex"))(4_999, 1, 3_000, 2_000),
        accumulator=first.accumulator,
    )
    assert isinstance(rejected, RouteRejected)
    assert first.accumulator.state_root() == root_before

    second = route_fee(
        source="dex", asset="AGRS", amount=9_999, split_table=canonical_split_table("dex"), accumulator=first.accumulator
    )
    assert isinstance(second, RouteAccepted)
    assert second.accumulator.dust_for("dex", "zUSD") == 1
    assert second.accumulator.bucket_total("cum_buyburn", "zUSD") == 0
    assert second.accumulator.bucket_total("cum_buyburn", "AGRS") > 0


def test_accumulator_overflow_rejects_and_preserves_state(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    acc = FeeAccumulator(cum_buyburn=(FeeAssetAmount("zUSD", MAX_FEE_AMOUNT),))
    root_before = acc.state_root()
    result = route_fee(
        source="dex",
        asset="zUSD",
        amount=10_000,
        split_table=canonical_split_table("dex"),
        accumulator=acc,
    )
    assert isinstance(result, RouteRejected)
    assert result.reason == "arithmetic_overflow"
    assert acc.state_root() == root_before


def test_structural_rust_bridge_rejections_are_no_op(rust_env):
    out = fee_route(
        accumulator=_empty_acc_doc(),
        tx={"kind": "route_fee", "source": "dex", "amount": 1, "split_table": _split("dex")},
    )
    assert out["accept"] is False
    assert out["reject_reason"] == "malformed_tx"
    assert out["pre_state_root"] == out["post_state_root"]


def test_deterministic_fuzz_sequences_match_python_rust_authority(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    rng = random.Random(20260530)
    acc = FeeAccumulator()
    accepted = rejected = 0
    tables = {
        "dex": canonical_split_table("dex"),
        "perps": canonical_split_table("perps"),
        "borrow": canonical_split_table("borrow"),
        "redemption": canonical_split_table("redemption"),
    }

    for _ in range(240):
        before = acc.state_root()
        source = rng.choice(["dex", "perps", "borrow", "redemption", "lending"])
        asset = rng.choice(["zUSD", "AGRS", "zDEX"])
        amount = rng.choice([0, 1, 3, 10_000, 12_347, MAX_FEE_AMOUNT + 1, -1])
        table = tables.get(source, type(canonical_split_table("dex"))(2_500, 2_500, 2_500, 2_500))
        result = route_fee(source=source, asset=asset, amount=amount, split_table=table, accumulator=acc)
        if isinstance(result, RouteAccepted):
            accepted += 1
            acc = result.accumulator
        else:
            rejected += 1
            assert acc.state_root() == before

    assert accepted > 0
    assert rejected > 0


def test_selector_fails_closed_on_malformed_rust_output(rust_env, monkeypatch):
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))

    def malformed_output(**kwargs):
        return {"version": 1, "kernel": "fee_router", "accept": True}

    monkeypatch.setattr("src.runtime.rust_invoker.fee_route", malformed_output)
    with pytest.raises(AuthorityError):
        route_fee(
            source="dex",
            asset="zUSD",
            amount=1,
            split_table=canonical_split_table("dex"),
            accumulator=FeeAccumulator(),
        )
