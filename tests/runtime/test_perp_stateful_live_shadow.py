"""Live-path wiring tests for stateful isolated-perps Rust shadow checks."""

from __future__ import annotations

import os
import sys
from dataclasses import replace
from pathlib import Path

import pytest

_REPO = Path(__file__).resolve().parents[2]
_TOOLS_RUNTIME = _REPO / "tools" / "runtime"
for _p in (str(_REPO), str(_TOOLS_RUNTIME)):
    if _p not in sys.path:
        sys.path.insert(0, _p)

from rust_shadow_replay import ShadowError, locate_or_build_cli  # noqa: E402
from tools.runtime import perp_funding_auto_lib as fa  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)


OPERATOR = fa.OPERATOR
PK_A = "aa" * 48
PK_B = "bb" * 48
QUOTE = "0x" + "51" * 32


def _policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"perp_stateful": mode},
        promoted_surfaces=frozenset(),
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


def test_rust_shadow_checks_accepted_isolated_lifecycle(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    market_id = "perp:live-shadow"
    state = fa.build_market(
        market_id=market_id,
        quote_asset=QUOTE,
        positions=[(PK_A, 300_000), (PK_B, -300_000)],
        clearing_price_e8=101_000_000,
        deposit=1_000_000,
    )

    state = fa._apply(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "apply_funding_auto")],
    )
    state = fa._apply(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch")],
    )
    state = fa._apply(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "set_market_params", params={})],
    )
    assert state.perps is not None
    assert market_id in state.perps.markets


def test_rust_shadow_checks_clear_breaker(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    market_id = "perp:live-clear"
    state = fa.build_market(
        market_id=market_id,
        quote_asset=QUOTE,
        positions=[],
        clearing_price_e8=100_000_000,
        deposit=1_000_000,
    )
    state = fa._apply(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch"), fa._op(market_id, "advance_epoch", delta=1)],
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = dict(market.global_state)
    gs["breaker_active"] = True
    gs["breaker_last_trigger_epoch"] = int(gs["now_epoch"])
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(quote_asset=market.quote_asset, global_state=gs, accounts=dict(market.accounts))
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))

    state = fa._apply(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "clear_breaker")],
    )
    post = state.perps.markets[market_id]
    assert post.global_state["breaker_active"] is False


def test_rust_shadow_checks_partial_liquidate(rust_env):
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    market_id = "perp:live-liq"
    state = fa.build_market(
        market_id=market_id,
        quote_asset=QUOTE,
        positions=[(PK_A, 500_000)],
        clearing_price_e8=100_000_000,
        deposit=1_000_000,
    )
    state = fa._apply(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch"), fa._op(market_id, "advance_epoch", delta=1)],
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    acct = market.accounts[PK_A]
    accts = dict(market.accounts)
    accts[PK_A] = replace(acct, collateral_quote=1)
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(quote_asset=market.quote_asset, global_state=dict(market.global_state), accounts=accts)
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))

    state = fa._apply(
        state=state,
        tx_sender_pubkey=PK_A,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "partial_liquidate", account_pubkey=PK_A, fraction_bps=0)],
    )
    assert state.perps.markets[market_id].accounts[PK_A].position_base == 0


def test_rust_shadow_unavailable_keeps_python():
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
        state = fa.build_market(
            market_id="perp:live-unavailable",
            quote_asset=QUOTE,
            positions=[],
            clearing_price_e8=100_000_000,
            deposit=1_000_000,
        )
        assert state.perps is not None
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old


def test_rust_authority_advance_epoch_materialized_accepts(rust_env):
    # advance_epoch is now materialized: under rust_authority_with_python_shadow the
    # selector compares the full Rust post-market vs Python and accepts on parity.
    market_id = "perp:live-authority-advance"
    state = fa.build_market(
        market_id=market_id,
        quote_asset=QUOTE,
        positions=[],
        clearing_price_e8=100_000_000,
        deposit=1_000_000,
    )
    state = fa._apply(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch")],
    )
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "advance_epoch", delta=1)],
    )
    assert res.ok is True, res.error
    assert int(res.state.perps.markets[market_id].global_state["epoch_phase"]) == 0


def test_rust_authority_rejects_unmaterialized_op(rust_env):
    # Ops without a full materialized Rust transition stay blocked under authority.
    market_id = "perp:live-authority-block"
    state = fa.build_market(
        market_id=market_id,
        quote_asset=QUOTE,
        positions=[(PK_A, 300_000), (PK_B, -300_000)],
        clearing_price_e8=101_000_000,
        deposit=1_000_000,
    )
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "apply_funding_auto")],
    )
    assert res.ok is False
    assert "not live-wired for this op" in (res.error or "")


def _settled(market_id: str):
    state = fa.build_market(
        market_id=market_id, quote_asset=QUOTE, positions=[], clearing_price_e8=100_000_000, deposit=1_000_000
    )
    return fa._apply(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[fa._op(market_id, "settle_epoch")]
    )


def test_rust_authority_fails_closed_on_injected_disagreement(rust_env, monkeypatch):
    from src.runtime import rust_invoker

    def tampered(request, **kwargs):
        out = rust_invoker.invoke("perp-isolated-op", request)
        out["post"]["global_state"]["now_epoch"] = "999999"  # corrupt the post-state
        return out

    monkeypatch.setattr(rust_invoker, "perp_isolated_op", tampered)
    state = _settled("perp:live-disagree")
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op("perp:live-disagree", "advance_epoch", delta=1)],
    )
    assert res.ok is False
    assert "disagreement" in (res.error or "")


def test_rust_authority_advance_unavailable_fails_closed():
    state = _settled("perp:live-auth-unavail")  # built under default python_authority
    old = os.environ.get("ZENODEX_RUNTIME_BIN")
    os.environ["ZENODEX_RUNTIME_BIN"] = str(_REPO / "rust-runtime" / "target" / "nonexistent-bin")
    try:
        set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
        res = fa._apply_result(
            state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
            ops=[fa._op("perp:live-auth-unavail", "advance_epoch", delta=1)],
        )
        assert res.ok is False  # Rust unavailable + authoritative -> fail closed
    finally:
        if old is None:
            os.environ.pop("ZENODEX_RUNTIME_BIN", None)
        else:
            os.environ["ZENODEX_RUNTIME_BIN"] = old
