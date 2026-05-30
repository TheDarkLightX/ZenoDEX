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


def test_rust_shadow_advance_full_state_and_effects_parity(rust_env):
    # advance_epoch is materialized: under rust_shadow the selector compares the full
    # Rust post-market AND the exact kernel effect payload vs Python, accepting on
    # parity. Python stays authoritative; Rust post-checks, fail-closed on mismatch.
    market_id = "perp:shadow-advance"
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
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "advance_epoch", delta=1)],
    )
    assert res.ok is True, res.error
    assert int(res.state.perps.markets[market_id].global_state["epoch_phase"]) == 0


def test_rust_authority_blocks_all_perp_stateful_ops(rust_env):
    # No perp_stateful op has a true Rust-authority path: Rust post-checks Python's
    # transition, it does not decide from the pre-state nor commit its materialized
    # result. So authority modes fail closed for advance_epoch (materialized) and
    # apply_funding_auto (unmaterialized) alike, rather than letting Python decide.
    # Build the pre-states first under the default python_authority policy.
    advance_state = _settled("perp:auth-block-advance")
    funded = fa.build_market(
        market_id="perp:auth-block-funding",
        quote_asset=QUOTE,
        positions=[(PK_A, 300_000), (PK_B, -300_000)],
        clearing_price_e8=101_000_000,
        deposit=1_000_000,
    )
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    res_adv = fa._apply_result(
        state=advance_state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op("perp:auth-block-advance", "advance_epoch", delta=1)],
    )
    assert res_adv.ok is False
    assert "not live-wired" in (res_adv.error or "")

    res_fund = fa._apply_result(
        state=funded,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op("perp:auth-block-funding", "apply_funding_auto")],
    )
    assert res_fund.ok is False
    assert "not live-wired" in (res_fund.error or "")


def _settled(market_id: str):
    state = fa.build_market(
        market_id=market_id, quote_asset=QUOTE, positions=[], clearing_price_e8=100_000_000, deposit=1_000_000
    )
    return fa._apply(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR, ops=[fa._op(market_id, "settle_epoch")]
    )


def _open(market_id: str):
    # Settled -> advance -> Open, so publish_clearing_price's guard (Open + cpe<now) holds.
    state = _settled(market_id)
    return fa._apply(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "advance_epoch", delta=1)],
    )


def test_rust_shadow_publish_full_state_and_effects_parity(rust_env):
    # publish_clearing_price is materialized: rust_shadow compares the full post-market
    # + the exact ClearingPricePublished effect vs Python, accepting on parity.
    market_id = "perp:shadow-publish"
    state = _open(market_id)
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "publish_clearing_price", price_e8=101_000_000)],
    )
    assert res.ok is True, res.error
    gs = res.state.perps.markets[market_id].global_state
    assert int(gs["epoch_phase"]) == 1
    assert int(gs["clearing_price_e8"]) == 101_000_000


def test_rust_shadow_settle_full_state_and_effects_parity(rust_env):
    # settle_epoch is materialized (the first account-mutating op): rust_shadow
    # compares the full settled post-market (global fee/insurance + every account's
    # realized P&L) AND the EpochSettled effect. build_market leaves PricePublished.
    market_id = "perp:shadow-settle"
    state = fa.build_market(
        market_id=market_id, quote_asset=QUOTE,
        positions=[(PK_A, 300_000), (PK_B, -300_000)],
        clearing_price_e8=101_000_000, deposit=1_000_000,
    )
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch")],
    )
    assert res.ok is True, res.error
    m = res.state.perps.markets[market_id]
    assert int(m.global_state["epoch_phase"]) == 2
    # P&L was realized (parity already enforced by the shadow compare).
    assert int(m.accounts[PK_A].collateral_quote) != 1_000_000
    assert int(m.accounts[PK_B].collateral_quote) != 1_000_000


def test_rust_shadow_settle_liquidation_parity(rust_env):
    # Force a liquidatable account (large position, tiny collateral) into settle and
    # confirm full-state + effect parity on the penalty-accumulation path (the branch
    # that mutates fee_pool/insurance), not just the plain-P&L path.
    market_id = "perp:shadow-settle-liq"
    state = fa.build_market(
        market_id=market_id, quote_asset=QUOTE,
        positions=[(PK_A, 500_000)],
        clearing_price_e8=101_000_000, deposit=1_000_000,
    )  # PricePublished
    market = state.perps.markets[market_id]
    accts = dict(market.accounts)
    accts[PK_A] = replace(accts[PK_A], collateral_quote=1)  # make it liquidatable
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset, global_state=dict(market.global_state), accounts=accts
    )
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch")],
    )
    assert res.ok is True, res.error  # rust_shadow accepted -> full state + effect agreed
    m = res.state.perps.markets[market_id]
    assert int(m.accounts[PK_A].position_base) == 0  # liquidated -> flat
    assert m.accounts[PK_A].liquidated_this_step is True


def test_rust_shadow_fails_closed_on_state_tamper(rust_env, monkeypatch):
    # rust_shadow is fail-closed: a corrupted Rust post-state diverges from Python
    # and rejects the op rather than silently accepting.
    from src.runtime import rust_invoker

    def tampered(request, **kwargs):
        out = rust_invoker.invoke("perp-isolated-op", request)
        out["post"]["global_state"]["now_epoch"] = "999999"  # corrupt the post-state
        return out

    monkeypatch.setattr(rust_invoker, "perp_isolated_op", tampered)
    state = _settled("perp:shadow-state-tamper")
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op("perp:shadow-state-tamper", "advance_epoch", delta=1)],
    )
    assert res.ok is False
    assert "disagreement" in (res.error or "")


def test_rust_shadow_fails_closed_on_effect_tamper(rust_env, monkeypatch):
    # The receipt-drift regression: post-STATE matches but the effect payload differs.
    # Effect parity must catch it (state-only comparison would have passed).
    from src.runtime import rust_invoker

    def tampered(request, **kwargs):
        out = rust_invoker.invoke("perp-isolated-op", request)
        out["effects"]["effective_maint_bps"] = "99999"  # corrupt effect; state intact
        return out

    monkeypatch.setattr(rust_invoker, "perp_isolated_op", tampered)
    state = _settled("perp:shadow-effect-tamper")
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op("perp:shadow-effect-tamper", "advance_epoch", delta=1)],
    )
    assert res.ok is False
    assert "disagreement" in (res.error or "")
