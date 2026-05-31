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

from src.core.perps import PerpAccountState  # noqa: E402
from src.state.balances import BalanceTable  # noqa: E402
from src.runtime.authority import (  # noqa: E402
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from tools.runtime import perp_funding_auto_lib as fa  # noqa: E402

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


def test_rust_shadow_skips_oversized_materialized_account_table(monkeypatch):
    # DbC/security regression: a Sybil-bloated market must not make rust_shadow
    # serialize/parse/echo an unbounded account table. Python remains authoritative
    # for oversized shadow-only materialization, just like when Rust is unavailable.
    from src.integration import perp_engine
    from src.runtime import rust_invoker

    market_id = "perp:shadow-oversized"
    state = _settled(market_id)
    assert state.perps is not None

    account = PerpAccountState(
        position_base=0,
        entry_price_e8=0,
        collateral_quote=0,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=0,
        liquidated_this_step=False,
    )
    market = state.perps.markets[market_id]
    accounts = {PK_A: account, PK_B: account}
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset,
        global_state=dict(market.global_state),
        accounts=accounts,
    )
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))

    def fail_if_invoked(request, **kwargs):
        raise AssertionError("oversized materialized shadow invoked Rust")

    monkeypatch.setattr(perp_engine, "_PERP_STATEFUL_MATERIALIZED_ACCOUNT_LIMIT", 1)
    monkeypatch.setattr(rust_invoker, "perp_isolated_op", fail_if_invoked)

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "advance_epoch", delta=1)],
    )

    assert res.ok is True, res.error
    assert int(res.state.perps.markets[market_id].global_state["epoch_phase"]) == 0


def test_rust_shadow_skips_materialized_request_above_bridge_stdin_cap(monkeypatch):
    from src.integration import perp_engine
    from src.runtime import rust_invoker

    market_id = "perp:shadow-oversized-request"
    state = _settled(market_id)

    def fail_if_invoked(request, **kwargs):
        raise AssertionError("oversized materialized request invoked Rust")

    monkeypatch.setattr(perp_engine, "_PERP_STATEFUL_MATERIALIZED_REQUEST_BYTES_LIMIT", 1)
    monkeypatch.setattr(rust_invoker, "perp_isolated_op", fail_if_invoked)

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "advance_epoch", delta=1)],
    )

    assert res.ok is True, res.error
    assert int(res.state.perps.markets[market_id].global_state["epoch_phase"]) == 0


def test_rust_shadow_skips_materialized_response_above_bridge_stdout_cap(monkeypatch):
    from src.integration import perp_engine
    from src.runtime import rust_invoker

    market_id = "perp:shadow-oversized-response"
    state = _settled(market_id)

    def fail_if_invoked(request, **kwargs):
        raise AssertionError("oversized materialized response invoked Rust")

    monkeypatch.setattr(perp_engine, "_PERP_STATEFUL_MATERIALIZED_RESPONSE_BYTES_LIMIT", 1)
    monkeypatch.setattr(rust_invoker, "perp_isolated_op", fail_if_invoked)

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "advance_epoch", delta=1)],
    )

    assert res.ok is True, res.error
    assert int(res.state.perps.markets[market_id].global_state["epoch_phase"]) == 0


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


def test_rust_authority_commits_advance_and_blocks_other_perp_stateful_ops(rust_env):
    # advance_epoch is the first true Rust-authority slice: Rust decides from the
    # pre-state and the Python shell commits the parsed Rust post-market. Other
    # perps stateful ops remain blocked until promoted one by one.
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
    assert res_adv.ok is True, res_adv.error
    assert int(res_adv.state.perps.markets["perp:auth-block-advance"].global_state["epoch_phase"]) == 0

    res_fund = fa._apply_result(
        state=funded,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op("perp:auth-block-funding", "apply_funding_auto")],
    )
    assert res_fund.ok is False
    assert "not live-wired" in (res_fund.error or "")


def test_rust_authority_advance_does_not_call_python_handler(rust_env, monkeypatch):
    # Pure rust_authority must not let the Python handler decide and then call Rust
    # as a post-check. It should call the materializer directly and commit Rust's
    # post-state.
    from src.integration import perp_engine

    state = _settled("perp:auth-rust-only-advance")

    def python_handler_must_not_run(*args, **kwargs):
        raise AssertionError("Python advance handler ran under pure rust_authority")

    monkeypatch.setitem(
        perp_engine._ISOLATED_ACTION_HANDLERS,
        "advance_epoch",
        python_handler_must_not_run,
    )
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op("perp:auth-rust-only-advance", "advance_epoch", delta=1)],
    )
    assert res.ok is True, res.error
    assert int(res.state.perps.markets["perp:auth-rust-only-advance"].global_state["epoch_phase"]) == 0


def test_rust_authority_with_python_shadow_fails_closed_on_advance_disagreement(rust_env, monkeypatch):
    from src.runtime import rust_invoker

    state = _settled("perp:auth-shadow-disagree-advance")
    original = rust_invoker.perp_isolated_op

    def tampered(request, **kwargs):
        out = original(request, **kwargs)
        out["post"]["global_state"]["now_epoch"] = "999999"
        return out

    monkeypatch.setattr(rust_invoker, "perp_isolated_op", tampered)
    set_active_authority_policy(_policy(AuthorityMode.RUST_AUTHORITY_WITH_PYTHON_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op("perp:auth-shadow-disagree-advance", "advance_epoch", delta=1)],
    )
    assert res.ok is False
    assert "disagreement" in (res.error or "")


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
    gs = dict(market.global_state)
    gs["min_notional_for_bounty"] = 0
    gs["liquidation_penalty_bps"] = 200
    accts = dict(market.accounts)
    accts[PK_A] = replace(accts[PK_A], collateral_quote=1)  # make it liquidatable
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset, global_state=gs, accounts=accts
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
    assert int(m.global_state["fee_pool_quote"]) > 0
    assert int(m.global_state["insurance_balance"]) > 0


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


def test_rust_shadow_fails_closed_on_funding_effect_tamper(rust_env, monkeypatch):
    # apply_funding_auto has a custom funding-summary effect rather than a nested
    # _common_effects payload. Full materialized parity still checks it exactly.
    from src.runtime import rust_invoker

    def tampered(request, **kwargs):
        out = rust_invoker.invoke("perp-isolated-op", request)
        out["effects"]["funding_sink_delta_quote"] = "99999"
        return out

    monkeypatch.setattr(rust_invoker, "perp_isolated_op", tampered)
    market_id = "perp:shadow-funding-effect-tamper"
    state = fa.build_market(
        market_id=market_id,
        quote_asset=QUOTE,
        positions=[(PK_A, 300_000), (PK_B, -100_000)],
        clearing_price_e8=101_000_000,
        deposit=1_000_000,
    )
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=OPERATOR,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "apply_funding_auto")],
    )
    assert res.ok is False
    assert "disagreement" in (res.error or "")


def test_rust_shadow_set_market_params_materialized_parity(rust_env):
    # set_market_params is full-state materialized: Rust must reproduce the
    # merged globals, carried accounts, and params effect payload.
    market_id = "perp:shadow-set-market-params"
    state = fa.build_market(
        market_id=market_id,
        quote_asset=QUOTE,
        positions=[(PK_A, 300_000)],
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
        ops=[
            fa._op(
                market_id,
                "set_market_params",
                params={"maintenance_margin_bps": 550, "funding_cap_bps": 500},
            )
        ],
    )
    assert res.ok is True, res.error
    market = res.state.perps.markets[market_id]
    assert int(market.global_state["maintenance_margin_bps"]) == 550
    assert int(market.global_state["funding_cap_bps"]) == 500
    assert int(market.accounts[PK_A].position_base) == 300_000


def _open_market(market_id: str, positions):
    # Bootstrap to an Open epoch with `positions`, so account ops are accepted.
    state = fa.build_market(
        market_id=market_id, quote_asset=QUOTE, positions=positions,
        clearing_price_e8=100_000_000, deposit=1_000_000,
    )
    state = fa._apply(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch")],
    )
    return fa._apply(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "advance_epoch", delta=1)],
    )


def test_rust_shadow_deposit_existing_account_parity(rust_env):
    # deposit_collateral materialized: rust_shadow compares the full post-market AND
    # the CollateralDeposited effect, which is computed on the affected account (the
    # position makes notional/maint NONZERO, not the flat-dummy zeros).
    market_id = "perp:shadow-deposit"
    state = _open_market(market_id, [(PK_A, 300_000)])
    pre = int(state.perps.markets[market_id].accounts[PK_A].collateral_quote)
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "deposit_collateral", account_pubkey=PK_A, amount=50_000)],
    )
    assert res.ok is True, res.error  # full state + account-effect parity held
    assert int(res.state.perps.markets[market_id].accounts[PK_A].collateral_quote) == pre + 50_000


def test_rust_shadow_deposit_request_carries_pre_state_balance_fact(rust_env, monkeypatch):
    # Future Rust authority depends on the request facts being real pre-state
    # integration facts, not hardcoded positives. In particular, deposit must carry
    # the wallet balance that Python checks before mutating collateral.
    from src.runtime import rust_invoker

    market_id = "perp:shadow-deposit-facts"
    state = _open_market(market_id, [(PK_A, 300_000)])
    pre_balance = int(state.balances.get(PK_A, QUOTE))
    seen: dict[str, object] = {}
    original = rust_invoker.perp_isolated_op

    def capture(request, **kwargs):
        seen.update(dict(request["facts"]))
        return original(request, **kwargs)

    monkeypatch.setattr(rust_invoker, "perp_isolated_op", capture)
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=PK_A,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "deposit_collateral", account_pubkey=PK_A, amount=50_000)],
    )
    assert res.ok is True, res.error
    assert seen["balance_available"] == str(pre_balance)
    assert seen["sender_bound_ok"] is True
    assert seen["operator_ok"] is False


def test_rust_materialized_post_round_trips_to_market_state_for_deposit(rust_env, monkeypatch):
    # Authority inversion needs this conversion: once Rust decides, the Python
    # shell must be able to commit the full Rust post-market without losing fields.
    from src.integration import perp_engine
    from src.runtime import rust_invoker

    market_id = "perp:shadow-deposit-post-roundtrip"
    state = _open_market(market_id, [(PK_A, 300_000)])
    captured: dict[str, object] = {}
    original = rust_invoker.perp_isolated_op

    def capture(request, **kwargs):
        out = original(request, **kwargs)
        captured["post"] = out["post"]
        return out

    monkeypatch.setattr(rust_invoker, "perp_isolated_op", capture)
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state,
        tx_sender_pubkey=PK_A,
        operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "deposit_collateral", account_pubkey=PK_A, amount=50_000)],
    )
    assert res.ok is True, res.error
    parsed = perp_engine._market_from_materialized_post(captured["post"])
    assert parsed == res.state.perps.markets[market_id]
    duplicated = dict(captured["post"])
    duplicated["accounts"] = list(captured["post"]["accounts"]) + [captured["post"]["accounts"][0]]
    with pytest.raises(ValueError, match="duplicate account key"):
        perp_engine._market_from_materialized_post(duplicated)


def test_rust_shadow_deposit_new_account_parity(rust_env):
    # First deposit to a pubkey with no prior account: Python creates it, and the
    # materializer must create the same flat account from the request (which does not
    # include it). Credit the wallet first so the deposit's balance check passes.
    market_id = "perp:shadow-deposit-new"
    pk_new = "cc" * 48
    state = _open_market(market_id, [])
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(pk_new, QUOTE, 1_000_000_000)
    state = replace(state, balances=funded)

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=pk_new, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "deposit_collateral", account_pubkey=pk_new, amount=50_000)],
    )
    assert res.ok is True, res.error  # parity including new-account creation
    accts = res.state.perps.markets[market_id].accounts
    assert pk_new in accts
    assert int(accts[pk_new].collateral_quote) == 50_000


def test_rust_shadow_deposit_resets_liquidated_flag(rust_env):
    # Regression: a liquidation flag set in settle persists through advance_epoch
    # (which copies real accounts verbatim); a subsequent deposit must reset it
    # (apply_deposit_collateral forces False). The materializer must mirror that —
    # preserving the pre-flag would diverge and false-reject a valid deposit.
    market_id = "perp:shadow-deposit-liq"
    state = fa.build_market(
        market_id=market_id, quote_asset=QUOTE,
        positions=[(PK_A, 500_000)], clearing_price_e8=101_000_000, deposit=1_000_000,
    )  # PricePublished
    market = state.perps.markets[market_id]
    gs = dict(market.global_state)
    gs["min_notional_for_bounty"] = 0
    gs["liquidation_penalty_bps"] = 200
    accts = dict(market.accounts)
    accts[PK_A] = replace(accts[PK_A], collateral_quote=1)  # liquidatable
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(quote_asset=market.quote_asset, global_state=gs, accounts=accts)
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))
    # settle liquidates PK_A; advance to Open carries the flag forward.
    state = fa._apply(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch")],
    )
    state = fa._apply(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "advance_epoch", delta=1)],
    )
    assert state.perps.markets[market_id].accounts[PK_A].liquidated_this_step is True  # persisted

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "deposit_collateral", account_pubkey=PK_A, amount=50_000)],
    )
    assert res.ok is True, res.error  # parity: materializer resets the flag like Python
    assert res.state.perps.markets[market_id].accounts[PK_A].liquidated_this_step is False


def test_rust_shadow_withdraw_existing_account_parity(rust_env):
    # withdraw_collateral materialized: rust_shadow compares the full post-market AND
    # the CollateralWithdrawn effect (account context -> nonzero notional/maint).
    market_id = "perp:shadow-withdraw"
    state = _open_market(market_id, [(PK_A, 300_000)])
    pre = int(state.perps.markets[market_id].accounts[PK_A].collateral_quote)
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "withdraw_collateral", account_pubkey=PK_A, amount=10_000)],
    )
    assert res.ok is True, res.error  # full state + account-effect parity held
    assert int(res.state.perps.markets[market_id].accounts[PK_A].collateral_quote) == pre - 10_000


def test_rust_shadow_withdraw_resets_liquidated_flag(rust_env):
    # Regression mirror of the deposit case: a liquidation flag carried forward must
    # be reset by withdraw too (apply_withdraw_collateral forces False). A genuinely
    # liquidated account ends flat with collateral 0, so no withdraw is accepted on
    # it; instead carry the flag onto a flat *funded* account (the realistic shape:
    # the flag persists through advance, which copies real accounts verbatim) and
    # withdraw a small amount that stays within collateral and cannot breach margin.
    market_id = "perp:shadow-withdraw-liq"
    state = _open_market(market_id, [])
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(PK_A, QUOTE, 1_000_000_000)
    state = replace(state, balances=funded)
    state = fa._apply(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "deposit_collateral", account_pubkey=PK_A, amount=500_000)],
    )
    market = state.perps.markets[market_id]
    accts = dict(market.accounts)
    accts[PK_A] = replace(accts[PK_A], liquidated_this_step=True)  # carry the prior flag
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset, global_state=dict(market.global_state), accounts=accts
    )
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))
    assert state.perps.markets[market_id].accounts[PK_A].liquidated_this_step is True

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "withdraw_collateral", account_pubkey=PK_A, amount=10_000)],
    )
    assert res.ok is True, res.error  # parity: materializer resets the flag like Python
    assert res.state.perps.markets[market_id].accounts[PK_A].liquidated_this_step is False


def test_rust_shadow_set_position_parity(rust_env):
    # set_position materialized: rust_shadow compares the full post-market AND the
    # PositionSet effect (account context -> nonzero notional/maint/init). Setting a
    # new position moves position_base and entry_price_e8 := index.
    market_id = "perp:shadow-setpos"
    state = _open_market(market_id, [(PK_A, 300_000)])
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "set_position", account_pubkey=PK_A, new_position_base=500_000)],
    )
    assert res.ok is True, res.error  # full state + account-effect parity held
    acct = res.state.perps.markets[market_id].accounts[PK_A]
    assert int(acct.position_base) == 500_000


def test_rust_shadow_set_position_short_parity(rust_env):
    # new_position_base is signed: a short (negative) must round-trip through the
    # request as a decimal string and parity-match (notional uses |position|).
    market_id = "perp:shadow-setpos-short"
    state = _open_market(market_id, [(PK_A, 300_000)])
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "set_position", account_pubkey=PK_A, new_position_base=-200_000)],
    )
    assert res.ok is True, res.error  # parity including the signed/negative path
    assert int(res.state.perps.markets[market_id].accounts[PK_A].position_base) == -200_000


def test_rust_shadow_set_position_zero_creates_new_account_parity(rust_env):
    # Mirrors Python's account-op behavior: a missing account is treated as a flat
    # initial account, so setting a zero position materializes a flat account.
    market_id = "perp:shadow-setpos-new-flat"
    state = _open_market(market_id, [])
    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "set_position", account_pubkey=PK_A, new_position_base=0)],
    )
    assert res.ok is True, res.error
    acct = res.state.perps.markets[market_id].accounts[PK_A]
    assert int(acct.position_base) == 0
    assert int(acct.entry_price_e8) == 0
    assert int(acct.collateral_quote) == 0


def test_rust_shadow_set_position_resets_liquidated_flag(rust_env):
    # A carried liquidation flag must be reset by set_position too
    # (apply_set_position forces False), with funding fields preserved.
    market_id = "perp:shadow-setpos-liq"
    state = _open_market(market_id, [(PK_A, 300_000)])
    market = state.perps.markets[market_id]
    accts = dict(market.accounts)
    accts[PK_A] = replace(accts[PK_A], liquidated_this_step=True)  # carry the prior flag
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset, global_state=dict(market.global_state), accounts=accts
    )
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))
    assert state.perps.markets[market_id].accounts[PK_A].liquidated_this_step is True

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "set_position", account_pubkey=PK_A, new_position_base=400_000)],
    )
    assert res.ok is True, res.error  # parity: materializer resets the flag like Python
    assert res.state.perps.markets[market_id].accounts[PK_A].liquidated_this_step is False


def test_rust_shadow_clear_breaker_materialized_parity(rust_env):
    # clear_breaker is now materialized (operator-gated GLOBAL op): rust_shadow
    # compares the full post-market (both breaker globals reset; accounts verbatim)
    # AND the flat-dummy BreakerCleared effect. A flat funded account is present to
    # confirm it passes through untouched. (The legacy test_rust_shadow_checks_
    # clear_breaker also exercises this path; this one asserts the materialized
    # full-state reset explicitly.)
    market_id = "perp:shadow-clearbrk"
    state = _open_market(market_id, [])  # flat -> all_positions_flat holds
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(PK_A, QUOTE, 1_000_000_000)
    state = replace(state, balances=funded)
    state = fa._apply(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "deposit_collateral", account_pubkey=PK_A, amount=500_000)],
    )
    market = state.perps.markets[market_id]
    gs = dict(market.global_state)
    gs["breaker_active"] = True
    gs["breaker_last_trigger_epoch"] = int(gs["now_epoch"])
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset, global_state=gs, accounts=dict(market.accounts)
    )
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "clear_breaker")],
    )
    assert res.ok is True, res.error  # full state + BreakerCleared effect parity held
    post = res.state.perps.markets[market_id]
    assert post.global_state["breaker_active"] is False
    assert int(post.global_state["breaker_last_trigger_epoch"]) == 0  # reset
    assert int(post.accounts[PK_A].collateral_quote) == 500_000  # account untouched


def test_rust_shadow_partial_liquidate_nonzero_penalty_parity(rust_env):
    # partial_liquidate is materialized: rust_shadow compares the full post-market
    # (post account + the ACCUMULATED fee/insurance globals) AND the
    # PartialLiquidationApplied effect, whose after-values come from the POST
    # (accumulated) globals over the POST account. Drive a sizable nonzero penalty
    # through the full bridge so the accumulation branch is exercised (not just the
    # 1-unit degenerate case) -- the branch Codex flagged for special attention.
    market_id = "perp:shadow-pliq"
    state = fa.build_market(
        market_id=market_id, quote_asset=QUOTE,
        positions=[(PK_A, 500_000)], clearing_price_e8=100_000_000, deposit=1_000_000,
    )
    state = fa._apply(
        state=state, tx_sender_pubkey=OPERATOR, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "settle_epoch"), fa._op(market_id, "advance_epoch", delta=1)],
    )
    market = state.perps.markets[market_id]
    gs = dict(market.global_state)
    gs["min_notional_for_bounty"] = 0
    gs["liquidation_penalty_bps"] = 500  # 5% -> sizable penalty
    accts = dict(market.accounts)
    accts[PK_A] = replace(accts[PK_A], collateral_quote=25_000)  # underwater (maint 30000)
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(quote_asset=market.quote_asset, global_state=gs, accounts=accts)
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))

    set_active_authority_policy(_policy(AuthorityMode.RUST_SHADOW))
    res = fa._apply_result(
        state=state, tx_sender_pubkey=PK_A, operator_pubkey=OPERATOR,
        ops=[fa._op(market_id, "partial_liquidate", account_pubkey=PK_A, fraction_bps=0)],
    )
    assert res.ok is True, res.error  # full state + effect parity on the accumulation branch
    post = res.state.perps.markets[market_id]
    assert post.accounts[PK_A].liquidated_this_step is True
    assert int(post.global_state["fee_pool_quote"]) > 1  # nonzero accumulation, not degenerate
    assert int(post.global_state["insurance_balance"]) > 1
