from __future__ import annotations

import importlib.util
from dataclasses import replace

import pytest

from src.core.dex import DexState
from src.state.balances import BalanceTable
from src.state.lp import LPTable


if importlib.util.find_spec("ESSO") is None:  # pragma: no cover
    pytest.skip("ESSO not installed (expected via external/ESSO or site package)", allow_module_level=True)


def _op(market_id: str, action: str, **kwargs: object) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "0.1",
        "market_id": market_id,
        "action": action,
    }
    op.update(kwargs)
    return op


def _apply_result(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], operator_pubkey: str):
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(operator_pubkey=operator_pubkey)
    return apply_perp_ops(config=cfg, state=state, operations={"5": ops}, tx_sender_pubkey=tx_sender_pubkey)


def _apply(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], operator_pubkey: str) -> DexState:
    res = _apply_result(state=state, tx_sender_pubkey=tx_sender_pubkey, operator_pubkey=operator_pubkey, ops=ops)
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def test_settle_epoch_is_order_independent() -> None:
    market_id = "perp:demo"
    quote_asset = "0x" + "33" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # Init market (operator).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )

    # Epoch 1: establish an oracle/index price (no accounts yet).
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Fund both traders so they can deposit collateral.
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000)
    funded.set(bob, quote_asset, 1_000_000)
    state = replace(state, balances=funded)

    # Open positions (trader-authenticated).
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", account_pubkey=alice, amount=1000), _op(market_id, "set_position", account_pubkey=alice, new_position_base=100)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", account_pubkey=bob, amount=1000), _op(market_id, "set_position", account_pubkey=bob, new_position_base=-100)],
    )

    # Epoch 2: publish a new clearing price (pre-settle state).
    pre = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    pre = _apply(
        state=pre,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=95_000_000)],
    )

    # Construct an equivalent state but with reversed account insertion order.
    assert pre.perps is not None
    market = pre.perps.markets[market_id]
    reversed_accounts = dict(reversed(list(market.accounts.items())))
    market_rev = type(market)(quote_asset=market.quote_asset, global_state=dict(market.global_state), accounts=reversed_accounts)
    perps_rev = type(pre.perps)(version=pre.perps.version, markets={market_id: market_rev})
    pre_rev = replace(pre, perps=perps_rev)

    # Settle epoch from both pre-states and compare.
    post = _apply(state=pre, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])
    post_rev = _apply(state=pre_rev, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    assert post.perps == post_rev.perps


def test_settle_epoch_accumulates_fee_pool_for_mixed_liquidation() -> None:
    market_id = "perp:liq"
    quote_asset = "0x" + "44" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # Init market (operator).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )

    # Epoch 1: establish an oracle/index price (no accounts yet).
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Fund both traders so they can deposit collateral.
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000)
    funded.set(bob, quote_asset, 1_000_000)
    state = replace(state, balances=funded)

    # Open positions (trader-authenticated).
    # Use a configuration where Alice becomes under-maintenance after a 5% price drop
    # but still has positive collateral, so a nonzero liquidation penalty is collected.
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", account_pubkey=alice, amount=100), _op(market_id, "set_position", account_pubkey=alice, new_position_base=1000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", account_pubkey=bob, amount=100), _op(market_id, "set_position", account_pubkey=bob, new_position_base=-1000)],
    )

    # Epoch 2: publish a new clearing price (pre-settle state).
    pre = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    pre = _apply(state=pre, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=95_000_000)])

    # Construct an equivalent state but with reversed account insertion order.
    assert pre.perps is not None
    market = pre.perps.markets[market_id]
    reversed_accounts = dict(reversed(list(market.accounts.items())))
    market_rev = type(market)(quote_asset=market.quote_asset, global_state=dict(market.global_state), accounts=reversed_accounts)
    perps_rev = type(pre.perps)(version=pre.perps.version, markets={market_id: market_rev})
    pre_rev = replace(pre, perps=perps_rev)

    post = _apply(state=pre, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])
    post_rev = _apply(state=pre_rev, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    assert post.perps == post_rev.perps

    assert post.perps is not None
    m = post.perps.markets[market_id]
    assert int(m.global_state["fee_pool_quote"]) == 4

    acct_alice = m.accounts[alice]
    acct_bob = m.accounts[bob]

    # Alice: liquidated (position forced to 0) with penalty collected into fee pool.
    assert acct_alice.position_base == 0
    assert acct_alice.entry_price_e8 == 0
    assert acct_alice.collateral_quote == 46

    # Bob: remains open and gains PnL from the price move.
    assert acct_bob.position_base == -1000
    assert acct_bob.entry_price_e8 == 95_000_000
    assert acct_bob.collateral_quote == 150


def test_breaker_reduce_only_and_clear() -> None:
    market_id = "perp:demo"
    quote_asset = "0x" + "44" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # Init market (operator).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )

    # Epoch 1: establish an oracle/index price (no accounts yet).
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Fund both traders so they can deposit collateral.
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000)
    funded.set(bob, quote_asset, 1_000_000)
    state = replace(state, balances=funded)

    # Open positions while breaker is inactive.
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", account_pubkey=alice, amount=1000), _op(market_id, "set_position", account_pubkey=alice, new_position_base=100)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", account_pubkey=bob, amount=1000), _op(market_id, "set_position", account_pubkey=bob, new_position_base=-100)],
    )

    # Epoch 2: publish a wildly out-of-bounds move (settle clamps + triggers breaker).
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=200_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert market.global_state["breaker_active"] is True
    # Default max_oracle_move_bps=500 => clamp to +5% from 1.00 to 1.05.
    assert market.global_state["index_price_e8"] == 105_000_000
    assert market.global_state["breaker_last_trigger_epoch"] == 2

    # Breaker posture: no opening while breaker is active (bob is already open; new account cannot open).
    res_open = _apply_result(
        state=state,
        tx_sender_pubkey="cc" * 48,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey="cc" * 48, new_position_base=1)],
    )
    assert res_open.ok is False

    # Breaker posture: cannot increase exposure.
    res_inc = _apply_result(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=200)],
    )
    assert res_inc.ok is False

    # Breaker posture: reduce is allowed.
    state = _apply(state=state, tx_sender_pubkey=alice, operator_pubkey=operator, ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=50)])

    # Breaker posture: no sign flip unless closing to 0.
    res_flip = _apply_result(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=-50)],
    )
    assert res_flip.ok is False

    # Clear breaker fails while positions are open (engine-level fail-closed).
    res_clear_open = _apply_result(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "clear_breaker")])
    assert res_clear_open.ok is False
    assert res_clear_open.error == "cannot clear breaker while positions are open"

    # Close out all positions.
    state = _apply(state=state, tx_sender_pubkey=alice, operator_pubkey=operator, ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=0)])
    state = _apply(state=state, tx_sender_pubkey=bob, operator_pubkey=operator, ops=[_op(market_id, "set_position", account_pubkey=bob, new_position_base=0)])

    # Clear breaker requires operator key.
    res_clear_nonop = _apply_result(state=state, tx_sender_pubkey=alice, operator_pubkey=operator, ops=[_op(market_id, "clear_breaker")])
    assert res_clear_nonop.ok is False
    assert res_clear_nonop.error == "operator only"

    # Operator can clear breaker once all accounts are flat.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "clear_breaker")])
    assert state.perps is not None
    market2 = state.perps.markets[market_id]
    assert market2.global_state["breaker_active"] is False


def test_operator_cannot_skip_settlement() -> None:
    market_id = "perp:demo"
    quote_asset = "0x" + "55" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])

    # Once a clearing price is published, the operator must settle before advancing or re-publishing.
    res_adv = _apply_result(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    assert res_adv.ok is False
    assert res_adv.error == "cannot advance epoch before settling current epoch"

    res_pub = _apply_result(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=101_000_000)])
    assert res_pub.ok is False
