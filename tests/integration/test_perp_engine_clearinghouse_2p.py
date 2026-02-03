from __future__ import annotations

from dataclasses import replace

from src.core.dex import DexState
from src.core.perps import PerpClearinghouse2pMarketState
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _op(market_id: str, action: str, *, version: str, **kwargs: object) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": version,
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


def test_init_market_2p_is_strict_about_prefix_and_operator() -> None:
    quote_asset = "0x" + "33" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # v0.2 market ids are namespaced (fail-closed so semantics don't mix by accident).
    bad_market_id = "perp:demo"
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                bad_market_id,
                "init_market_2p",
                version="1.0",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
            )
        ],
    )
    assert not res.ok
    assert res.error is not None and "perp:ch2p:" in res.error

    market_id = "perp:ch2p:demo"
    res2 = _apply_result(
        state=state,
        tx_sender_pubkey="ff" * 48,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "init_market_2p",
                version="1.0",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
            )
        ],
    )
    assert not res2.ok
    assert res2.error == "operator only"


def test_set_position_pair_requires_net_zero() -> None:
    market_id = "perp:ch2p:netzero"
    quote_asset = "0x" + "44" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "init_market_2p",
                version="1.0",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
            )
        ],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_position_pair",
                version="1.0",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                new_position_base_a=1,
                new_position_base_b=0,
            )
        ],
    )
    assert not res.ok
    assert res.error == "clearinghouse_2p requires net position == 0"


def test_settle_epoch_2p_preserves_exact_conservation_in_quote_e8() -> None:
    market_id = "perp:ch2p:dust"
    quote_asset = "0x" + "55" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    funded = BalanceTable()
    funded.set(alice, quote_asset, 10)
    funded.set(bob, quote_asset, 10)
    state = DexState(balances=funded, pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "init_market_2p",
                version="1.0",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
            )
        ],
    )

    # Epoch 1: initialize index price at 1.00.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="1.0", price_e8=100_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="1.0")])

    # Minimal collateral so the initial-margin guard is satisfiable.
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=alice, amount=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=bob, amount=1)],
    )

    # Open a tiny matched pair position (net-zero, quote-e8 accounting).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_position_pair",
                version="1.0",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                new_position_base_a=1,
                new_position_base_b=-1,
            )
        ],
    )

    # Epoch 2: a +1 tick move in price_e8 creates xs=[+1, -1] at settlement.
    # With quote-e8 collateral, this is exact and must conserve total deposits.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="1.0", price_e8=100_000_001)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="1.0")])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse2pMarketState)
    assert m.account_a_pubkey == alice
    assert m.account_b_pubkey == bob
    assert int(m.state["collateral_e8_a"]) + int(m.state["collateral_e8_b"]) + int(m.state["fee_pool_e8"]) == int(
        m.state["net_deposited_e8"]
    )


def test_settle_epoch_2p_pair_liquidation_closes_both_positions() -> None:
    market_id = "perp:ch2p:liq"
    quote_asset = "0x" + "66" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # Seed balances (collateral deposits draw from balances).
    funded = BalanceTable()
    funded.set(alice, quote_asset, 1000)
    funded.set(bob, quote_asset, 1000)
    state = replace(state, balances=funded)

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "init_market_2p",
                version="1.0",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
            )
        ],
    )

    # Epoch 1: establish index price.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="1.0", price_e8=100_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="1.0")])

    # Deposit collateral for both sides (user-authenticated).
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=alice, amount=100)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="1.0", account_pubkey=bob, amount=100)],
    )

    # Open a matched pair position.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_position_pair",
                version="1.0",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                new_position_base_a=1000,
                new_position_base_b=-1000,
            )
        ],
    )

    # Epoch 2: a +5% move makes the short side under maintenance; pair liquidation closes both positions.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="1.0", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="1.0", price_e8=105_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="1.0")])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse2pMarketState)
    assert int(m.state["fee_pool_e8"]) == 525_000_000
    assert int(m.state["collateral_e8_a"]) == 15_000_000_000
    assert int(m.state["collateral_e8_b"]) == 4_475_000_000
    assert int(m.state["position_base_a"]) == 0
    assert int(m.state["position_base_b"]) == 0
    assert int(m.state["entry_price_e8_a"]) == 0
    assert int(m.state["entry_price_e8_b"]) == 0
    assert int(m.state["collateral_e8_a"]) + int(m.state["collateral_e8_b"]) + int(m.state["fee_pool_e8"]) == int(
        m.state["net_deposited_e8"]
    )
