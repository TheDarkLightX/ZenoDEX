from __future__ import annotations

from src.core.dex import DexState
from src.core.perps import PerpClearinghouse3pTransferMarketState
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


def test_init_market_3p_is_strict_about_prefix_and_operator() -> None:
    quote_asset = "0x" + "33" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48
    carol = "cc" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    bad_market_id = "perp:demo"
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                bad_market_id,
                "init_market_3p",
                version="1.1",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                account_c_pubkey=carol,
            )
        ],
    )
    assert not res.ok
    assert res.error is not None and "perp:ch3p:" in res.error

    market_id = "perp:ch3p:demo"
    res2 = _apply_result(
        state=state,
        tx_sender_pubkey="ff" * 48,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "init_market_3p",
                version="1.1",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                account_c_pubkey=carol,
            )
        ],
    )
    assert not res2.ok
    assert res2.error == "operator only"


def test_set_position_triplet_requires_net_zero_and_one_idle() -> None:
    market_id = "perp:ch3p:netzero"
    quote_asset = "0x" + "44" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48
    carol = "cc" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "init_market_3p",
                version="1.1",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                account_c_pubkey=carol,
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
                "set_position_triplet",
                version="1.1",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                account_c_pubkey=carol,
                new_position_base_a=1,
                new_position_base_b=0,
                new_position_base_c=0,
            )
        ],
    )
    assert not res.ok
    assert res.error == "clearinghouse_3p requires net position == 0"

    res2 = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_position_triplet",
                version="1.1",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                account_c_pubkey=carol,
                new_position_base_a=1,
                new_position_base_b=-2,
                new_position_base_c=1,
            )
        ],
    )
    assert not res2.ok
    assert res2.error == "clearinghouse_3p requires at least one flat position"


def test_settle_epoch_3p_can_transfer_distressed_side_and_preserve_conservation() -> None:
    market_id = "perp:ch3p:transfer"
    quote_asset = "0x" + "55" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48
    carol = "cc" * 48

    funded = BalanceTable()
    funded.set(alice, quote_asset, 1000)
    funded.set(bob, quote_asset, 1000)
    funded.set(carol, quote_asset, 1000)
    state = DexState(balances=funded, pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "init_market_3p",
                version="1.1",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                account_c_pubkey=carol,
            )
        ],
    )

    # Epoch 1: initialize index price at 1.00.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="1.1", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", version="1.1", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="1.1")])

    # Fund all accounts (quote units; kernel stores quote-e8).
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="1.1", account_pubkey=alice, amount=100)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="1.1", account_pubkey=bob, amount=100)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=carol,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="1.1", account_pubkey=carol, amount=200)],
    )

    # Open a matched AB position pair (C idle).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_position_triplet",
                version="1.1",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                account_c_pubkey=carol,
                new_position_base_a=1000,
                new_position_base_b=-1000,
                new_position_base_c=0,
            )
        ],
    )

    # Epoch 2: +5% move triggers maintenance breach for the short; its position is transferred to idle C.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="1.1", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", version="1.1", price_e8=105_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="1.1")])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert isinstance(m, PerpClearinghouse3pTransferMarketState)

    assert int(m.state["position_base_a"]) == 1000
    assert int(m.state["position_base_b"]) == 0
    assert int(m.state["position_base_c"]) == -1000
    assert int(m.state["collateral_e8_a"]) == 15_000_000_000
    assert int(m.state["collateral_e8_b"]) == 4_475_000_000
    assert int(m.state["collateral_e8_c"]) == 20_000_000_000
    assert int(m.state["fee_pool_e8"]) == 525_000_000
    assert (
        int(m.state["collateral_e8_a"])
        + int(m.state["collateral_e8_b"])
        + int(m.state["collateral_e8_c"])
        + int(m.state["fee_pool_e8"])
        == int(m.state["net_deposited_e8"])
    )
