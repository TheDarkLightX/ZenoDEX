from __future__ import annotations

from dataclasses import replace

from src.core.dex import DexState
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
                version="0.2",
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
                version="0.2",
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
                version="0.2",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
            )
        ],
    )

    # Establish oracle/index so set_position guards can run.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="0.2", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="0.2", price_e8=100_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="0.2")])

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_position_pair",
                version="0.2",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                new_position_base_a=1,
                new_position_base_b=0,
            )
        ],
    )
    assert not res.ok
    assert res.error == "clearinghouse_2p requires net position == 0"


def test_settle_epoch_2p_uses_dust_allocator_to_avoid_rounding_leak() -> None:
    market_id = "perp:ch2p:dust"
    quote_asset = "0x" + "55" * 32
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
                version="0.2",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
            )
        ],
    )

    # Epoch 1: initialize index price at 1.00.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="0.2", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="0.2", price_e8=100_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="0.2")])

    # Open a tiny matched pair position (net-zero).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_position_pair",
                version="0.2",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                new_position_base_a=1,
                new_position_base_b=-1,
            )
        ],
    )

    # Epoch 2: a +1 tick move in price_e8 creates xs=[+1, -1] at settlement.
    # Naive floor-div on signed products would produce [0, -1] and violate conservation;
    # the clearinghouse uses a deterministic dust allocator so the step remains safe.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="0.2", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="0.2", price_e8=100_000_001)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="0.2")])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert set(m.accounts.keys()) == {alice, bob}
    assert m.accounts[alice].collateral_quote == 0
    assert m.accounts[bob].collateral_quote == 0


def test_settle_epoch_2p_pair_liquidation_closes_both_positions() -> None:
    market_id = "perp:ch2p:liq"
    quote_asset = "0x" + "66" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # Seed balances (collateral deposits draw from balances).
    funded = BalanceTable()
    funded.set(alice, quote_asset, 1_000_000_000)
    funded.set(bob, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "init_market_2p",
                version="0.2",
                quote_asset=quote_asset,
                account_a_pubkey=alice,
                account_b_pubkey=bob,
            )
        ],
    )

    # Epoch 1: establish index price.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="0.2", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="0.2", price_e8=100_000_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="0.2")])

    # Deposit collateral for both sides (user-authenticated).
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="0.2", account_pubkey=alice, amount=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", version="0.2", account_pubkey=bob, amount=100_000_000)],
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
                version="0.2",
                account_a_pubkey=alice,
                account_b_pubkey=bob,
                new_position_base_a=1_000_000,
                new_position_base_b=-1_000_000,
            )
        ],
    )

    # Epoch 2: a -5% move makes Alice (long) under maintenance; pair liquidation closes both positions.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", version="0.2", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", version="0.2", price_e8=95_000_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch", version="0.2")])

    assert state.perps is not None
    m = state.perps.markets[market_id]
    assert int(m.global_state["fee_pool_quote"]) == 4_750_000
    assert int(m.global_state["fee_income"]) == 4_750_000
    assert int(m.global_state["insurance_balance"]) == 4_750_000

    acct_alice = m.accounts[alice]
    acct_bob = m.accounts[bob]

    assert acct_alice.position_base == 0
    assert acct_alice.entry_price_e8 == 0
    assert acct_alice.collateral_quote == 45_250_000

    assert acct_bob.position_base == 0
    assert acct_bob.entry_price_e8 == 0
    assert acct_bob.collateral_quote == 150_000_000

