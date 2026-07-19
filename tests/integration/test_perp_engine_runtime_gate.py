from __future__ import annotations

from dataclasses import replace

from src.core.dex import DexState
from src.core.perps import PerpMarketState
from src.state.balances import BalanceTable
from src.state.lp import LPTable


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

    cfg = PerpEngineConfig(operator_pubkey=operator_pubkey, allow_isolated_markets=True)
    return apply_perp_ops(config=cfg, state=state, operations={"5": ops}, tx_sender_pubkey=tx_sender_pubkey, block_timestamp=0)


def _seed_initial_oracle_snapshot_for_test(state: DexState, ops: list[dict[str, object]]) -> DexState:
    """Model the external oracle snapshot required before first isolated settlement."""
    if len(ops) != 1 or ops[0].get("action") != "publish_clearing_price":
        return state
    market_id = ops[0].get("market_id")
    if not isinstance(market_id, str) or state.perps is None or market_id not in state.perps.markets:
        return state
    market = state.perps.markets[market_id]
    if not isinstance(market, PerpMarketState):
        return state
    global_state = dict(market.global_state)
    if bool(global_state.get("oracle_seen", False)) and int(global_state.get("index_price_e8", 0)) > 0:
        return state
    global_state["oracle_seen"] = True
    global_state["oracle_last_update_epoch"] = max(0, int(global_state.get("now_epoch", 0)) - 1)
    global_state["index_price_e8"] = int(ops[0].get("price_e8", 0))
    markets = dict(state.perps.markets)
    markets[market_id] = replace(market, global_state=global_state)
    return replace(state, perps=replace(state.perps, markets=markets))


def _apply(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], operator_pubkey: str) -> DexState:
    res = _apply_result(state=state, tx_sender_pubkey=tx_sender_pubkey, operator_pubkey=operator_pubkey, ops=ops)
    assert res.ok is True, res.error
    assert res.state is not None
    return _seed_initial_oracle_snapshot_for_test(res.state, ops)


def test_deposit_collateral_unknown_fields_precede_sender_binding() -> None:
    market_id = "perp:runtime-deposit"
    quote_asset = "0x" + "44" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", account_pubkey=alice, amount=1, extra=1)],
    )

    assert res.ok is False
    assert res.error == "deposit_collateral has unknown fields"



def test_set_position_sender_binding_error_preserved() -> None:
    market_id = "perp:runtime-position"
    quote_asset = "0x" + "45" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    res = _apply_result(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=1)],
    )

    assert res.ok is False
    assert res.error == "account_pubkey must match tx sender"
