from __future__ import annotations

from dataclasses import replace

from src.core.dex import DexState
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
    if not hasattr(market, "global_state"):
        return state
    global_state = market.global_state
    if bool(global_state.get("oracle_seen", False)) and int(global_state.get("index_price_e8", 0)) > 0:
        return state
    global_state["oracle_seen"] = True
    global_state["oracle_last_update_epoch"] = max(0, int(global_state.get("now_epoch", 0)) - 1)
    global_state["index_price_e8"] = int(ops[0].get("price_e8", 0))
    return state


def _apply(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], operator_pubkey: str) -> DexState:
    res = _apply_result(state=state, tx_sender_pubkey=tx_sender_pubkey, operator_pubkey=operator_pubkey, ops=ops)
    assert res.ok is True, res.error
    assert res.state is not None
    return _seed_initial_oracle_snapshot_for_test(res.state, ops)


def test_publish_clearing_price_rejects_unsafe_oracle_reward_posture() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-reward-unsafe"
    quote_asset = "0x" + "88" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        oracle_pubkey=operator,
        allow_isolated_markets=True,
        oracle_spot_fee_bps=20,
        oracle_spot_reward_bps=20,
        oracle_spot_reward_safety_margin_bps=1,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error is not None and "oracle reward posture unsafe" in res.error


def test_publish_clearing_price_accepts_safe_oracle_reward_posture() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-reward-safe"
    quote_asset = "0x" + "89" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        oracle_pubkey=operator,
        allow_isolated_markets=True,
        oracle_spot_fee_bps=20,
        oracle_spot_reward_bps=19,
        oracle_spot_reward_safety_margin_bps=1,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is True, res.error


def test_operator_pubkey_accepts_0X_prefix() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:op-0X"
    quote_asset = "0x" + "ab" * 32
    operator = "aa" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    cfg = PerpEngineConfig(operator_pubkey="0X" + operator, allow_isolated_markets=True)
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "init_market", quote_asset=quote_asset)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is True, res.error


def test_settle_epoch_oracle_adapter_bridge_required_when_configured() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-adapter-required"
    quote_asset = "0x" + "91" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_adapter_for_isolated_settle_epoch=True,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "settle_epoch")]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "settle_epoch requires oracle_adapter_bridge"


def test_publish_clearing_price_rejects_zero_oracle_fee_friction() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-reward-zero-fee"
    quote_asset = "0x" + "8a" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        oracle_spot_fee_bps=0,
        oracle_spot_reward_bps=0,
        oracle_spot_reward_safety_margin_bps=1,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "oracle reward posture unsafe: require oracle_spot_fee_bps > 0"


def test_publish_clearing_price_rejects_zero_oracle_reward_safety_margin() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-reward-zero-margin"
    quote_asset = "0x" + "8b" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        oracle_spot_fee_bps=10,
        oracle_spot_reward_bps=0,
        oracle_spot_reward_safety_margin_bps=0,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "oracle reward posture unsafe: require oracle_spot_reward_safety_margin_bps > 0"


def test_publish_clearing_price_rejects_reward_subsidy_without_oracle_signer() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-reward-missing-signer"
    quote_asset = "0x" + "8d" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        oracle_spot_fee_bps=20,
        oracle_spot_reward_bps=1,
        oracle_spot_reward_safety_margin_bps=1,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "oracle reward posture unsafe: require oracle_pubkey when oracle_spot_reward_bps > 0"


def test_set_market_params_enforces_collectible_penalty_floor() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:bounty-floor"
    quote_asset = "0x" + "8c" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    # settle epoch so set_market_params is allowed.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        min_collectible_liquidation_penalty_quote=5_000,
    )
    # With 50 bps penalty, this policy requires:
    # min_notional_for_bounty >= ceil(5000 * 10000 / 50) = 1,000,000
    res_bad = apply_perp_ops(
        config=cfg,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "set_market_params",
                    params={"liquidation_penalty_bps": 50, "min_notional_for_bounty": 999_999},
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res_bad.ok is False
    assert res_bad.error is not None and "ceil(5000 * 10000 / liquidation_penalty_bps)" in res_bad.error

    res_ok = apply_perp_ops(
        config=cfg,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "set_market_params",
                    params={"liquidation_penalty_bps": 50, "min_notional_for_bounty": 1_000_000},
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res_ok.ok is True, res_ok.error


def test_set_market_params_reports_funding_rate_clamp() -> None:
    market_id = "perp:funding-clamp-effect"
    quote_asset = "0x" + "8d" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    assert state.perps is not None
    market = state.perps.markets[market_id]
    stale_global = dict(market.global_state)
    stale_global["funding_rate_bps"] = 100
    stale_market = type(market)(
        quote_asset=market.quote_asset,
        global_state=stale_global,
        accounts=dict(market.accounts),
    )
    stale_state = replace(
        state,
        perps=type(state.perps)(version=state.perps.version, markets={market_id: stale_market}),
    )

    res = _apply_result(
        state=stale_state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"funding_cap_bps": 50})],
    )
    assert res.ok is True, res.error
    assert res.effects is not None
    effect = res.effects[0]
    assert effect["funding_rate_clamped"] is True
    assert effect["funding_rate_bps_before"] == 100
    assert effect["funding_rate_bps_after"] == 50

    assert res.state is not None and res.state.perps is not None
    next_market = res.state.perps.markets[market_id]
    assert int(next_market.global_state["funding_rate_bps"]) == 50


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

    # Epoch 2 (OPEN): deposit collateral and open positions, then publish+settle.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    # Fund both traders so they can deposit collateral.
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000)
    funded.set(bob, quote_asset, 1_000_000)
    state = replace(state, balances=funded)

    # Open positions during OPEN phase.
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

    # Settle epoch 2 at same price to complete the cycle.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Epoch 3: publish a new (different) clearing price (pre-settle state).
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


def test_set_position_rejects_malformed_oracle_snapshot_zero_index() -> None:
    market_id = "perp:malformed-oracle"
    quote_asset = "0x" + "77" * 32
    operator = "00" * 48
    alice = "aa" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    # Establish oracle, then return to OPEN where set_position is allowed.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000)
    state = replace(state, balances=funded)
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "deposit_collateral", account_pubkey=alice, amount=1000)],
    )

    assert state.perps is not None
    market = state.perps.markets[market_id]
    # Simulate an in-memory corrupted oracle snapshot (invalid reachable state).
    # Snapshot parsing should fail-closed on this, but runtime code should still
    # reject actions when fed malformed state.
    market.global_state["oracle_seen"] = True
    market.global_state["oracle_last_update_epoch"] = int(market.global_state.get("now_epoch", 0))
    market.global_state["index_price_e8"] = 0

    res = _apply_result(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=10)],
    )
    assert res.ok is False
    assert res.error == "guard"


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
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Epoch 2 (OPEN): deposit collateral and open positions.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    # Fund both traders so they can deposit collateral.
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000_000)
    funded.set(bob, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    # Open positions during OPEN phase.
    # Use a configuration where Alice becomes under-maintenance after a 5% price drop
    # but still has positive collateral, so a nonzero liquidation penalty is collected.
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=1_000_000),
        ],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=bob, amount=100_000_000),
            _op(market_id, "set_position", account_pubkey=bob, new_position_base=-1_000_000),
        ],
    )

    # Settle epoch 2 at same price to complete the cycle.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Epoch 3: publish a new clearing price (pre-settle state).
    pre = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    pre = _apply(state=pre, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=95_000_000_000)])

    # Construct an equivalent state but with reversed account insertion order.
    assert pre.perps is not None
    market = pre.perps.markets[market_id]
    reversed_accounts = dict(reversed(list(market.accounts.items())))
    market_rev = type(market)(quote_asset=market.quote_asset, global_state=dict(market.global_state), accounts=reversed_accounts)
    perps_rev = type(pre.perps)(version=pre.perps.version, markets={market_id: market_rev})
    pre_rev = replace(pre, perps=perps_rev)

    cap_accounts = dict(market.accounts)
    cap_accounts[alice] = replace(cap_accounts[alice], collateral_quote=52_000_000)
    cap_market = type(market)(quote_asset=market.quote_asset, global_state=dict(market.global_state), accounts=cap_accounts)
    cap_pre = replace(pre, perps=type(pre.perps)(version=pre.perps.version, markets={market_id: cap_market}))
    cap_res = _apply_result(
        state=cap_pre,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    assert cap_res.ok is True, cap_res.error
    assert cap_res.effects is not None
    cap_effect = cap_res.effects[0]
    assert cap_effect["liquidation_penalty_raw_quote"] == 4_750_000
    assert cap_effect["liquidation_penalty_collected_quote"] == 2_000_000
    assert cap_effect["liquidation_penalty_shortfall_quote"] == 2_750_000
    assert cap_effect["liquidation_penalty_cap_bound_count"] == 1

    post_res = _apply_result(
        state=pre,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    assert post_res.ok is True, post_res.error
    assert post_res.state is not None
    assert post_res.effects is not None
    effect = post_res.effects[0]
    assert effect["liquidation_penalty_raw_quote"] == 4_750_000
    assert effect["liquidation_penalty_collected_quote"] == 4_750_000
    assert effect["liquidation_penalty_shortfall_quote"] == 0
    assert effect["liquidation_penalty_cap_bound_count"] == 0
    post = post_res.state
    post_rev = _apply(state=pre_rev, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    assert post.perps == post_rev.perps

    assert post.perps is not None
    m = post.perps.markets[market_id]
    assert int(m.global_state["fee_pool_quote"]) == 4_750_000
    assert int(m.global_state["fee_income"]) == 4_750_000
    assert int(m.global_state["insurance_balance"]) == 4_750_000

    acct_alice = m.accounts[alice]
    acct_bob = m.accounts[bob]

    # Alice: liquidated (position forced to 0) with penalty collected into fee pool.
    assert acct_alice.position_base == 0
    assert acct_alice.entry_price_e8 == 0
    assert acct_alice.collateral_quote == 45_250_000

    # Bob: remains open and gains PnL from the price move.
    assert acct_bob.position_base == -1_000_000
    assert acct_bob.entry_price_e8 == 95_000_000_000
    assert acct_bob.collateral_quote == 150_000_000


def test_settle_epoch_clears_liquidated_flag_for_flat_accounts() -> None:
    market_id = "perp:liq-flag"
    quote_asset = "0x" + "55" * 32
    operator = "00" * 48
    alice = "aa" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=1_000_000),
        ],
    )

    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Epoch 3: force liquidation.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=95_000_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    assert state.perps is not None
    market = state.perps.markets[market_id]
    acct = market.accounts[alice]
    assert acct.position_base == 0
    assert acct.liquidated_this_step is True

    # advance_epoch is global-only, so the per-account liquidation marker persists.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert market.accounts[alice].liquidated_this_step is True

    # Next settlement on a flat account must clear the marker.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=95_000_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert market.accounts[alice].position_base == 0
    assert market.accounts[alice].liquidated_this_step is False


def test_apply_perp_ops_fail_closed_on_invalid_field_type() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:bad-field-type"
    quote_asset = "0x" + "aa" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )

    cfg = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "advance_epoch", delta="1")]},  # type: ignore[arg-type]
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "delta must be an int"


def test_apply_perp_ops_rejects_pathological_int_widths() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:wide-int"
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    cfg = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True, max_int_bits=128)
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": [_op(market_id, "advance_epoch", delta=(1 << 200))]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error is not None and "int wider than 128 bits" in res.error


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

    # Epoch 2 (OPEN): deposit collateral and open positions.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    # Fund both traders so they can deposit collateral.
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000)
    funded.set(bob, quote_asset, 1_000_000)
    state = replace(state, balances=funded)

    # Open positions during OPEN phase while breaker is inactive.
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

    # Settle epoch 2 at same price (positions survive unchanged).
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Epoch 3: publish a wildly out-of-bounds move (settle clamps + triggers breaker).
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=200_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Epoch 4 (OPEN + breaker_active): reduce-only operations allowed.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert market.global_state["breaker_active"] is True
    # Default max_oracle_move_bps=500 => clamp to +5% from 1.00 to 1.05.
    assert market.global_state["index_price_e8"] == 105_000_000
    assert market.global_state["breaker_last_trigger_epoch"] == 3

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


def test_publish_clearing_price_rejects_zero_price() -> None:
    market_id = "perp:zero-price"
    quote_asset = "0x" + "56" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=0)],
    )
    assert res.ok is False
    assert res.error == "publish_clearing_price requires price_e8 > 0"


def test_publish_clearing_price_rejects_internal_batch_mark_source() -> None:
    from src.core.perp_apply_funding_auto_gate import MARK_PRICE_SOURCE_INTERNAL_BATCH_CLEARING

    market_id = "perp:unsafe-mark-source"
    quote_asset = "0x" + "57" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "publish_clearing_price",
                price_e8=100_000_000,
                mark_price_source_kind=MARK_PRICE_SOURCE_INTERNAL_BATCH_CLEARING,
            )
        ],
    )
    assert res.ok is False
    assert res.error == "publish_clearing_price requires derivatives-safe mark_price_source_kind"


def test_apply_funding_auto_applies_to_all_open_positions() -> None:
    market_id = "perp:funding"
    quote_asset = "0x" + "66" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())

    # Init market and establish the initial index price at 1.00.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Epoch 2 (OPEN): deposit collateral and open positions.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    # Fund balances so traders can post collateral.
    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000_000)
    funded.set(bob, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    # Open equal and opposite positions during OPEN phase (notional = 1_000_000 quote at index=1.00).
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=200_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=1_000_000),
        ],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=bob, amount=200_000),
            _op(market_id, "set_position", account_pubkey=bob, new_position_base=-1_000_000),
        ],
    )

    # Settle epoch 2 at same price to complete the cycle.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Epoch 3: publish a 2% higher clearing price, then apply funding.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "apply_funding_auto")])

    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert market.global_state["funding_rate_bps"] == 100  # capped (2% basis => 200 bps, cap=100).

    acct_alice = market.accounts[alice]
    acct_bob = market.accounts[bob]

    assert acct_alice.funding_last_applied_epoch == 3
    assert acct_bob.funding_last_applied_epoch == 3

    # Funding magnitude: notional=1_000_000, rate=100 bps => 10_000.
    assert acct_alice.collateral_quote == 200_000 - 10_000
    assert acct_bob.collateral_quote == 200_000 + 10_000
    assert acct_alice.funding_paid_cumulative == 10_000
    assert acct_bob.funding_paid_cumulative == -10_000
    assert int(market.global_state["fee_pool_quote"]) == 0


def test_apply_funding_auto_allows_empty_open_interest() -> None:
    market_id = "perp:funding-empty"
    quote_asset = "0x" + "68" * 32
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
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # No user positions are ever opened. Funding auto should still be callable for
    # the epoch and update the global funding rate deterministically.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)])
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "apply_funding_auto")],
    )
    assert res.ok is True, res.error
    assert res.state is not None
    assert res.effects is not None

    effect = res.effects[0]
    assert effect.get("accounts_applied") == 0
    assert effect.get("funding_rate_bps") == 100

    assert res.state.perps is not None
    market = res.state.perps.markets[market_id]
    assert market.accounts == {}
    assert int(market.global_state["funding_rate_bps"]) == 100
    assert int(market.global_state["fee_pool_quote"]) == 0


def test_apply_funding_auto_rejects_stale_oracle() -> None:
    market_id = "perp:funding-stale"
    quote_asset = "0x" + "69" * 32
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
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Tight staleness budget so a skipped epoch window fail-closes funding.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"max_oracle_staleness_epochs": 1})],
    )

    # Jump several epochs ahead without oracle refresh, then publish clearing for current epoch.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=3)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)])

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "apply_funding_auto")],
    )
    assert res.ok is False
    assert res.error == "cannot apply funding: oracle is stale"


def test_apply_funding_auto_rejects_malformed_control_fields() -> None:
    from src.core.perps import PerpMarketState, PerpsState

    market_id = "perp:funding-malformed-controls"
    quote_asset = "0x" + "6a" * 32
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
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)])

    assert state.perps is not None
    market_any = state.perps.markets[market_id]
    assert isinstance(market_any, PerpMarketState)

    def _state_with_global_override(key: str, value: int) -> DexState:
        global_state = dict(market_any.global_state)
        global_state[key] = value
        perps = PerpsState(
            version=int(state.perps.version),
            markets={
                **state.perps.markets,
                market_id: PerpMarketState(
                    quote_asset=market_any.quote_asset,
                    global_state=global_state,
                    accounts=dict(market_any.accounts),
                ),
            },
        )
        return replace(state, perps=perps)

    malformed_cases = (
        ("max_oracle_staleness_epochs", 0, "cannot apply funding: invalid max_oracle_staleness_epochs"),
        ("funding_cap_bps", 0, "cannot apply funding: invalid funding_cap_bps"),
        ("clearing_price_e8", 0, "cannot apply funding: clearing_price_e8 must be positive"),
        ("max_oracle_move_bps", -1, "cannot apply funding: invalid max_oracle_move_bps"),
    )
    for field, value, expected_error in malformed_cases:
        res = _apply_result(
            state=_state_with_global_override(field, value),
            tx_sender_pubkey=operator,
            operator_pubkey=operator,
            ops=[_op(market_id, "apply_funding_auto")],
        )
        assert res.ok is False
        assert res.error == expected_error


def test_apply_funding_auto_routes_positive_net_flow_to_fee_pool() -> None:
    market_id = "perp:funding-unbalanced"
    quote_asset = "0x" + "67" * 32
    operator = "00" * 48
    alice = "aa" * 48

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

    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=200_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=1_000_000),
        ],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)])

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "apply_funding_auto")],
    )
    assert res.ok is True, res.error
    assert res.state is not None
    assert res.effects is not None
    assert res.effects[0]["projected_net_funding_quote"] == 10_000
    assert res.effects[0]["fee_pool_delta_quote"] == 10_000

    assert res.state.perps is not None
    market = res.state.perps.markets[market_id]
    acct_alice = market.accounts[alice]
    assert acct_alice.collateral_quote == 190_000
    assert acct_alice.funding_paid_cumulative == 10_000
    assert int(market.global_state["fee_pool_quote"]) == 10_000
    assert int(market.global_state["fee_income"]) == 10_000
    assert int(market.global_state["insurance_balance"]) == 10_000


def test_apply_funding_auto_rejects_negative_fee_pool_after() -> None:
    market_id = "perp:funding-negative-fee-pool"
    quote_asset = "0x" + "6b" * 32
    operator = "00" * 48
    alice = "aa" * 48

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

    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=200_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=-1_000_000),
        ],
    )
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)])

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "apply_funding_auto")],
    )
    assert res.ok is False
    assert res.error is not None
    assert "funding sink bounds" in res.error

    from src.core.perps import PerpMarketState, PerpsState

    assert state.perps is not None
    market = state.perps.markets[market_id]
    funded_global = dict(market.global_state)
    funded_global["fee_pool_quote"] = 10_000
    funded_global["fee_income"] = 10_000
    funded_global["insurance_balance"] = 10_000
    funded_state = replace(
        state,
        perps=PerpsState(
            version=int(state.perps.version),
            markets={
                **state.perps.markets,
                market_id: PerpMarketState(
                    quote_asset=market.quote_asset,
                    global_state=funded_global,
                    accounts=dict(market.accounts),
                ),
            },
        ),
    )

    ok_res = _apply_result(
        state=funded_state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "apply_funding_auto")],
    )
    assert ok_res.ok is True, ok_res.error
    assert ok_res.state is not None
    assert ok_res.effects is not None
    assert ok_res.effects[0]["projected_net_funding_quote"] == -10_000
    assert ok_res.effects[0]["fee_pool_delta_quote"] == -10_000

    assert ok_res.state.perps is not None
    ok_market = ok_res.state.perps.markets[market_id]
    acct_alice = ok_market.accounts[alice]
    assert acct_alice.collateral_quote == 210_000
    assert acct_alice.funding_paid_cumulative == -10_000
    assert int(ok_market.global_state["fee_pool_quote"]) == 0
    assert int(ok_market.global_state["fee_income"]) == 0
    assert int(ok_market.global_state["insurance_balance"]) == 0


def test_set_market_params_mid_epoch_guard_and_margin_safety() -> None:
    market_id = "perp:params"
    quote_asset = "0x" + "77" * 32
    operator = "00" * 48
    alice = "aa" * 48

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

    # Epoch 2 (OPEN): deposit collateral and open positions.
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=1_000_000),
        ],
    )

    # Settle epoch 2 at same price so set_market_params can be tested (requires settled epoch).
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])

    # Operator-only.
    res_nonop = _apply_result(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"initial_margin_bps": 1200})],
    )
    assert res_nonop.ok is False
    assert res_nonop.error == "operator only"

    # Invalid: raising maintenance margin would put the account below maintenance.
    res_bad = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"initial_margin_bps": 3000, "maintenance_margin_bps": 2000})],
    )
    assert res_bad.ok is False
    assert res_bad.error is not None and "under maintenance margin" in res_bad.error

    # With open positions, decreasing the bounty threshold is rejected fail-closed
    # before evaluating the collectible-floor inequality.
    res_bounty_floor = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"liquidation_penalty_bps": 50, "min_notional_for_bounty": 199})],
    )
    assert res_bounty_floor.ok is False
    assert res_bounty_floor.error is not None and "cannot decrease min_notional_for_bounty while positions are open" in res_bounty_floor.error

    # Scientist hardening: liquidation penalty must stay positive.
    res_zero_penalty = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"liquidation_penalty_bps": 0})],
    )
    assert res_zero_penalty.ok is False
    assert res_zero_penalty.error is not None and "liquidation_penalty_bps > 0" in res_zero_penalty.error

    # Scientist hardening: depeg buffer must remain positive (fail-closed against disabling buffer).
    res_zero_depeg = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"depeg_buffer_bps": 0})],
    )
    assert res_zero_depeg.ok is False
    assert res_zero_depeg.error is not None and "depeg_buffer_bps > 0" in res_zero_depeg.error

    # Funded-liquidation hardening: this move bound still satisfies the older
    # max_oracle_move_bps <= effective maintenance guard, but leaves too little
    # post-move headroom to fund the advertised liquidation penalty.
    res_unfunded_liquidation = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"max_oracle_move_bps": 548})],
    )
    assert res_unfunded_liquidation.ok is False
    assert res_unfunded_liquidation.error is not None
    assert "require funded liquidation" in res_unfunded_liquidation.error

    # Scientist hardening: while positions are open, do not allow increasing liquidation penalty.
    res_penalty_up = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"liquidation_penalty_bps": 60})],
    )
    assert res_penalty_up.ok is False
    assert res_penalty_up.error is not None and "cannot increase liquidation_penalty_bps while positions are open" in res_penalty_up.error

    # Scientist hardening: while positions are open, do not allow lowering bounty threshold.
    res_bounty_down = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"min_notional_for_bounty": 50_000_000})],
    )
    assert res_bounty_down.ok is False
    assert res_bounty_down.error is not None and "cannot decrease min_notional_for_bounty while positions are open" in res_bounty_down.error

    # Hardening-direction updates are allowed while positions are open.
    res_harden = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_market_params",
                params={"liquidation_penalty_bps": 40, "min_notional_for_bounty": 120_000_000},
            )
        ],
    )
    assert res_harden.ok is True, res_harden.error

    # Mid-epoch guard: params can only be updated when the current epoch is settled.
    mid = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    res_mid = _apply_result(
        state=mid,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"initial_margin_bps": 1200})],
    )
    assert res_mid.ok is False
    assert res_mid.error == "cannot update market params mid-epoch"
