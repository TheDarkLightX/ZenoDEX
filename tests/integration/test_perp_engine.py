from __future__ import annotations

from dataclasses import replace

import pytest

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


def _apply_result(
    *, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], operator_pubkey: str
):
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    cfg = PerpEngineConfig(operator_pubkey=operator_pubkey, allow_isolated_markets=True)
    return apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=0,
    )


def _apply(
    *, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], operator_pubkey: str
) -> DexState:
    res = _apply_result(
        state=state, tx_sender_pubkey=tx_sender_pubkey, operator_pubkey=operator_pubkey, ops=ops
    )
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def _bootstrap(
    *,
    state: DexState,
    market_id: str,
    price_e8: int,
    operator_pubkey: str,
) -> DexState:
    return _apply(
        state=state,
        tx_sender_pubkey=operator_pubkey,
        operator_pubkey=operator_pubkey,
        ops=[_op(market_id, "bootstrap_oracle", price_e8=price_e8)],
    )


def test_bootstrap_oracle_is_operator_only_one_time_and_lifecycle_complete() -> None:
    market_id = "perp:bootstrap-lifecycle"
    quote_asset = "0x" + "81" * 32
    operator = "00" * 48
    alice = "aa" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )

    unauthorized = _apply_result(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "bootstrap_oracle", price_e8=100_000_000)],
    )
    assert unauthorized.ok is False
    assert unauthorized.state is None
    assert unauthorized.effects is None
    assert unauthorized.error == "operator only"

    bootstrapped = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "bootstrap_oracle", price_e8=100_000_000)],
    )
    assert bootstrapped.ok is True, bootstrapped.error
    assert bootstrapped.state is not None
    assert bootstrapped.effects is not None
    assert bootstrapped.state.perps is not None
    market = bootstrapped.state.perps.markets[market_id]
    assert market.global_state["oracle_seen"] is True
    assert market.global_state["oracle_last_update_epoch"] == 0
    assert market.global_state["index_price_e8"] == 100_000_000

    replay = _apply_result(
        state=bootstrapped.state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "bootstrap_oracle", price_e8=100_000_000)],
    )
    assert replay.ok is False
    assert replay.state is None
    assert replay.effects is None
    assert replay.error == "guard"

    advanced = _apply(
        state=bootstrapped.state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    published = _apply(
        state=advanced,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    settled = _apply(
        state=published,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    assert settled.perps is not None
    settled_market = settled.perps.markets[market_id]
    assert settled_market.global_state["epoch_phase"] == 2
    assert settled_market.global_state["index_price_e8"] == 100_000_000


def test_isolated_advance_epoch_rejects_delta_above_one() -> None:
    market_id = "perp:advance-epoch-bva"
    quote_asset = "0x" + "83" * 32
    operator = "00" * 48

    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )

    result = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=2)],
    )

    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "advance_epoch delta must be 1 for isolated markets"


def test_bootstrap_oracle_price_bva_and_pre_value_boundary() -> None:
    from src.core.domain_limits import PERP_PRICE_E8_MAX

    operator = "00" * 48
    quote_asset = "0x" + "82" * 32
    cases = (
        ("zero", 0, False, "bootstrap_oracle requires price_e8 > 0"),
        ("one", 1, True, None),
        ("max", PERP_PRICE_E8_MAX, True, None),
        ("over-max", PERP_PRICE_E8_MAX + 1, False, "param_domain:price_e8"),
    )

    for suffix, price_e8, expected_ok, expected_error in cases:
        market_id = f"perp:bootstrap-bva-{suffix}"
        initial = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
        initialized = _apply(
            state=initial,
            tx_sender_pubkey=operator,
            operator_pubkey=operator,
            ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
        )
        result = _apply_result(
            state=initialized,
            tx_sender_pubkey=operator,
            operator_pubkey=operator,
            ops=[_op(market_id, "bootstrap_oracle", price_e8=price_e8)],
        )
        assert result.ok is expected_ok
        if expected_ok:
            assert result.state is not None
            assert result.effects is not None
            assert result.state.perps is not None
            assert result.state.perps.markets[market_id].global_state["index_price_e8"] == price_e8
        else:
            assert result.state is None
            assert result.effects is None
            assert result.error == expected_error

    post_value_market_id = "perp:bootstrap-after-value"
    alice = "aa" * 48
    initialized = _apply(
        state=DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()),
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(post_value_market_id, "init_market", quote_asset=quote_asset)],
    )
    funded = BalanceTable()
    funded.set(alice, quote_asset, 1)
    funded_state = replace(initialized, balances=funded)
    with_collateral = _apply(
        state=funded_state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[
            _op(
                post_value_market_id,
                "deposit_collateral",
                account_pubkey=alice,
                amount=1,
            )
        ],
    )
    after_value = _apply_result(
        state=with_collateral,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                post_value_market_id,
                "bootstrap_oracle",
                price_e8=100_000_000,
            )
        ],
    )
    assert after_value.ok is False
    assert after_value.state is None
    assert after_value.effects is None
    assert after_value.error == "bootstrap_oracle requires an empty market"


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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    assert (
        res.error
        == "oracle reward posture unsafe: require oracle_spot_reward_safety_margin_bps > 0"
    )


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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    assert (
        res.error
        == "oracle reward posture unsafe: require oracle_pubkey when oracle_spot_reward_bps > 0"
    )


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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    # settle epoch so set_market_params is allowed.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

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
    assert (
        res_bad.error is not None
        and "ceil(5000 * 10000 / liquidation_penalty_bps)" in res_bad.error
    )

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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )

    # Epoch 1: establish an oracle/index price (no accounts yet).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 2 (OPEN): deposit collateral and open positions, then publish+settle.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=1000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100),
        ],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=bob, amount=1000),
            _op(market_id, "set_position", account_pubkey=bob, new_position_base=-100),
        ],
    )

    # Settle epoch 2 at same price to complete the cycle.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 3: publish a new (different) clearing price (pre-settle state).
    pre = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
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
    market_rev = type(market)(
        quote_asset=market.quote_asset,
        global_state=dict(market.global_state),
        accounts=reversed_accounts,
    )
    perps_rev = type(pre.perps)(version=pre.perps.version, markets={market_id: market_rev})
    pre_rev = replace(pre, perps=perps_rev)

    # Settle epoch from both pre-states and compare.
    post = _apply(
        state=pre,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    post_rev = _apply(
        state=pre_rev,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    # Establish oracle, then return to OPEN where set_position is allowed.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    malformed_global_state = dict(market.global_state)
    malformed_global_state["oracle_seen"] = True
    malformed_global_state["oracle_last_update_epoch"] = int(
        malformed_global_state.get("now_epoch", 0)
    )
    malformed_global_state["index_price_e8"] = 0

    # Committed mappings reject mutation, and the typed market constructor
    # rejects the malformed replacement before it can reach runtime dispatch.
    with pytest.raises(TypeError, match="immutable"):
        market.global_state["index_price_e8"] = 0
    with pytest.raises(
        ValueError,
        match="index_price_e8 must be positive when oracle_seen is true",
    ):
        replace(market, global_state=malformed_global_state)


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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000_000,
        operator_pubkey=operator,
    )

    # Epoch 1: establish an oracle/index price (no accounts yet).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 2 (OPEN): deposit collateral and open positions.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 3: publish a new clearing price (pre-settle state).
    pre = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    pre = _apply(
        state=pre,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=95_000_000_000)],
    )

    # Construct an equivalent state but with reversed account insertion order.
    assert pre.perps is not None
    market = pre.perps.markets[market_id]
    reversed_accounts = dict(reversed(list(market.accounts.items())))
    market_rev = type(market)(
        quote_asset=market.quote_asset,
        global_state=dict(market.global_state),
        accounts=reversed_accounts,
    )
    perps_rev = type(pre.perps)(version=pre.perps.version, markets={market_id: market_rev})
    pre_rev = replace(pre, perps=perps_rev)

    cap_accounts = dict(market.accounts)
    cap_accounts[alice] = replace(cap_accounts[alice], collateral_quote=52_000_000)
    cap_market = type(market)(
        quote_asset=market.quote_asset,
        global_state=dict(market.global_state),
        accounts=cap_accounts,
    )
    cap_pre = replace(
        pre, perps=type(pre.perps)(version=pre.perps.version, markets={market_id: cap_market})
    )
    cap_res = _apply_result(
        state=cap_pre,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    assert cap_res.ok is True, cap_res.error
    assert cap_res.state is not None
    assert cap_res.effects is not None
    cap_effect = cap_res.effects[0]
    assert cap_effect["liquidation_penalty_raw_quote"] == 4_750_000
    assert cap_effect["liquidation_penalty_collected_quote"] == 2_000_000
    assert cap_effect["liquidation_penalty_shortfall_quote"] == 2_750_000
    assert cap_effect["liquidation_penalty_cap_bound_count"] == 1
    assert cap_res.state.perps is not None
    capped_alice = cap_res.state.perps.markets[market_id].accounts[alice]
    assert capped_alice.position_base == 0
    assert capped_alice.collateral_quote == 0

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
    post_rev = _apply(
        state=pre_rev,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

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


def test_publish_rejects_if_exact_mounted_settlement_would_overflow() -> None:
    from src.core.perp_epoch import perp_epoch_isolated_default_fee_pool_max_quote
    from src.core.perps import (
        PERPS_STATE_VERSION,
        PerpAccountState,
        PerpMarketState,
        PerpsState,
    )
    from src.integration.perp_engine import (
        PerpEngineConfig,
        _kernel_initial_global_state,
        apply_perp_ops,
    )

    market_id = "perp:publish-settlement-overflow"
    quote_asset = "0x" + "83" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48
    index_price_e8 = 100_000_000_000
    max_fee_pool = int(perp_epoch_isolated_default_fee_pool_max_quote())
    pre_fee_pool = max_fee_pool - 5_000_000

    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": index_price_e8,
            "fee_pool_quote": pre_fee_pool,
            "fee_income": pre_fee_pool,
            "insurance_balance": pre_fee_pool,
            "min_notional_for_bounty": 0,
        }
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={
                market_id: PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=global_state,
                    accounts={
                        alice: PerpAccountState(
                            position_base=1_000_000,
                            entry_price_e8=index_price_e8,
                            collateral_quote=100_000_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        bob: PerpAccountState(
                            position_base=1_000_000,
                            entry_price_e8=index_price_e8,
                            collateral_quote=100_000_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                    },
                )
            },
        ),
    )

    result = apply_perp_ops(
        config=PerpEngineConfig(
            operator_pubkey=operator,
            allow_isolated_markets=True,
        ),
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "publish_clearing_price",
                    price_e8=95_000_000_000,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == (
        "publish_clearing_price has no mounted settlement path: "
        "fee/insurance overflow (post-settle)"
    )
    assert state.perps is not None
    unchanged = state.perps.markets[market_id]
    assert unchanged.global_state["epoch_phase"] == 0
    assert unchanged.global_state["clearing_price_seen"] is False
    assert unchanged.global_state["fee_pool_quote"] == pre_fee_pool


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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 3: force liquidation.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=95_000_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    assert state.perps is not None
    market = state.perps.markets[market_id]
    acct = market.accounts[alice]
    assert acct.position_base == 0
    assert acct.liquidated_this_step is True

    # advance_epoch is global-only, so the per-account liquidation marker persists.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert market.accounts[alice].liquidated_this_step is True

    # Next settlement on a flat account must clear the marker.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=95_000_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )

    # Epoch 1: establish an oracle/index price (no accounts yet).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 2 (OPEN): deposit collateral and open positions.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=1000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100),
        ],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=bob, amount=1000),
            _op(market_id, "set_position", account_pubkey=bob, new_position_base=-100),
        ],
    )

    # Settle epoch 2 at same price (positions survive unchanged).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 3: publish a wildly out-of-bounds move (settle clamps + triggers breaker).
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=200_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 4 (OPEN + breaker_active): reduce-only operations allowed.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=50)],
    )

    # Breaker posture: no sign flip unless closing to 0.
    res_flip = _apply_result(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=-50)],
    )
    assert res_flip.ok is False

    # Clear breaker fails while positions are open (engine-level fail-closed).
    res_clear_open = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "clear_breaker")],
    )
    assert res_clear_open.ok is False
    assert res_clear_open.error == "cannot clear breaker while positions are open"

    # Close out all positions.
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey=alice, new_position_base=0)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_position", account_pubkey=bob, new_position_base=0)],
    )

    # Clear breaker requires operator key.
    res_clear_nonop = _apply_result(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "clear_breaker")],
    )
    assert res_clear_nonop.ok is False
    assert res_clear_nonop.error == "operator only"

    # Operator can clear breaker once all accounts are flat.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "clear_breaker")],
    )
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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )

    # Once a clearing price is published, the operator must settle before advancing or re-publishing.
    res_adv = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    assert res_adv.ok is False
    assert res_adv.error == "cannot advance epoch before settling current epoch"

    res_pub = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=101_000_000)],
    )
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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 2 (OPEN): deposit collateral and open positions.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 3: publish a 2% higher clearing price, then apply funding.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "apply_funding_auto")],
    )

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

    # Funding applied after publication must preserve the mounted, composed
    # settlement path for every account in the market.
    settled = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    assert settled.ok is True, settled.error
    assert settled.state is not None
    assert settled.state.perps is not None
    settled_market = settled.state.perps.markets[market_id]
    assert int(settled_market.global_state["epoch_phase"]) == 2
    assert sum(account.collateral_quote for account in settled_market.accounts.values()) == 400_000


def test_apply_funding_auto_rejects_when_post_funding_settlement_would_be_impossible() -> None:
    from src.core.perp_epoch import perp_epoch_isolated_default_fee_pool_max_quote
    from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
    from src.integration.perp_engine import _kernel_initial_global_state

    market_id = "perp:funding-preserves-composed-settlement"
    quote_asset = "0x" + "84" * 32
    operator = "00" * 48
    max_fee = int(perp_epoch_isolated_default_fee_pool_max_quote())

    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": 100_000_000,
            "fee_pool_quote": max_fee - 120_000,
            "fee_income": max_fee - 120_000,
            "insurance_balance": max_fee - 120_000,
            "min_notional_for_bounty": 0,
        }
    )
    accounts = {
        f"long-{index:02d}": PerpAccountState(
            position_base=1_000_000,
            entry_price_e8=100_000_000,
            collateral_quote=70_000,
            funding_paid_cumulative=0,
            funding_last_applied_epoch=2,
            liquidated_this_step=False,
        )
        for index in range(13)
    }
    accounts["short"] = PerpAccountState(
        position_base=-1_000_000,
        entry_price_e8=100_000_000,
        collateral_quote=60_000,
        funding_paid_cumulative=0,
        funding_last_applied_epoch=2,
        liquidated_this_step=False,
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={
                market_id: PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=global_state,
                    accounts=accounts,
                )
            },
        ),
    )

    published = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=105_000_000)],
    )
    assert published.ok is True, published.error
    assert published.state is not None

    funded = _apply_result(
        state=published.state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "apply_funding_auto")],
    )

    assert funded.ok is False
    assert funded.state is None
    assert funded.effects is None
    assert funded.error is not None
    assert funded.error.startswith("apply_funding_auto would destroy mounted settlement path: ")


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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # No user positions are ever opened. Funding auto should still be callable for
    # the epoch and update the global funding rate deterministically.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)],
    )
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


def test_isolated_oi_liquidity_policy_rejects_unsupported_aggregate_open_interest() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oi-depth-policy"
    quote_asset = "0x" + "70" * 32
    operator = "00" * 48
    alice = "aa" * 48
    bob = "bb" * 48

    def apply_with_config(
        state: DexState, *, sender: str, ops: list[dict[str, object]], cfg: PerpEngineConfig
    ):
        result = apply_perp_ops(
            config=cfg,
            state=state,
            operations={"5": ops},
            tx_sender_pubkey=sender,
            block_timestamp=0,
        )
        return result

    def apply_ok(
        state: DexState, *, sender: str, ops: list[dict[str, object]], cfg: PerpEngineConfig
    ) -> DexState:
        result = apply_with_config(state, sender=sender, ops=ops, cfg=cfg)
        assert result.ok is True, result.error
        assert result.state is not None
        return result.state

    def setup_state(cfg: PerpEngineConfig) -> DexState:
        state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
        state = apply_ok(
            state,
            sender=operator,
            cfg=cfg,
            ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
        )
        state = _bootstrap(
            state=state,
            market_id=market_id,
            price_e8=100_000_000,
            operator_pubkey=operator,
        )
        state = apply_ok(
            state, sender=operator, cfg=cfg, ops=[_op(market_id, "advance_epoch", delta=1)]
        )
        state = apply_ok(
            state,
            sender=operator,
            cfg=cfg,
            ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
        )
        state = apply_ok(state, sender=operator, cfg=cfg, ops=[_op(market_id, "settle_epoch")])
        state = apply_ok(
            state, sender=operator, cfg=cfg, ops=[_op(market_id, "advance_epoch", delta=1)]
        )

        funded = BalanceTable()
        for (pk, asset), amt in state.balances.get_all_balances().items():
            funded.set(pk, asset, int(amt))
        funded.set(alice, quote_asset, 1_000_000_000)
        funded.set(bob, quote_asset, 1_000_000_000)
        return replace(state, balances=funded)

    cfg_open = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    open_state = setup_state(cfg_open)
    open_state = apply_ok(
        open_state,
        sender=alice,
        cfg=cfg_open,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=300_000),
        ],
    )
    open_result = apply_with_config(
        open_state,
        sender=bob,
        cfg=cfg_open,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=bob, amount=100_000),
            _op(market_id, "set_position", account_pubkey=bob, new_position_base=200_001),
        ],
    )
    assert open_result.ok is True, open_result.error

    cfg_guarded = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        isolated_oi_spot_depth_quote=1_000_000,
        isolated_oi_arbitrage_absorb_bps=5_000,
    )
    guarded_state = setup_state(cfg_guarded)
    guarded_state = apply_ok(
        guarded_state,
        sender=alice,
        cfg=cfg_guarded,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=300_000),
        ],
    )
    rejected = apply_with_config(
        guarded_state,
        sender=bob,
        cfg=cfg_guarded,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=bob, amount=100_000),
            _op(market_id, "set_position", account_pubkey=bob, new_position_base=200_001),
        ],
    )
    assert rejected.ok is False
    assert rejected.error is not None
    assert "open interest exceeds liquidity-depth bound" in rejected.error
    assert "open_interest_quote=500001" in rejected.error
    assert "max_open_interest_quote=500000" in rejected.error

    boundary = apply_with_config(
        guarded_state,
        sender=bob,
        cfg=cfg_guarded,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=bob, amount=100_000),
            _op(market_id, "set_position", account_pubkey=bob, new_position_base=200_000),
        ],
    )
    assert boundary.ok is True, boundary.error


def test_isolated_oi_depth_certificate_binds_market_and_epoch() -> None:
    from src.core.perp_depth_source_quorum_economics import (
        DepthSourceEconomicsRow,
        depth_source_quorum_economics_payload_from_fields,
    )
    from src.core.perp_oi_depth_certificate import (
        certificate_payload_from_fields,
        oi_depth_source_authority_hash,
        source_authority_binding_payload_from_fields,
        source_authority_payload_from_fields,
        verify_oi_depth_source_authority_payload,
    )
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oi-depth-cert"
    quote_asset = "0x" + "72" * 32
    operator = "00" * 48
    alice = "aa" * 48

    def apply_with_config(
        state: DexState, *, sender: str, ops: list[dict[str, object]], cfg: PerpEngineConfig
    ):
        result = apply_perp_ops(
            config=cfg,
            state=state,
            operations={"5": ops},
            tx_sender_pubkey=sender,
            block_timestamp=0,
        )
        return result

    def apply_ok(
        state: DexState, *, sender: str, ops: list[dict[str, object]], cfg: PerpEngineConfig
    ) -> DexState:
        result = apply_with_config(state, sender=sender, ops=ops, cfg=cfg)
        assert result.ok is True, result.error
        assert result.state is not None
        return result.state

    cfg_base = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = apply_ok(
        state,
        sender=operator,
        cfg=cfg_base,
        ops=[_op(market_id, "init_market", quote_asset=quote_asset)],
    )
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = apply_ok(
        state, sender=operator, cfg=cfg_base, ops=[_op(market_id, "advance_epoch", delta=1)]
    )
    state = apply_ok(
        state,
        sender=operator,
        cfg=cfg_base,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = apply_ok(state, sender=operator, cfg=cfg_base, ops=[_op(market_id, "settle_epoch")])
    state = apply_ok(
        state, sender=operator, cfg=cfg_base, ops=[_op(market_id, "advance_epoch", delta=1)]
    )

    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    funded.set(alice, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    cross_market_cert = certificate_payload_from_fields(
        market_id="perp:other-market",
        valid_from_epoch=2,
        valid_until_epoch=2,
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
        source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    cross_market_cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_oi_depth_certificate=True,
        isolated_oi_depth_certificate=cross_market_cert,
    )
    cross_market = apply_with_config(
        state,
        sender=alice,
        cfg=cross_market_cfg,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert cross_market.ok is False
    assert cross_market.error is not None
    assert "market_id mismatch" in cross_market.error

    stale_cert = certificate_payload_from_fields(
        market_id=market_id,
        valid_from_epoch=1,
        valid_until_epoch=1,
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
        source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    stale_cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_oi_depth_certificate=True,
        isolated_oi_depth_certificate=stale_cert,
    )
    stale = apply_with_config(
        state,
        sender=alice,
        cfg=stale_cfg,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert stale.ok is False
    assert stale.error is not None
    assert "certificate epoch out of range" in stale.error

    valid_cert = certificate_payload_from_fields(
        market_id=market_id,
        valid_from_epoch=2,
        valid_until_epoch=2,
        spot_depth_quote=1_000_000,
        arbitrage_absorb_bps=5_000,
        source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    missing_authority_cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_oi_depth_certificate=True,
        isolated_oi_depth_certificate=valid_cert,
        require_isolated_oi_depth_source_authority=True,
    )
    missing_authority = apply_with_config(
        state,
        sender=alice,
        cfg=missing_authority_cfg,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert missing_authority.ok is False
    assert missing_authority.error is not None
    assert "isolated OI depth source authority required" in missing_authority.error

    unauthorized_authority = source_authority_payload_from_fields(
        market_id=market_id,
        valid_from_epoch=2,
        valid_until_epoch=2,
        authorized_source_ids=("depth:amm:btc-usd",),
    )
    unauthorized_cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_oi_depth_certificate=True,
        isolated_oi_depth_certificate=valid_cert,
        require_isolated_oi_depth_source_authority=True,
        isolated_oi_depth_source_authority=unauthorized_authority,
    )
    unauthorized = apply_with_config(
        state,
        sender=alice,
        cfg=unauthorized_cfg,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert unauthorized.ok is False
    assert unauthorized.error is not None
    assert "source_id not authorized: depth:orderbook:btc-usd" in unauthorized.error

    valid_authority = source_authority_payload_from_fields(
        market_id=market_id,
        valid_from_epoch=2,
        valid_until_epoch=2,
        authorized_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    authority_verdict = verify_oi_depth_source_authority_payload(
        valid_authority,
        expected_market_id=market_id,
        now_epoch=2,
        required_source_ids=("depth:amm:btc-usd", "depth:orderbook:btc-usd"),
    )
    assert authority_verdict.ok is True
    assert authority_verdict.authority is not None
    authority_hash = oi_depth_source_authority_hash(authority_verdict.authority)
    state_root_hash = "sha256:" + "44" * 32
    other_state_root_hash = "sha256:" + "45" * 32
    policy_hash = "sha256:" + "55" * 32
    valid_binding = source_authority_binding_payload_from_fields(
        market_id=market_id,
        valid_from_epoch=2,
        valid_until_epoch=2,
        authority_hash=authority_hash,
        authority_state_root_hash=state_root_hash,
        policy_hash=policy_hash,
        signer_privkey=1,
    )
    signer = valid_binding["signer_pubkey"]
    assert isinstance(signer, str)

    missing_binding_cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_oi_depth_certificate=True,
        isolated_oi_depth_certificate=valid_cert,
        require_isolated_oi_depth_source_authority=True,
        isolated_oi_depth_source_authority=valid_authority,
        require_isolated_oi_depth_source_authority_binding=True,
        isolated_oi_depth_source_authority_state_root_hash=state_root_hash,
        isolated_oi_depth_source_authority_policy_hash=policy_hash,
        isolated_oi_depth_source_authority_signer_pubkeys=(signer,),
    )
    missing_binding = apply_with_config(
        state,
        sender=alice,
        cfg=missing_binding_cfg,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert missing_binding.ok is False
    assert missing_binding.error is not None
    assert "isolated OI depth source authority binding required" in missing_binding.error

    wrong_root_binding = source_authority_binding_payload_from_fields(
        market_id=market_id,
        valid_from_epoch=2,
        valid_until_epoch=2,
        authority_hash=authority_hash,
        authority_state_root_hash=other_state_root_hash,
        policy_hash=policy_hash,
        signer_privkey=1,
    )
    wrong_root_cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_oi_depth_certificate=True,
        isolated_oi_depth_certificate=valid_cert,
        require_isolated_oi_depth_source_authority=True,
        isolated_oi_depth_source_authority=valid_authority,
        require_isolated_oi_depth_source_authority_binding=True,
        isolated_oi_depth_source_authority_binding=wrong_root_binding,
        isolated_oi_depth_source_authority_state_root_hash=state_root_hash,
        isolated_oi_depth_source_authority_policy_hash=policy_hash,
        isolated_oi_depth_source_authority_signer_pubkeys=(signer,),
    )
    wrong_root = apply_with_config(
        state,
        sender=alice,
        cfg=wrong_root_cfg,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert wrong_root.ok is False
    assert wrong_root.error is not None
    assert "source authority binding state_root_hash mismatch" in wrong_root.error

    wrong_signer_binding = source_authority_binding_payload_from_fields(
        market_id=market_id,
        valid_from_epoch=2,
        valid_until_epoch=2,
        authority_hash=authority_hash,
        authority_state_root_hash=state_root_hash,
        policy_hash=policy_hash,
        signer_privkey=2,
    )
    wrong_signer_cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_oi_depth_certificate=True,
        isolated_oi_depth_certificate=valid_cert,
        require_isolated_oi_depth_source_authority=True,
        isolated_oi_depth_source_authority=valid_authority,
        require_isolated_oi_depth_source_authority_binding=True,
        isolated_oi_depth_source_authority_binding=wrong_signer_binding,
        isolated_oi_depth_source_authority_state_root_hash=state_root_hash,
        isolated_oi_depth_source_authority_policy_hash=policy_hash,
        isolated_oi_depth_source_authority_signer_pubkeys=(signer,),
    )
    wrong_signer = apply_with_config(
        state,
        sender=alice,
        cfg=wrong_signer_cfg,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert wrong_signer.ok is False
    assert wrong_signer.error is not None
    assert "source authority binding signer not allowed" in wrong_signer.error

    valid_cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_oi_depth_certificate=True,
        isolated_oi_depth_certificate=valid_cert,
        require_isolated_oi_depth_source_authority=True,
        isolated_oi_depth_source_authority=valid_authority,
        require_isolated_oi_depth_source_authority_binding=True,
        isolated_oi_depth_source_authority_binding=valid_binding,
        isolated_oi_depth_source_authority_state_root_hash=state_root_hash,
        isolated_oi_depth_source_authority_policy_hash=policy_hash,
        isolated_oi_depth_source_authority_signer_pubkeys=(signer,),
    )
    accepted = apply_with_config(
        state,
        sender=alice,
        cfg=valid_cfg,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert accepted.ok is True, accepted.error

    def economics_payload(
        *,
        reported_depth_quote: int = 1_000_000,
        arbitrage_absorb_bps: int = 5_000,
        source_ids: tuple[str, ...] = (
            "depth:amm:btc-usd",
            "depth:orderbook:btc-usd",
        ),
        slashable_each_quote: int = 15_000,
        threshold: int | None = None,
    ) -> dict[str, object]:
        rows = tuple(
            DepthSourceEconomicsRow(
                source_id=source_id,
                weight=1,
                bond_quote=slashable_each_quote,
                slash_fraction_bps=10_000,
                future_value_lost_quote=0,
            )
            for source_id in source_ids
        )
        return depth_source_quorum_economics_payload_from_fields(
            market_id=market_id,
            valid_from_epoch=2,
            valid_until_epoch=2,
            policy_hash=policy_hash,
            source_rows=rows,
            quorum_threshold_weight=threshold or len(rows),
            true_depth_quote=500_000,
            reported_depth_quote=reported_depth_quote,
            arbitrage_absorb_bps=arbitrage_absorb_bps,
            defect_gain_bps=1_000,
            deterrence_margin_bps=2_000,
        )

    def economics_cfg(
        economics: dict[str, object] | None,
        *,
        binding: dict[str, object] | None = valid_binding,
        require_economics: bool = True,
    ) -> PerpEngineConfig:
        return PerpEngineConfig(
            operator_pubkey=operator,
            allow_isolated_markets=True,
            require_isolated_oi_depth_certificate=True,
            isolated_oi_depth_certificate=valid_cert,
            require_isolated_oi_depth_source_authority=True,
            isolated_oi_depth_source_authority=valid_authority,
            isolated_oi_depth_source_authority_binding=binding,
            isolated_oi_depth_source_authority_state_root_hash=state_root_hash,
            isolated_oi_depth_source_authority_policy_hash=policy_hash,
            isolated_oi_depth_source_authority_signer_pubkeys=(signer,),
            require_isolated_oi_depth_source_quorum_economics=require_economics,
            isolated_oi_depth_source_quorum_economics=economics,
            isolated_oi_depth_source_quorum_economics_policy_hash=policy_hash,
        )

    missing_economics = apply_with_config(
        state,
        sender=alice,
        cfg=economics_cfg(None),
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert missing_economics.ok is False
    assert missing_economics.error is not None
    assert "source quorum economics envelope required" in missing_economics.error

    missing_economics_binding = apply_with_config(
        state,
        sender=alice,
        cfg=economics_cfg(economics_payload(), binding=None, require_economics=False),
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert missing_economics_binding.ok is False
    assert missing_economics_binding.error is not None
    assert "binding required for source quorum economics" in missing_economics_binding.error

    depth_substitution = apply_with_config(
        state,
        sender=alice,
        cfg=economics_cfg(economics_payload(reported_depth_quote=900_000)),
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert depth_substitution.ok is False
    assert depth_substitution.error is not None
    assert "reported_depth_quote mismatch" in depth_substitution.error

    absorb_substitution = apply_with_config(
        state,
        sender=alice,
        cfg=economics_cfg(economics_payload(arbitrage_absorb_bps=4_000)),
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert absorb_substitution.ok is False
    assert absorb_substitution.error is not None
    assert "arbitrage_absorb_bps mismatch" in absorb_substitution.error

    source_substitution = apply_with_config(
        state,
        sender=alice,
        cfg=economics_cfg(
            economics_payload(
                source_ids=("depth:amm:btc-usd",),
                slashable_each_quote=30_000,
                threshold=1,
            )
        ),
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert source_substitution.ok is False
    assert source_substitution.error is not None
    assert "source_rows source_id mismatch" in source_substitution.error

    unbonded_economics = apply_with_config(
        state,
        sender=alice,
        cfg=economics_cfg(economics_payload(slashable_each_quote=0)),
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert unbonded_economics.ok is False
    assert unbonded_economics.error is not None
    assert "quorum_downside_below_required" in unbonded_economics.error

    valid_economics = apply_with_config(
        state,
        sender=alice,
        cfg=economics_cfg(economics_payload()),
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100_000),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=100_000),
        ],
    )
    assert valid_economics.ok is True, valid_economics.error


def test_advance_epoch_rejects_skipped_oracle_window_before_funding() -> None:
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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Tight staleness budget so a skipped epoch window fail-closes funding.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"max_oracle_staleness_epochs": 1})],
    )

    # A caller-selected jump could stale the Oracle and strand every recovery
    # action. The mounted lifecycle accepts exactly one epoch at a time.
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=3)],
    )
    assert res.ok is False
    assert res.state is None
    assert res.effects is None
    assert res.error == "advance_epoch delta must be 1 for isolated markets"


def test_set_market_params_rejects_staleness_widening_with_open_positions() -> None:
    market_id = "perp:stale-softening"
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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"max_oracle_staleness_epochs": 1})],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    widened = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"max_oracle_staleness_epochs": 100})],
    )
    assert widened.ok is False
    assert widened.error is not None
    assert "cannot increase max_oracle_staleness_epochs while positions are open" in widened.error

    skipped = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=3)],
    )
    assert skipped.ok is False
    assert skipped.state is None
    assert skipped.effects is None
    assert skipped.error == "advance_epoch delta must be 1 for isolated markets"

    # Preserve stale-snapshot guard coverage for imported/recovered snapshots.
    assert state.perps is not None
    market = state.perps.markets[market_id]
    stale_global = dict(market.global_state)
    stale_global["now_epoch"] = int(stale_global["now_epoch"]) + 3
    stale_global["epoch_phase"] = 0
    stale_market = type(market)(
        quote_asset=market.quote_asset,
        global_state=stale_global,
        accounts=dict(market.accounts),
    )
    stale_state = replace(
        state,
        perps=type(state.perps)(
            version=state.perps.version,
            markets={market_id: stale_market},
        ),
    )
    stale_withdraw = _apply_result(
        state=stale_state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[_op(market_id, "withdraw_collateral", account_pubkey=alice, amount=1)],
    )
    assert stale_withdraw.ok is False
    assert stale_withdraw.error == "guard"


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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)],
    )

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
        (
            "max_oracle_staleness_epochs",
            0,
            "cannot apply funding: invalid max_oracle_staleness_epochs",
        ),
        ("funding_cap_bps", 0, "cannot apply funding: invalid funding_cap_bps"),
        ("clearing_price_e8", 0, "cannot apply funding: clearing_price_e8 must be positive"),
        ("max_oracle_move_bps", -1, "cannot apply funding: invalid max_oracle_move_bps"),
    )
    for field, value, expected_error in malformed_cases:
        try:
            candidate_state = _state_with_global_override(field, value)
        except ValueError as exc:
            assert field == "max_oracle_move_bps"
            assert "invalid funded liquidation params" in str(exc)
            continue
        res = _apply_result(
            state=candidate_state,
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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)],
    )

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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=102_000_000)],
    )

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


def test_apply_funding_auto_requires_closeout_liability_certificate_for_negative_net_funding() -> (
    None
):
    from src.core.perp_funding_closeout_liability_certificate import (
        PositionAccount,
        build_funding_closeout_liability_certificate,
        funding_closeout_liability_certificate_to_payload,
    )
    from src.core.perp_v2.math import PRICE_SCALE, funding_payment
    from src.core.perps import (
        PERPS_STATE_VERSION,
        PerpAccountState,
        PerpMarketState,
        PerpsState,
    )
    from src.integration.perp_engine import (
        PerpEngineConfig,
        _kernel_initial_global_state,
        apply_perp_ops,
    )

    market_id = "perp:funding-closeout-cert"
    quote_asset = "0x" + "6c" * 32
    operator = "00" * 48
    payer = "aa" * 48
    receiver = "bb" * 48
    price_e8 = 100 * PRICE_SCALE
    funding_price_e8 = 102 * PRICE_SCALE
    position_base = 100_000
    missing_payer_due_quote = funding_payment(position_base, price_e8, 100)
    assert missing_payer_due_quote == 100_000

    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": price_e8,
            "clearing_price_seen": False,
            "clearing_price_epoch": 0,
            "clearing_price_e8": 0,
            "fee_pool_quote": 95_000,
            "fee_income": 95_000,
            "initial_insurance": 0,
            "insurance_balance": 95_000,
            "min_notional_for_bounty": 0,
        }
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={
                market_id: PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=global_state,
                    accounts={
                        payer: PerpAccountState(
                            position_base=position_base,
                            entry_price_e8=price_e8,
                            collateral_quote=5_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        receiver: PerpAccountState(
                            position_base=-position_base,
                            entry_price_e8=price_e8,
                            collateral_quote=600_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                    },
                )
            },
        ),
    )
    base_config = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    closeout = apply_perp_ops(
        config=base_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "partial_liquidate",
                    account_pubkey=payer,
                    fraction_bps=10_000,
                )
            ]
        },
        tx_sender_pubkey=payer,
        block_timestamp=0,
    )
    assert closeout.ok is True, closeout.error
    assert closeout.state is not None
    assert closeout.effects is not None
    publish = apply_perp_ops(
        config=base_config,
        state=closeout.state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=funding_price_e8)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert publish.ok is True, publish.error
    assert publish.state is not None

    cert = build_funding_closeout_liability_certificate(
        (
            PositionAccount(payer, position_base),
            PositionAccount(receiver, -position_base),
        ),
        (
            PositionAccount(payer, 0),
            PositionAccount(receiver, -position_base),
        ),
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        sink_draw_by_account={payer: missing_payer_due_quote},
    )
    guarded_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_funding_closeout_liability_certificate_on_negative_net_funding=True,
        isolated_funding_closeout_pre_due_vector_hash=cert.pre_due_vector_hash,
    )

    missing = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={"5": [_op(market_id, "apply_funding_auto")]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert missing.ok is False
    assert (
        missing.error == "funding closeout liability certificate required for negative net funding"
    )

    legacy_perps = replace(
        publish.state.perps,
        markets={
            **publish.state.perps.markets,
            market_id: replace(
                publish.state.perps.markets[market_id],
                pending_funding_closeout_source_availability_hashes=(),
            ),
        },
    )
    valid = apply_perp_ops(
        config=guarded_config,
        state=replace(publish.state, perps=legacy_perps),
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_liability_certificate=(
                        funding_closeout_liability_certificate_to_payload(cert)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert valid.ok is True, valid.error
    assert valid.state is not None
    assert valid.effects is not None
    assert valid.effects[0]["projected_net_funding_quote"] == -missing_payer_due_quote
    assert valid.effects[0]["fee_pool_after_quote"] == 0
    assert valid.state.perps is not None
    market = valid.state.perps.markets[market_id]
    assert market.accounts[receiver].collateral_quote == 700_000


def test_apply_funding_auto_receipt_binds_closeout_certificate_to_market_and_root() -> None:
    from src.core.perp_funding_closeout_liability_certificate import (
        PositionAccount,
        build_funding_closeout_liability_certificate,
        build_funding_closeout_liability_receipt,
        funding_closeout_liability_certificate_to_payload,
        funding_closeout_liability_receipt_to_payload,
    )
    from src.core.perp_v2.math import PRICE_SCALE, funding_payment
    from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
    from src.integration.perp_engine import (
        PerpEngineConfig,
        _kernel_initial_global_state,
        apply_perp_ops,
    )

    market_id = "perp:funding-closeout-receipt"
    quote_asset = "0x" + "6d" * 32
    operator = "00" * 48
    payer = "aa" * 48
    receiver = "bb" * 48
    price_e8 = 100 * PRICE_SCALE
    funding_price_e8 = 102 * PRICE_SCALE
    position_base = 100_000
    missing_payer_due_quote = funding_payment(position_base, price_e8, 100)

    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": price_e8,
            "clearing_price_seen": False,
            "clearing_price_epoch": 0,
            "clearing_price_e8": 0,
            "fee_pool_quote": 95_000,
            "fee_income": 95_000,
            "initial_insurance": 0,
            "insurance_balance": 95_000,
            "min_notional_for_bounty": 0,
        }
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={
                market_id: PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=global_state,
                    accounts={
                        payer: PerpAccountState(
                            position_base=position_base,
                            entry_price_e8=price_e8,
                            collateral_quote=5_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        receiver: PerpAccountState(
                            position_base=-position_base,
                            entry_price_e8=price_e8,
                            collateral_quote=600_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                    },
                )
            },
        ),
    )
    base_config = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    closeout = apply_perp_ops(
        config=base_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "partial_liquidate",
                    account_pubkey=payer,
                    fraction_bps=10_000,
                )
            ]
        },
        tx_sender_pubkey=payer,
        block_timestamp=0,
    )
    assert closeout.ok is True, closeout.error
    assert closeout.state is not None
    publish = apply_perp_ops(
        config=base_config,
        state=closeout.state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=funding_price_e8)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert publish.ok is True, publish.error
    assert publish.state is not None

    pre_accounts = (
        PositionAccount(payer, position_base),
        PositionAccount(receiver, -position_base),
    )
    post_accounts = (
        PositionAccount(payer, 0),
        PositionAccount(receiver, -position_base),
    )
    certificate = build_funding_closeout_liability_certificate(
        pre_accounts,
        post_accounts,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        sink_draw_by_account={payer: missing_payer_due_quote},
    )
    receipt = build_funding_closeout_liability_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        sink_draw_by_account={payer: missing_payer_due_quote},
    )
    guarded_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_funding_closeout_liability_receipt_on_negative_net_funding=True,
    )
    assert closeout.state.perps is not None
    closeout_market = closeout.state.perps.markets[market_id]
    assert tuple(closeout_market.pending_funding_closeout_root_hashes) == (
        receipt.pre_close_state_root_hash,
    )
    assert publish.state.perps is not None
    publish_market = publish.state.perps.markets[market_id]
    assert tuple(publish_market.pending_funding_closeout_root_hashes) == (
        receipt.pre_close_state_root_hash,
    )

    raw_cert = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_liability_certificate=(
                        funding_closeout_liability_certificate_to_payload(certificate)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert raw_cert.ok is False
    assert raw_cert.error == "funding closeout liability receipt required for negative net funding"

    wrong_market_payload = funding_closeout_liability_receipt_to_payload(receipt)
    wrong_market_payload["market_id"] = market_id + "-other"
    wrong_market = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_liability_receipt=wrong_market_payload,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_market.ok is False
    assert wrong_market.error == "invalid funding closeout liability receipt: market_id mismatch"

    wrong_root_payload = funding_closeout_liability_receipt_to_payload(receipt)
    wrong_root_payload["pre_close_state_root_hash"] = "sha256:" + "00" * 32
    wrong_root = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_liability_receipt=wrong_root_payload,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_root.ok is False
    assert wrong_root.error == "funding closeout receipt root not pending"

    valid = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_liability_receipt=(
                        funding_closeout_liability_receipt_to_payload(receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert valid.ok is True, valid.error
    assert valid.state is not None
    assert valid.effects is not None
    assert valid.effects[0]["projected_net_funding_quote"] == -missing_payer_due_quote
    assert valid.effects[0]["fee_pool_after_quote"] == 0
    assert valid.effects[0]["funding_closeout_pending_root_hashes_consumed"] == [
        receipt.pre_close_state_root_hash,
    ]
    assert valid.state.perps is not None
    valid_market = valid.state.perps.markets[market_id]
    assert valid_market.pending_funding_closeout_root_hashes == ()


def test_apply_funding_auto_v3_rationed_receipt_applies_multi_receiver_haircuts() -> None:
    from src.core.perp_funding_closeout_liability_certificate import (
        PositionAccount,
        build_funding_closeout_allocation_receipt,
        build_funding_closeout_rationed_allocation_receipt,
        build_funding_closeout_source_bound_rationed_allocation_receipt,
        funding_closeout_allocation_receipt_to_payload,
        funding_closeout_rationed_allocation_receipt_to_payload,
        funding_closeout_source_bound_rationed_allocation_receipt_to_payload,
    )
    from src.core.perp_funding_closeout_receiver_rationing import (
        ReceiverClaimRow,
        build_receiver_haircut_rationing,
        receiver_haircut_rationing_to_payload,
    )
    from src.core.perp_v2.math import PRICE_SCALE
    from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
    from src.integration.perp_engine import (
        PerpEngineConfig,
        _kernel_initial_global_state,
        apply_perp_ops,
    )

    market_id = "perp:funding-closeout-v3-rationed"
    quote_asset = "0x" + "6e" * 32
    operator = "00" * 48
    payer = "aa" * 48
    receiver_a = "bb" * 48
    receiver_b = "cc" * 48
    price_e8 = 100 * PRICE_SCALE
    funding_price_e8 = 102 * PRICE_SCALE

    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": price_e8,
            "clearing_price_seen": False,
            "clearing_price_epoch": 0,
            "clearing_price_e8": 0,
            "fee_pool_quote": 95_000,
            "fee_income": 95_000,
            "initial_insurance": 0,
            "insurance_balance": 95_000,
            "min_notional_for_bounty": 0,
        }
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={
                market_id: PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=global_state,
                    accounts={
                        payer: PerpAccountState(
                            position_base=100_000,
                            entry_price_e8=price_e8,
                            collateral_quote=5_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        receiver_a: PerpAccountState(
                            position_base=-60_000,
                            entry_price_e8=price_e8,
                            collateral_quote=600_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        receiver_b: PerpAccountState(
                            position_base=-40_000,
                            entry_price_e8=price_e8,
                            collateral_quote=400_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                    },
                )
            },
        ),
    )
    base_config = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    closeout = apply_perp_ops(
        config=base_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "partial_liquidate",
                    account_pubkey=payer,
                    fraction_bps=10_000,
                )
            ]
        },
        tx_sender_pubkey=payer,
        block_timestamp=0,
    )
    assert closeout.ok is True, closeout.error
    assert closeout.state is not None
    publish = apply_perp_ops(
        config=base_config,
        state=closeout.state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=funding_price_e8)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert publish.ok is True, publish.error
    assert publish.state is not None

    pre_accounts = (
        PositionAccount(payer, 100_000),
        PositionAccount(receiver_a, -60_000),
        PositionAccount(receiver_b, -40_000),
    )
    post_accounts = (
        PositionAccount(payer, 0),
        PositionAccount(receiver_a, -60_000),
        PositionAccount(receiver_b, -40_000),
    )
    v2_receipt = build_funding_closeout_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        payer_available_by_account={payer: 30_000},
        sink_capacity_by_account={payer: 40_000},
    )
    v3_receipt = build_funding_closeout_rationed_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        payer_available_by_account={payer: 30_000},
        sink_capacity_by_account={payer: 40_000},
    )
    v4_receipt = build_funding_closeout_source_bound_rationed_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        payer_available_by_account={payer: 30_000},
        sink_capacity_by_account={payer: 40_000},
    )
    v4_emitted_receipt = build_funding_closeout_source_bound_rationed_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        payer_available_by_account={payer: 0},
        sink_capacity_by_account={payer: 100_000},
    )
    assert (
        closeout.effects[0]["funding_closeout_source_availability_hash"]
        == v4_emitted_receipt.source_availability_hash
    )
    assert closeout.effects[0]["funding_closeout_source_availability_rows"] == [
        {
            "account_pubkey": payer,
            "epoch": 3,
            "payer_available_quote": 0,
            "sink_capacity_quote": 100_000,
        }
    ]
    assert closeout.state.perps is not None
    closeout_market = closeout.state.perps.markets[market_id]
    assert closeout_market.pending_funding_closeout_source_availability_hashes == (
        v4_emitted_receipt.source_availability_hash,
    )
    assert publish.state.perps is not None
    publish_market = publish.state.perps.markets[market_id]
    assert publish_market.pending_funding_closeout_source_availability_hashes == (
        v4_emitted_receipt.source_availability_hash,
    )
    legacy_perps = replace(
        publish.state.perps,
        markets={
            **publish.state.perps.markets,
            market_id: replace(
                publish.state.perps.markets[market_id],
                pending_funding_closeout_source_availability_hashes=(),
            ),
        },
    )
    legacy_source_state = replace(publish.state, perps=legacy_perps)
    guarded_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_funding_closeout_allocation_receipt_on_negative_net_funding=True,
    )

    v2_multi_receiver = apply_perp_ops(
        config=guarded_config,
        state=legacy_source_state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_allocation_receipt_to_payload(v2_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert v2_multi_receiver.ok is False
    assert (
        v2_multi_receiver.error
        == "funding closeout allocation receipt requires exactly one open funding receiver"
    )

    wrong_payload = funding_closeout_rationed_allocation_receipt_to_payload(v3_receipt)
    wrong_rationing = build_receiver_haircut_rationing(
        (
            ReceiverClaimRow(receiver_a, 50_000),
            ReceiverClaimRow(receiver_b, 50_000),
        ),
        total_haircut_quote=30_000,
    )
    wrong_payload["receiver_haircut_rationing"] = receiver_haircut_rationing_to_payload(
        wrong_rationing
    )
    wrong_rationing_res = apply_perp_ops(
        config=guarded_config,
        state=legacy_source_state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=wrong_payload,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_rationing_res.ok is False
    assert (
        wrong_rationing_res.error
        == "invalid funding closeout rationed allocation receipt: receiver haircut rationing mismatch"
    )

    source_bound_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_funding_closeout_allocation_receipt_on_negative_net_funding=True,
    )
    v3_under_source_policy = apply_perp_ops(
        config=source_bound_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_rationed_allocation_receipt_to_payload(v3_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert v3_under_source_policy.ok is False
    assert (
        v3_under_source_policy.error == "funding closeout source-bound allocation receipt required"
    )

    wrong_source_res = apply_perp_ops(
        config=source_bound_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_source_bound_rationed_allocation_receipt_to_payload(
                            v4_receipt
                        )
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_source_res.ok is False
    assert wrong_source_res.error == "funding closeout source availability root not pending"

    assert publish.state.perps is not None
    ambiguous_perps = replace(
        publish.state.perps,
        markets={
            **publish.state.perps.markets,
            market_id: replace(
                publish.state.perps.markets[market_id],
                pending_funding_closeout_source_availability_hashes=(
                    v4_emitted_receipt.source_availability_hash,
                    "sha256:" + "11" * 32,
                ),
            ),
        },
    )
    ambiguous_source = apply_perp_ops(
        config=source_bound_config,
        state=replace(publish.state, perps=ambiguous_perps),
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_source_bound_rationed_allocation_receipt_to_payload(
                            v4_emitted_receipt
                        )
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert ambiguous_source.ok is False
    assert ambiguous_source.error == "funding closeout source-portfolio allocation receipt required"

    source_bound_valid = apply_perp_ops(
        config=source_bound_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_source_bound_rationed_allocation_receipt_to_payload(
                            v4_emitted_receipt
                        )
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert source_bound_valid.ok is True, source_bound_valid.error
    assert source_bound_valid.effects is not None
    assert source_bound_valid.effects[0]["projected_net_funding_quote"] == -100_000
    assert source_bound_valid.effects[0]["funding_closeout_receiver_haircut_quote"] == 0
    assert source_bound_valid.effects[0]["funding_closeout_receiver_haircuts_quote_by_account"] == {
        receiver_a: 0,
        receiver_b: 0,
    }
    assert source_bound_valid.effects[0][
        "funding_closeout_pending_source_availability_hashes_consumed"
    ] == [v4_emitted_receipt.source_availability_hash]
    assert source_bound_valid.state is not None
    assert source_bound_valid.state.perps is not None
    source_bound_market = source_bound_valid.state.perps.markets[market_id]
    assert source_bound_market.accounts[receiver_a].collateral_quote == 660_000
    assert source_bound_market.accounts[receiver_b].collateral_quote == 440_000
    assert source_bound_market.pending_funding_closeout_source_availability_hashes == ()

    valid = apply_perp_ops(
        config=guarded_config,
        state=legacy_source_state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_rationed_allocation_receipt_to_payload(v3_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert valid.ok is True, valid.error
    assert valid.effects is not None
    assert valid.effects[0]["projected_net_funding_quote"] == -70_000
    assert valid.effects[0]["funding_closeout_receiver_haircut_quote"] == 30_000
    assert valid.effects[0]["funding_closeout_receiver_haircuts_quote_by_account"] == {
        receiver_a: 18_000,
        receiver_b: 12_000,
    }
    assert valid.state is not None
    assert valid.state.perps is not None
    valid_market = valid.state.perps.markets[market_id]
    assert valid_market.accounts[receiver_a].collateral_quote == 642_000
    assert valid_market.accounts[receiver_a].funding_paid_cumulative == -42_000
    assert valid_market.accounts[receiver_b].collateral_quote == 428_000
    assert valid_market.accounts[receiver_b].funding_paid_cumulative == -28_000
    assert valid_market.pending_funding_closeout_root_hashes == ()
    assert valid_market.pending_funding_closeout_source_availability_hashes == ()


def test_apply_funding_auto_mixed_open_netting_receipt_applies_signed_surface() -> None:
    from src.core.perp_funding_closeout_liability_certificate import PositionAccount
    from src.core.perp_funding_closeout_mixed_open_netting import (
        build_mixed_open_funding_netting_certificate,
        mixed_open_funding_netting_certificate_to_payload,
    )
    from src.core.perp_funding_closeout_receiver_rationing import (
        ReceiverClaimRow,
        build_receiver_haircut_rationing,
        receiver_haircut_rationing_to_payload,
    )
    from src.core.perp_v2.math import PRICE_SCALE
    from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
    from src.integration.perp_engine import (
        PerpEngineConfig,
        _kernel_initial_global_state,
        apply_perp_ops,
    )

    market_id = "perp:funding-closeout-mixed-open"
    quote_asset = "0x" + "7e" * 32
    operator = "00" * 48
    payer = "aa" * 48
    receiver = "bb" * 48
    price_e8 = 100 * PRICE_SCALE
    funding_price_e8 = 102 * PRICE_SCALE

    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": price_e8,
            "clearing_price_seen": False,
            "clearing_price_epoch": 0,
            "clearing_price_e8": 0,
            "fee_pool_quote": 30_000,
            "fee_income": 30_000,
            "initial_insurance": 0,
            "insurance_balance": 30_000,
            "min_notional_for_bounty": 0,
        }
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={
                market_id: PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=global_state,
                    accounts={
                        payer: PerpAccountState(
                            position_base=40_000,
                            entry_price_e8=price_e8,
                            collateral_quote=500_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        receiver: PerpAccountState(
                            position_base=-100_000,
                            entry_price_e8=price_e8,
                            collateral_quote=1_000_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                    },
                )
            },
        ),
    )
    base_config = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    publish = apply_perp_ops(
        config=base_config,
        state=state,
        operations={"5": [_op(market_id, "publish_clearing_price", price_e8=funding_price_e8)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert publish.ok is True, publish.error
    assert publish.state is not None

    post_accounts = (
        PositionAccount(payer, 40_000),
        PositionAccount(receiver, -100_000),
    )
    receipt = build_mixed_open_funding_netting_certificate(
        post_accounts,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        receiver_haircut_sum_quote=30_000,
    )
    guarded_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_funding_closeout_allocation_receipt_on_negative_net_funding=True,
    )

    raw_net_payload = mixed_open_funding_netting_certificate_to_payload(receipt)
    raw_net_rationing = build_receiver_haircut_rationing(
        (ReceiverClaimRow(receiver, 60_000),),
        total_haircut_quote=30_000,
    )
    raw_net_payload["receiver_haircut_rationing"] = receiver_haircut_rationing_to_payload(
        raw_net_rationing
    )
    raw_net_res = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=raw_net_payload,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert raw_net_res.ok is False
    assert (
        raw_net_res.error
        == "invalid funding closeout mixed-open netting receipt: receiver haircut rationing mismatch"
    )

    wrong_rate_receipt = build_mixed_open_funding_netting_certificate(
        post_accounts,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=50,
        receiver_haircut_sum_quote=15_000,
    )
    wrong_rate_res = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        mixed_open_funding_netting_certificate_to_payload(wrong_rate_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_rate_res.ok is False
    assert (
        wrong_rate_res.error
        == "invalid funding closeout mixed-open netting receipt: funding_rate_bps mismatch"
    )

    valid = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        mixed_open_funding_netting_certificate_to_payload(receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert valid.ok is True, valid.error
    assert valid.effects is not None
    assert valid.effects[0]["projected_net_funding_quote"] == -30_000
    assert valid.effects[0]["fee_pool_after_quote"] == 0
    assert valid.effects[0]["funding_closeout_receiver_haircut_quote"] == 30_000
    assert valid.effects[0]["funding_closeout_receiver_haircuts_quote_by_account"] == {
        receiver: 30_000,
    }
    assert valid.effects[0]["funding_closeout_allocation_receipt_applied"] is True
    assert valid.state is not None
    assert valid.state.perps is not None
    market = valid.state.perps.markets[market_id]
    assert market.accounts[payer].collateral_quote == 460_000
    assert market.accounts[payer].funding_paid_cumulative == 40_000
    assert market.accounts[receiver].collateral_quote == 1_070_000
    assert market.accounts[receiver].funding_paid_cumulative == -70_000


def test_apply_funding_auto_v5_source_portfolio_accepts_multi_closeout_reservations() -> None:
    from src.core.perp_funding_closeout_liability_certificate import (
        ClosedFundingSourceRow,
        PositionAccount,
        build_funding_closeout_carry_forward_receipt,
        build_funding_closeout_source_bound_rationed_allocation_receipt,
        build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt,
        carried_funding_closeout_liability_hash,
        funding_closeout_carry_forward_receipt_to_payload,
        funding_closeout_source_bound_rationed_allocation_receipt_to_payload,
        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload,
    )
    from src.core.perp_funding_closeout_policy_ledger import (
        HAIRCUT_POLICY_FINAL_LOSS,
        build_funding_closeout_policy_ledger,
        funding_closeout_policy_ledger_hash,
        funding_closeout_policy_ledger_to_payload,
    )
    from src.core.perp_v2.math import PRICE_SCALE
    from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
    from src.integration.perp_engine import (
        PerpEngineConfig,
        _kernel_initial_global_state,
        apply_perp_ops,
    )

    market_id = "perp:funding-closeout-v5-source-portfolio"
    quote_asset = "0x" + "6e" * 32
    operator = "00" * 48
    payer_a = "aa" * 48
    receiver_a = "bb" * 48
    receiver_b = "cc" * 48
    payer_b = "dd" * 48
    price_e8 = 100 * PRICE_SCALE
    funding_price_e8 = 102 * PRICE_SCALE

    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": price_e8,
            "clearing_price_seen": False,
            "clearing_price_epoch": 0,
            "clearing_price_e8": 0,
            "fee_pool_quote": 140_000,
            "fee_income": 140_000,
            "initial_insurance": 0,
            "insurance_balance": 140_000,
            "min_notional_for_bounty": 0,
        }
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={
                market_id: PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=global_state,
                    accounts={
                        payer_a: PerpAccountState(
                            position_base=100_000,
                            entry_price_e8=price_e8,
                            collateral_quote=5_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        payer_b: PerpAccountState(
                            position_base=50_000,
                            entry_price_e8=price_e8,
                            collateral_quote=5_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        receiver_a: PerpAccountState(
                            position_base=-90_000,
                            entry_price_e8=price_e8,
                            collateral_quote=900_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        receiver_b: PerpAccountState(
                            position_base=-60_000,
                            entry_price_e8=price_e8,
                            collateral_quote=600_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                    },
                )
            },
        ),
    )
    base_config = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)

    first_closeout = apply_perp_ops(
        config=base_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "partial_liquidate",
                    account_pubkey=payer_a,
                    fraction_bps=10_000,
                )
            ]
        },
        tx_sender_pubkey=payer_a,
        block_timestamp=0,
    )
    assert first_closeout.ok is True, first_closeout.error
    assert first_closeout.state is not None
    assert first_closeout.effects is not None
    second_closeout = apply_perp_ops(
        config=base_config,
        state=first_closeout.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "partial_liquidate",
                    account_pubkey=payer_b,
                    fraction_bps=10_000,
                )
            ]
        },
        tx_sender_pubkey=payer_b,
        block_timestamp=0,
    )
    assert second_closeout.ok is True, second_closeout.error
    assert second_closeout.state is not None
    assert second_closeout.effects is not None
    publish = apply_perp_ops(
        config=base_config,
        state=second_closeout.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "publish_clearing_price",
                    price_e8=funding_price_e8,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert publish.ok is True, publish.error
    assert publish.state is not None
    assert publish.state.perps is not None
    publish_market = publish.state.perps.markets[market_id]
    assert len(publish_market.pending_funding_closeout_source_availability_hashes) == 2
    assert int(publish_market.global_state["fee_pool_quote"]) == 150_000
    stale_settle = apply_perp_ops(
        config=base_config,
        state=publish.state,
        operations={"5": [_op(market_id, "settle_epoch")]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert stale_settle.ok is False
    assert (
        stale_settle.error
        == "settle_epoch requires pending funding closeout liabilities to be consumed before epoch boundary"
    )

    emitted_source_rows = tuple(
        ClosedFundingSourceRow(
            account_pubkey=str(row["account_pubkey"]),
            epoch=int(row["epoch"]),
            payer_available_quote=int(row["payer_available_quote"]),
            sink_capacity_quote=int(row["sink_capacity_quote"]),
        )
        for effect in (first_closeout.effects[0], second_closeout.effects[0])
        for row in effect["funding_closeout_source_availability_rows"]
    )
    assert emitted_source_rows == (
        ClosedFundingSourceRow(payer_a, 3, 0, 145_000),
        ClosedFundingSourceRow(payer_b, 3, 0, 150_000),
    )
    pre_accounts = (
        PositionAccount(payer_a, 100_000),
        PositionAccount(receiver_a, -90_000),
        PositionAccount(receiver_b, -60_000),
        PositionAccount(payer_b, 50_000),
    )
    post_accounts = (
        PositionAccount(payer_a, 0),
        PositionAccount(receiver_a, -90_000),
        PositionAccount(receiver_b, -60_000),
        PositionAccount(payer_b, 0),
    )
    v4_downgrade_receipt = build_funding_closeout_source_bound_rationed_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        payer_available_by_account={payer_a: 0, payer_b: 0},
        sink_capacity_by_account={payer_a: 100_000, payer_b: 50_000},
    )
    v5_receipt = build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        emitted_source_availability_rows=emitted_source_rows,
        aggregate_sink_capacity_quote=150_000,
        sink_capacity_by_account={payer_a: 100_000, payer_b: 50_000},
    )
    policy_ledger = build_funding_closeout_policy_ledger(
        v5_receipt,
        haircut_policy=HAIRCUT_POLICY_FINAL_LOSS,
    )
    policy_payload = funding_closeout_policy_ledger_to_payload(policy_ledger)
    policy_hash = funding_closeout_policy_ledger_hash(policy_ledger)
    carry_receipt = build_funding_closeout_carry_forward_receipt(
        v5_receipt,
        carry_epoch=4,
    )
    wrong_carry_payload = funding_closeout_carry_forward_receipt_to_payload(carry_receipt)
    wrong_carry_payload["pending_source_availability_hashes"] = ["sha256:" + "99" * 32]
    wrong_carry = apply_perp_ops(
        config=base_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "carry_funding_closeout_liability",
                    funding_closeout_carry_forward_receipt=wrong_carry_payload,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_carry.ok is False
    assert (
        wrong_carry.error
        == "invalid funding closeout carry-forward receipt: pending source availability hashes mismatch"
    )

    carry = apply_perp_ops(
        config=base_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "carry_funding_closeout_liability",
                    funding_closeout_carry_forward_receipt=(
                        funding_closeout_carry_forward_receipt_to_payload(carry_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert carry.ok is True, carry.error
    assert carry.effects is not None
    assert carry.effects[0]["source_epoch"] == 3
    assert carry.effects[0]["carry_epoch"] == 4
    assert carry.effects[0][
        "funding_closeout_carried_liability_hash"
    ] == carried_funding_closeout_liability_hash(carry_receipt)
    assert carry.state is not None
    assert carry.state.perps is not None
    carry_market = carry.state.perps.markets[market_id]
    assert carry_market.pending_funding_closeout_root_hashes == ()
    assert carry_market.pending_funding_closeout_source_availability_hashes == ()
    assert carry_market.pending_funding_closeout_carried_liability_hashes == (
        carried_funding_closeout_liability_hash(carry_receipt),
    )
    carried_settle = apply_perp_ops(
        config=base_config,
        state=carry.state,
        operations={"5": [_op(market_id, "settle_epoch")]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert carried_settle.ok is True, carried_settle.error
    assert carried_settle.state is not None

    premature_carried_settlement = apply_perp_ops(
        config=base_config,
        state=carried_settle.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_carried_liability",
                    funding_closeout_carry_forward_receipt=(
                        funding_closeout_carry_forward_receipt_to_payload(carry_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert premature_carried_settlement.ok is False
    assert (
        premature_carried_settlement.error
        == "cannot settle carried funding closeout after clearing price is published"
    )

    carried_advance = apply_perp_ops(
        config=base_config,
        state=carried_settle.state,
        operations={"5": [_op(market_id, "advance_epoch", delta=1)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert carried_advance.ok is True, carried_advance.error
    assert carried_advance.state is not None
    assert carried_advance.state.perps is not None
    carried_advanced_market = carried_advance.state.perps.markets[market_id]
    carried_pre_receiver_a = carried_advanced_market.accounts[receiver_a]
    carried_pre_receiver_b = carried_advanced_market.accounts[receiver_b]
    assert carried_advanced_market.pending_funding_closeout_carried_liability_hashes == (
        carried_funding_closeout_liability_hash(carry_receipt),
    )

    underfunded_carried_market = replace(
        carried_advanced_market,
        global_state={
            **carried_advanced_market.global_state,
            "claims_paid": 150_000,
            "insurance_balance": 0,
        },
    )
    underfunded_carried_state = replace(
        carried_advance.state,
        perps=replace(
            carried_advance.state.perps,
            markets={
                **carried_advance.state.perps.markets,
                market_id: underfunded_carried_market,
            },
        ),
    )
    underfunded_carried_settlement = apply_perp_ops(
        config=base_config,
        state=underfunded_carried_state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_carried_liability",
                    funding_closeout_carry_forward_receipt=(
                        funding_closeout_carry_forward_receipt_to_payload(carry_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert underfunded_carried_settlement.ok is False
    assert underfunded_carried_settlement.error == (
        "funding closeout carried settlement would violate funding sink bounds (payable=150000)"
    )

    carried_settlement = apply_perp_ops(
        config=base_config,
        state=carried_advance.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_carried_liability",
                    funding_closeout_carry_forward_receipt=(
                        funding_closeout_carry_forward_receipt_to_payload(carry_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert carried_settlement.ok is True, carried_settlement.error
    assert carried_settlement.effects is not None
    assert carried_settlement.effects[0][
        "funding_closeout_carried_liability_hash_consumed"
    ] == carried_funding_closeout_liability_hash(carry_receipt)
    assert carried_settlement.effects[0][
        "funding_closeout_carried_receiver_payments_quote_by_account"
    ] == {
        receiver_a: 90_000,
        receiver_b: 60_000,
    }
    assert carried_settlement.effects[0]["funding_closeout_carried_total_payable_quote"] == 150_000
    assert carried_settlement.state is not None
    assert carried_settlement.state.perps is not None
    carried_settled_market = carried_settlement.state.perps.markets[market_id]
    assert carried_settled_market.pending_funding_closeout_carried_liability_hashes == ()
    assert (
        carried_settled_market.accounts[receiver_a].collateral_quote
        == carried_pre_receiver_a.collateral_quote + 90_000
    )
    assert (
        carried_settled_market.accounts[receiver_a].funding_paid_cumulative
        == carried_pre_receiver_a.funding_paid_cumulative - 90_000
    )
    assert carried_settled_market.accounts[receiver_a].funding_last_applied_epoch == 3
    assert (
        carried_settled_market.accounts[receiver_b].collateral_quote
        == carried_pre_receiver_b.collateral_quote + 60_000
    )
    assert (
        carried_settled_market.accounts[receiver_b].funding_paid_cumulative
        == carried_pre_receiver_b.funding_paid_cumulative - 60_000
    )
    assert carried_settled_market.accounts[receiver_b].funding_last_applied_epoch == 3
    assert carried_settled_market.global_state["fee_pool_quote"] == 0
    assert carried_settled_market.global_state["fee_income"] == 0
    assert carried_settled_market.global_state["insurance_balance"] == 0

    duplicate_carried_settlement = apply_perp_ops(
        config=base_config,
        state=carried_settlement.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_carried_liability",
                    funding_closeout_carry_forward_receipt=(
                        funding_closeout_carry_forward_receipt_to_payload(carry_receipt)
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert duplicate_carried_settlement.ok is False
    assert (
        duplicate_carried_settlement.error == "funding closeout carried liability root not pending"
    )

    guarded_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_isolated_funding_closeout_allocation_receipt_on_negative_net_funding=True,
    )
    v4_downgrade = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_source_bound_rationed_allocation_receipt_to_payload(
                            v4_downgrade_receipt
                        )
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert v4_downgrade.ok is False
    assert v4_downgrade.error == "funding closeout source-portfolio allocation receipt required"

    under_reserved_payload = (
        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(v5_receipt)
    )
    under_reserved_payload["aggregate_sink_capacity_quote"] = 149_999
    under_reserved = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=under_reserved_payload,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert under_reserved.ok is False
    assert (
        under_reserved.error
        == "invalid funding closeout source-portfolio allocation receipt: aggregate sink capacity mismatch"
    )

    missing_policy = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
                            v5_receipt
                        )
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert missing_policy.ok is False
    assert (
        missing_policy.error
        == "funding closeout policy ledger required for source-portfolio allocation receipt"
    )

    wrong_policy_payload = dict(policy_payload)
    wrong_policy_payload["source_portfolio_receipt_hash"] = "sha256:" + "88" * 32
    wrong_policy = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
                            v5_receipt
                        )
                    ),
                    funding_closeout_policy_ledger=wrong_policy_payload,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_policy.ok is False
    assert (
        wrong_policy.error
        == "invalid funding closeout policy ledger: policy ledger source receipt hash mismatch"
    )

    valid = apply_perp_ops(
        config=guarded_config,
        state=publish.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "apply_funding_auto",
                    funding_closeout_allocation_receipt=(
                        funding_closeout_source_portfolio_bound_rationed_allocation_receipt_to_payload(
                            v5_receipt
                        )
                    ),
                    funding_closeout_policy_ledger=policy_payload,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert valid.ok is True, valid.error
    assert valid.effects is not None
    assert valid.effects[0]["projected_net_funding_quote"] == -150_000
    assert valid.effects[0]["funding_closeout_receiver_haircut_quote"] == 0
    assert valid.effects[0]["funding_closeout_receiver_haircuts_quote_by_account"] == {
        receiver_a: 0,
        receiver_b: 0,
    }
    assert valid.effects[0]["funding_closeout_pending_source_availability_hashes_consumed"] == list(
        publish_market.pending_funding_closeout_source_availability_hashes
    )
    assert valid.effects[0]["funding_closeout_policy_ledger_emitted"] is True
    assert valid.effects[0]["funding_closeout_policy_ledger_hash"] == policy_hash
    assert valid.effects[0]["funding_closeout_policy_ledger"] == policy_payload
    assert valid.state is not None
    assert valid.state.perps is not None
    valid_market = valid.state.perps.markets[market_id]
    assert valid_market.accounts[receiver_a].collateral_quote == 990_000
    assert valid_market.accounts[receiver_b].collateral_quote == 660_000
    assert valid_market.global_state["fee_pool_quote"] == 0
    assert valid_market.pending_funding_closeout_source_availability_hashes == ()
    assert valid_market.funding_closeout_policy_ledger_hashes == (policy_hash,)

    settled = apply_perp_ops(
        config=base_config,
        state=valid.state,
        operations={"5": [_op(market_id, "settle_epoch")]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert settled.ok is True, settled.error
    assert settled.state is not None
    assert settled.state.perps is not None
    settled_market = settled.state.perps.markets[market_id]
    assert settled_market.pending_funding_closeout_root_hashes == ()
    assert settled_market.pending_funding_closeout_source_availability_hashes == ()

    stale_import_perps = replace(
        settled.state.perps,
        markets={
            **settled.state.perps.markets,
            market_id: replace(
                settled_market,
                pending_funding_closeout_root_hashes=("sha256:" + "22" * 32,),
                pending_funding_closeout_source_availability_hashes=("sha256:" + "33" * 32,),
            ),
        },
    )
    stale_import_state = replace(settled.state, perps=stale_import_perps)
    stale_advance = apply_perp_ops(
        config=base_config,
        state=stale_import_state,
        operations={"5": [_op(market_id, "advance_epoch", delta=1)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert stale_advance.ok is False
    assert (
        stale_advance.error
        == "advance_epoch requires pending funding closeout liabilities to be consumed before epoch boundary"
    )


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
    state = _bootstrap(
        state=state,
        market_id=market_id,
        price_e8=100_000_000,
        operator_pubkey=operator,
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

    # Epoch 2 (OPEN): deposit collateral and open positions.
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )

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
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch")],
    )

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
        ops=[
            _op(
                market_id,
                "set_market_params",
                params={"initial_margin_bps": 3000, "maintenance_margin_bps": 2000},
            )
        ],
    )
    assert res_bad.ok is False
    assert res_bad.error is not None and "under maintenance margin" in res_bad.error

    # With open positions, decreasing the bounty threshold is rejected fail-closed
    # before evaluating the collectible-floor inequality.
    res_bounty_floor = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_market_params",
                params={"liquidation_penalty_bps": 50, "min_notional_for_bounty": 199},
            )
        ],
    )
    assert res_bounty_floor.ok is False
    assert (
        res_bounty_floor.error is not None
        and "cannot decrease min_notional_for_bounty while positions are open"
        in res_bounty_floor.error
    )

    # Scientist hardening: liquidation penalty must stay positive.
    res_zero_penalty = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"liquidation_penalty_bps": 0})],
    )
    assert res_zero_penalty.ok is False
    assert (
        res_zero_penalty.error is not None
        and "liquidation_penalty_bps > 0" in res_zero_penalty.error
    )

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
    assert (
        res_penalty_up.error is not None
        and "cannot increase liquidation_penalty_bps while positions are open"
        in res_penalty_up.error
    )

    # Scientist hardening: while positions are open, do not widen the stale-oracle action window.
    res_staleness_up = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"max_oracle_staleness_epochs": 101})],
    )
    assert res_staleness_up.ok is False
    assert res_staleness_up.error is not None
    assert (
        "cannot increase max_oracle_staleness_epochs while positions are open"
        in res_staleness_up.error
    )

    # Scientist hardening: while positions are open, do not allow lowering bounty threshold.
    res_bounty_down = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"min_notional_for_bounty": 50_000_000})],
    )
    assert res_bounty_down.ok is False
    assert (
        res_bounty_down.error is not None
        and "cannot decrease min_notional_for_bounty while positions are open"
        in res_bounty_down.error
    )

    # Hardening-direction updates are allowed while positions are open.
    res_harden = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[
            _op(
                market_id,
                "set_market_params",
                params={
                    "liquidation_penalty_bps": 40,
                    "max_oracle_staleness_epochs": 50,
                    "min_notional_for_bounty": 120_000_000,
                },
            )
        ],
    )
    assert res_harden.ok is True, res_harden.error

    # Mid-epoch guard: params can only be updated when the current epoch is settled.
    mid = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "advance_epoch", delta=1)],
    )
    res_mid = _apply_result(
        state=mid,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"initial_margin_bps": 1200})],
    )
    assert res_mid.ok is False
    assert res_mid.error == "cannot update market params mid-epoch"


def test_settle_funding_closeout_recovery_consumes_policy_root_and_distribution() -> None:
    from src.core.perp_funding_closeout_liability_certificate import (
        ClosedFundingSourceRow,
        PositionAccount,
        build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt,
    )
    from src.core.perp_funding_closeout_policy_ledger import (
        HAIRCUT_POLICY_RECOVERABLE_CLAIM,
        build_funding_closeout_policy_ledger,
        funding_closeout_policy_ledger_hash,
        funding_closeout_policy_ledger_to_payload,
    )
    from src.core.perp_funding_closeout_priority import (
        RECOVERY_PRIORITY_RECEIVER_FIRST,
        build_funding_closeout_receiver_recovery_distribution_certificate,
        build_funding_closeout_recovery_collection_receipt,
        build_funding_closeout_recovery_priority_certificate,
        build_funding_closeout_recovery_source_authority,
        build_funding_closeout_recovery_source_authority_binding,
        build_funding_closeout_sink_recovery_distribution_certificate,
        funding_closeout_receiver_recovery_distribution_certificate_to_payload,
        funding_closeout_recovery_collection_receipt_to_payload,
        funding_closeout_recovery_priority_certificate_to_payload,
        funding_closeout_recovery_source_authority_binding_hash,
        funding_closeout_recovery_source_authority_binding_to_payload,
        funding_closeout_recovery_source_authority_hash,
        funding_closeout_recovery_source_authority_to_payload,
        funding_closeout_sink_recovery_distribution_certificate_hash,
        funding_closeout_sink_recovery_distribution_certificate_to_payload,
    )
    from src.core.perp_v2.math import PRICE_SCALE
    from src.core.perps import PERPS_STATE_VERSION, PerpAccountState, PerpMarketState, PerpsState
    from src.integration.perp_engine import (
        PerpEngineConfig,
        _kernel_initial_global_state,
        apply_perp_ops,
    )

    market_id = "perp:funding-closeout-recovery-settlement"
    quote_asset = "0x" + "71" * 32
    operator = "00" * 48
    payer_a = "aa" * 48
    receiver_a = "bb" * 48
    receiver_b = "cc" * 48
    payer_b = "dd" * 48
    price_e8 = 100 * PRICE_SCALE
    authority_state_root_hash = "sha256:" + "44" * 32
    other_authority_state_root_hash = "sha256:" + "45" * 32
    authority_policy_hash = "sha256:" + "55" * 32

    global_state = _kernel_initial_global_state()
    global_state.update(
        {
            "now_epoch": 3,
            "epoch_phase": 0,
            "oracle_seen": True,
            "oracle_last_update_epoch": 2,
            "index_price_e8": price_e8,
            "fee_pool_quote": 0,
            "fee_income": 0,
            "insurance_balance": 0,
            "min_notional_for_bounty": 0,
        }
    )
    pre_accounts = (
        PositionAccount(payer_a, 100_000),
        PositionAccount(receiver_a, -90_000),
        PositionAccount(receiver_b, -60_000),
        PositionAccount(payer_b, 50_000),
    )
    post_accounts = (
        PositionAccount(payer_a, 0),
        PositionAccount(receiver_a, -90_000),
        PositionAccount(receiver_b, -60_000),
        PositionAccount(payer_b, 0),
    )
    source_receipt = build_funding_closeout_source_portfolio_bound_rationed_allocation_receipt(
        pre_accounts,
        post_accounts,
        market_id=market_id,
        epoch=3,
        price_e8=price_e8,
        funding_rate_bps=100,
        emitted_source_availability_rows=(
            ClosedFundingSourceRow(payer_a, 3, 0, 145_000),
            ClosedFundingSourceRow(payer_b, 3, 0, 150_000),
        ),
        aggregate_sink_capacity_quote=70_000,
        sink_capacity_by_account={payer_a: 40_000, payer_b: 30_000},
    )
    policy_ledger = build_funding_closeout_policy_ledger(
        source_receipt,
        haircut_policy=HAIRCUT_POLICY_RECOVERABLE_CLAIM,
    )
    policy_hash = funding_closeout_policy_ledger_hash(policy_ledger)
    priority = build_funding_closeout_recovery_priority_certificate(
        policy_ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=100_000,
    )
    collection = build_funding_closeout_recovery_collection_receipt(
        policy_ledger,
        priority,
        source_id="source:closed-payer-recovery",
        collection_nonce=1,
    )
    source_authority = build_funding_closeout_recovery_source_authority(
        market_id=market_id,
        valid_from_epoch=3,
        valid_until_epoch=3,
        authorized_source_ids=("source:closed-payer-recovery",),
    )
    unauthorized_source_authority = build_funding_closeout_recovery_source_authority(
        market_id=market_id,
        valid_from_epoch=3,
        valid_until_epoch=3,
        authorized_source_ids=("source:other-recovery",),
    )
    source_authority_binding = build_funding_closeout_recovery_source_authority_binding(
        market_id=market_id,
        valid_from_epoch=3,
        valid_until_epoch=3,
        authority_hash=funding_closeout_recovery_source_authority_hash(source_authority),
        authority_state_root_hash=authority_state_root_hash,
        policy_hash=authority_policy_hash,
        signer_privkey=1,
    )
    source_authority_binding_payload = (
        funding_closeout_recovery_source_authority_binding_to_payload(source_authority_binding)
    )
    source_authority_signer = str(source_authority_binding_payload["signer_pubkey"])
    distribution = build_funding_closeout_receiver_recovery_distribution_certificate(
        policy_ledger,
        priority,
    )
    sink_distribution = build_funding_closeout_sink_recovery_distribution_certificate(
        policy_ledger,
        priority,
    )
    sink_distribution_payload = funding_closeout_sink_recovery_distribution_certificate_to_payload(
        sink_distribution
    )
    partial_priority = build_funding_closeout_recovery_priority_certificate(
        policy_ledger,
        priority_policy=RECOVERY_PRIORITY_RECEIVER_FIRST,
        source_capacity_quote=50_000,
    )
    partial_collection = build_funding_closeout_recovery_collection_receipt(
        policy_ledger,
        partial_priority,
        source_id="source:closed-payer-recovery",
        collection_nonce=2,
    )
    partial_distribution = build_funding_closeout_receiver_recovery_distribution_certificate(
        policy_ledger,
        partial_priority,
    )
    partial_sink_distribution = build_funding_closeout_sink_recovery_distribution_certificate(
        policy_ledger,
        partial_priority,
    )
    initial_receiver_claim_balances = (
        (receiver_a, 48_000),
        (receiver_b, 32_000),
    )
    initial_receiver_claim_lots = (
        (receiver_a, "receiver-a-old", 10_000, 5),
        (receiver_a, "receiver-a-new", 38_000, 10),
        (receiver_b, "receiver-b-old", 12_000, 5),
        (receiver_b, "receiver-b-new", 20_000, 10),
    )
    state = DexState(
        balances=BalanceTable(),
        pools={},
        lp_balances=LPTable(),
        perps=PerpsState(
            version=PERPS_STATE_VERSION,
            markets={
                market_id: PerpMarketState(
                    quote_asset=quote_asset,
                    global_state=global_state,
                    accounts={
                        receiver_a: PerpAccountState(
                            position_base=-90_000,
                            entry_price_e8=price_e8,
                            collateral_quote=900_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                        receiver_b: PerpAccountState(
                            position_base=-60_000,
                            entry_price_e8=price_e8,
                            collateral_quote=600_000,
                            funding_paid_cumulative=0,
                            funding_last_applied_epoch=2,
                            liquidated_this_step=False,
                        ),
                    },
                    funding_closeout_policy_ledger_hashes=(policy_hash,),
                    funding_closeout_receiver_claim_balances_quote=(
                        initial_receiver_claim_balances
                    ),
                    funding_closeout_receiver_claim_lots_quote=(initial_receiver_claim_lots),
                )
            },
        ),
    )
    config = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    authorized_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        isolated_funding_closeout_recovery_source_authority=(
            funding_closeout_recovery_source_authority_to_payload(source_authority)
        ),
        isolated_funding_closeout_recovery_source_authority_binding=(
            source_authority_binding_payload
        ),
        isolated_funding_closeout_recovery_source_authority_state_root_hash=(
            authority_state_root_hash
        ),
        isolated_funding_closeout_recovery_source_authority_policy_hash=(authority_policy_hash),
        isolated_funding_closeout_recovery_source_authority_signer_pubkeys=(
            source_authority_signer,
        ),
    )
    unauthorized_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        isolated_funding_closeout_recovery_source_authority=(
            funding_closeout_recovery_source_authority_to_payload(unauthorized_source_authority)
        ),
    )
    missing_binding_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        isolated_funding_closeout_recovery_source_authority=(
            funding_closeout_recovery_source_authority_to_payload(source_authority)
        ),
    )
    wrong_root_config = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        isolated_funding_closeout_recovery_source_authority=(
            funding_closeout_recovery_source_authority_to_payload(source_authority)
        ),
        isolated_funding_closeout_recovery_source_authority_binding=(
            source_authority_binding_payload
        ),
        isolated_funding_closeout_recovery_source_authority_state_root_hash=(
            other_authority_state_root_hash
        ),
        isolated_funding_closeout_recovery_source_authority_policy_hash=(authority_policy_hash),
        isolated_funding_closeout_recovery_source_authority_signer_pubkeys=(
            source_authority_signer,
        ),
    )
    missing_collection = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert missing_collection.ok is False
    assert missing_collection.error == "funding closeout recovery collection receipt required"

    wrong_collection_payload = funding_closeout_recovery_collection_receipt_to_payload(collection)
    wrong_collection_payload["collected_source_quote"] = 99_999
    wrong_collection = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(wrong_collection_payload),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_collection.ok is False
    assert (
        wrong_collection.error == "invalid funding closeout recovery collection receipt: "
        "recovery collection credited amount mismatch"
    )

    missing_authority = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert missing_authority.ok is False
    assert missing_authority.error == "funding closeout recovery source authority required"

    missing_binding = apply_perp_ops(
        config=missing_binding_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert missing_binding.ok is False
    assert missing_binding.error == "funding closeout recovery source authority binding required"

    wrong_root = apply_perp_ops(
        config=wrong_root_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_root.ok is False
    assert (
        wrong_root.error == "invalid funding closeout recovery source authority binding: "
        "recovery source authority binding state_root_hash mismatch"
    )

    unauthorized_source = apply_perp_ops(
        config=unauthorized_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert unauthorized_source.ok is False
    assert (
        unauthorized_source.error == "invalid funding closeout recovery source authority: "
        "recovery source_id not authorized: source:closed-payer-recovery"
    )

    state_without_receiver_claims = replace(
        state,
        perps=replace(
            state.perps,
            markets={
                **state.perps.markets,
                market_id: replace(
                    state.perps.markets[market_id],
                    funding_closeout_receiver_claim_balances_quote=(),
                    funding_closeout_receiver_claim_lots_quote=(),
                ),
            },
        ),
    )
    missing_receiver_claim_balance = apply_perp_ops(
        config=authorized_config,
        state=state_without_receiver_claims,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert missing_receiver_claim_balance.ok is False
    assert (
        missing_receiver_claim_balance.error
        == "funding closeout recovery exceeds receiver claim balance"
    )

    partial = apply_perp_ops(
        config=authorized_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(partial_priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(partial_collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            partial_distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(
                        funding_closeout_sink_recovery_distribution_certificate_to_payload(
                            partial_sink_distribution
                        )
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert partial.ok is True, partial.error
    assert partial.effects is not None
    assert partial.effects[0]["funding_closeout_receiver_recovery_quote"] == 50_000
    assert partial.effects[0]["funding_closeout_sink_recovery_quote"] == 0
    assert partial.effects[0]["funding_closeout_receiver_recoveries_quote_by_account"] == {
        receiver_a: 30_000,
        receiver_b: 20_000,
    }
    assert partial.effects[0]["funding_closeout_receiver_claim_balances_quote"] == {
        receiver_a: 18_000,
        receiver_b: 12_000,
    }
    assert partial.effects[0]["funding_closeout_receiver_claim_lots_quote"] == [
        {
            "account_pubkey": receiver_a,
            "lot_id": "receiver-a-new",
            "balance_quote": 18_000,
            "expires_at_epoch": 10,
        },
        {
            "account_pubkey": receiver_b,
            "lot_id": "receiver-b-new",
            "balance_quote": 12_000,
            "expires_at_epoch": 10,
        },
    ]
    assert partial.effects[0]["funding_closeout_receiver_claim_lot_debits_quote"] == [
        {
            "account_pubkey": receiver_a,
            "lot_id": "receiver-a-old",
            "debited_quote": 10_000,
            "remaining_lot_balance_quote": 0,
            "expires_at_epoch": 5,
        },
        {
            "account_pubkey": receiver_a,
            "lot_id": "receiver-a-new",
            "debited_quote": 20_000,
            "remaining_lot_balance_quote": 18_000,
            "expires_at_epoch": 10,
        },
        {
            "account_pubkey": receiver_b,
            "lot_id": "receiver-b-old",
            "debited_quote": 12_000,
            "remaining_lot_balance_quote": 0,
            "expires_at_epoch": 5,
        },
        {
            "account_pubkey": receiver_b,
            "lot_id": "receiver-b-new",
            "debited_quote": 8_000,
            "remaining_lot_balance_quote": 12_000,
            "expires_at_epoch": 10,
        },
    ]
    assert partial.state is not None
    assert partial.state.perps is not None
    partial_market = partial.state.perps.markets[market_id]
    assert partial_market.funding_closeout_receiver_claim_balances_quote == (
        (receiver_a, 18_000),
        (receiver_b, 12_000),
    )
    assert partial_market.funding_closeout_receiver_claim_lots_quote == (
        (receiver_a, "receiver-a-new", 18_000, 10),
        (receiver_b, "receiver-b-new", 12_000, 10),
    )
    assert partial_market.funding_closeout_policy_ledger_hashes == ()

    valid = apply_perp_ops(
        config=authorized_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert valid.ok is True, valid.error
    assert valid.effects is not None
    assert valid.effects[0]["funding_closeout_policy_ledger_hash_consumed"] == policy_hash
    assert valid.effects[0]["funding_closeout_receiver_recovery_quote"] == 80_000
    assert valid.effects[0]["funding_closeout_sink_recovery_quote"] == 20_000
    assert valid.effects[0]["funding_closeout_collected_source_quote"] == 100_000
    assert (
        valid.effects[0]["funding_closeout_recovery_collection_source_id"]
        == "source:closed-payer-recovery"
    )
    assert valid.effects[0]["funding_closeout_recovery_source_authority_hash"].startswith("sha256:")
    assert valid.effects[0][
        "funding_closeout_recovery_source_authority_binding_hash"
    ] == funding_closeout_recovery_source_authority_binding_hash(source_authority_binding)
    assert valid.effects[0]["funding_closeout_receiver_recoveries_quote_by_account"] == {
        receiver_a: 48_000,
        receiver_b: 32_000,
    }
    assert valid.effects[0][
        "funding_closeout_sink_recovery_distribution_hash"
    ] == funding_closeout_sink_recovery_distribution_certificate_hash(sink_distribution)
    assert valid.effects[0]["funding_closeout_sink_recoveries_quote_by_claimant"] == {
        "protocol_sink": 20_000,
    }
    assert valid.effects[0]["funding_closeout_sink_claimant_balances_quote"] == {
        "protocol_sink": 20_000,
    }
    assert valid.effects[0]["funding_closeout_receiver_claim_balances_quote"] == {}
    assert valid.effects[0]["funding_closeout_receiver_claim_lots_quote"] == []
    assert valid.effects[0]["funding_closeout_sink_recovery_rows"] == [
        {
            "account_pubkey": payer_a,
            "claimant": "protocol_sink",
            "subrogated_claim_quote": 40_000,
            "recovery_quote": 11_429,
        },
        {
            "account_pubkey": payer_b,
            "claimant": "protocol_sink",
            "subrogated_claim_quote": 30_000,
            "recovery_quote": 8_571,
        },
    ]
    assert valid.state is not None
    assert valid.state.perps is not None
    valid_market = valid.state.perps.markets[market_id]
    assert valid_market.funding_closeout_policy_ledger_hashes == ()
    assert valid_market.funding_closeout_sink_claimant_balances_quote == (
        ("protocol_sink", 20_000),
    )
    assert valid_market.funding_closeout_receiver_claim_balances_quote == ()
    assert valid_market.funding_closeout_receiver_claim_lots_quote == ()
    assert valid_market.accounts[receiver_a].collateral_quote == 948_000
    assert valid_market.accounts[receiver_a].funding_paid_cumulative == -48_000
    assert valid_market.accounts[receiver_b].collateral_quote == 632_000
    assert valid_market.accounts[receiver_b].funding_paid_cumulative == -32_000
    assert valid_market.global_state["fee_pool_quote"] == 20_000
    assert valid_market.global_state["fee_income"] == 20_000
    assert valid_market.global_state["insurance_balance"] == 20_000

    duplicate = apply_perp_ops(
        config=authorized_config,
        state=valid.state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert duplicate.ok is False
    assert duplicate.error == "funding closeout policy ledger root not pending"

    missing_sink_distribution = apply_perp_ops(
        config=authorized_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert missing_sink_distribution.ok is False
    assert missing_sink_distribution.error == "funding closeout sink distribution required"

    wrong_distribution_payload = (
        funding_closeout_receiver_recovery_distribution_certificate_to_payload(distribution)
    )
    rows = list(wrong_distribution_payload["receiver_rows"])
    rows[0] = {**rows[0], "recovery_quote": 50_000}
    rows[1] = {**rows[1], "recovery_quote": 30_000}
    wrong_distribution_payload["receiver_rows"] = rows
    wrong_distribution = apply_perp_ops(
        config=authorized_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(wrong_distribution_payload),
                    funding_closeout_sink_recovery_distribution=(sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_distribution.ok is False
    assert (
        wrong_distribution.error
        == "invalid funding closeout receiver distribution: receiver recovery row exceeds recoverable claim"
    )

    wrong_sink_distribution_payload = dict(sink_distribution_payload)
    sink_rows = list(wrong_sink_distribution_payload["sink_rows"])
    sink_rows[0] = {**sink_rows[0], "recovery_quote": 0}
    sink_rows[1] = {**sink_rows[1], "recovery_quote": 20_000}
    wrong_sink_distribution_payload["sink_rows"] = sink_rows
    wrong_sink_distribution = apply_perp_ops(
        config=authorized_config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_funding_closeout_recovery",
                    funding_closeout_policy_ledger=(
                        funding_closeout_policy_ledger_to_payload(policy_ledger)
                    ),
                    funding_closeout_recovery_priority_certificate=(
                        funding_closeout_recovery_priority_certificate_to_payload(priority)
                    ),
                    funding_closeout_recovery_collection_receipt=(
                        funding_closeout_recovery_collection_receipt_to_payload(collection)
                    ),
                    funding_closeout_receiver_recovery_distribution=(
                        funding_closeout_receiver_recovery_distribution_certificate_to_payload(
                            distribution
                        )
                    ),
                    funding_closeout_sink_recovery_distribution=(wrong_sink_distribution_payload),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert wrong_sink_distribution.ok is False
    assert (
        wrong_sink_distribution.error == "invalid funding closeout sink distribution: "
        "sink largest-remainder distribution mismatch"
    )
