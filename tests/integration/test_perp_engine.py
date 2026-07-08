from __future__ import annotations

from dataclasses import asdict, replace

from src.core.dex import DexState
from src.runtime.authority import (
    AuthorityMode,
    AuthorityPolicy,
    reset_active_authority_policy,
    set_active_authority_policy,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _perp_stateful_policy(mode: AuthorityMode) -> AuthorityPolicy:
    return AuthorityPolicy(
        default=AuthorityMode.PYTHON_AUTHORITY,
        per_surface={"perp_stateful": mode},
        promoted_surfaces=frozenset(),
    )


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


def _apply(*, state: DexState, tx_sender_pubkey: str, ops: list[dict[str, object]], operator_pubkey: str) -> DexState:
    res = _apply_result(state=state, tx_sender_pubkey=tx_sender_pubkey, operator_pubkey=operator_pubkey, ops=ops)
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def _with_oracle_snapshot(
    state: DexState,
    *,
    market_id: str,
    price_e8: int,
    last_update_epoch: int | None = None,
) -> DexState:
    # Test helper: model a validated oracle snapshot already present in app state.
    assert state.perps is not None
    market = state.perps.markets[market_id]
    global_state = dict(market.global_state)
    now_epoch = int(global_state.get("now_epoch", 0))
    global_state["oracle_seen"] = True
    global_state["oracle_last_update_epoch"] = (
        max(0, now_epoch - 1) if last_update_epoch is None else int(last_update_epoch)
    )
    global_state["index_price_e8"] = int(price_e8)
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset,
        global_state=global_state,
        accounts=dict(market.accounts),
    )
    return replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))


def _settle_ready_state(*, market_id: str, quote_asset: str, operator: str) -> DexState:
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
    return _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )


def test_init_market_np_rejects_unfunded_liquidation_params() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    operator = "00" * 48
    quote_asset = "0x" + "77" * 32
    res = apply_perp_ops(
        config=PerpEngineConfig(operator_pubkey=operator),
        state=DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable()),
        operations={
            "22": [
                _op(
                    "perp:chnp:unfunded",
                    "init_market_np",
                    version="1.2",
                    quote_asset=quote_asset,
                    index_price_e8=100_000_000,
                    params={"max_oracle_move_bps": 548},
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error is not None and "funded liquidation" in res.error


def _perps_oracle_authorization_bundle(config: object, state: DexState, market_id: str, *, value_e8: int | None = None) -> dict[str, object]:
    from src.integration.perp_engine import (
        _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        _isolated_settle_oracle_runtime_facts,
    )
    from src.integration.zeno_oracle_authorization import (
        OracleAuthorization,
        oracle_value_hash,
        semantic_hash,
    )
    from tests.integration.oracle_authorization_test_helpers import authorization_bundle

    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    observed_epoch = int(market.global_state.get("oracle_last_update_epoch", 0))
    now_epoch = int(market.global_state.get("now_epoch", 0))
    authorized_value_e8 = int(market.global_state.get("index_price_e8", 0) if value_e8 is None else value_e8)
    authorization = OracleAuthorization(
        consumer_module="zenodex.perps",
        action_kind="settle_epoch",
        action_id=str(runtime["action_id"]),
        action_facts_hash=str(runtime["action_facts_hash"]),
        pre_state_hash=str(runtime["pre_state_hash"]),
        profile_id=_ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        query_id=str(runtime["query_id"]),
        value_e8=authorized_value_e8,
        value_hash=oracle_value_hash(
            query_id=str(runtime["query_id"]),
            value_e8=authorized_value_e8,
            observed_epoch=observed_epoch,
        ),
        confidence_e8=1,
        deviation_bps=0,
        observed_epoch=observed_epoch,
        expires_at_epoch=observed_epoch + 2,
        feed_id="feed:perps-index:v1",
        feed_registry_root=semantic_hash("test.perps.feed_registry", {"name": "r1"}),
        query_policy_root=semantic_hash("test.perps.query_policy", {"name": "q1"}),
        source_registry_root=semantic_hash("test.perps.source_registry", {"name": "s1"}),
        reporter_registry_root=semantic_hash("test.perps.reporter_registry", {"name": "p1"}),
        evidence_class="O3",
        economic_envelope_id="econ:perps-small-v1",
        receipt_graph_root=semantic_hash("test.perps.receipt_graph", {"name": "placeholder"}),
    )
    return authorization_bundle(asdict(authorization))


def _perps_settle_bridge_verifier(config: object, state: DexState, market_id: str):
    from src.integration.perp_engine import (
        _ORACLE_PERPS_INDEX_QUERY_ID,
        _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        _perps_runtime_oracle_action_id,
    )

    assert state.perps is not None
    market = state.perps.markets[market_id]
    expected_action_id = _perps_runtime_oracle_action_id(
        config,
        market_id=market_id,
        action_kind="settle_epoch",
        market=market,
    )

    def verifier(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "errors": [],
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": expected_action_id,
        }

    return verifier


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
        operations={"19": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
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
        operations={"19": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
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
        operations={"19": [_op(market_id, "init_market", quote_asset=quote_asset)]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is True, res.error


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
        operations={"19": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
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
        operations={"19": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
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
        operations={"19": [_op(market_id, "publish_clearing_price", price_e8=100_000_000)]},
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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
            "19": [
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
            "19": [
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000_000)
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

    post = _apply(state=pre, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000_000)
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
        operations={"19": [_op(market_id, "advance_epoch", delta="1")]},  # type: ignore[arg-type]
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
        operations={"19": [_op(market_id, "advance_epoch", delta=(1 << 200))]},
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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


def test_settle_epoch_rejects_missing_oracle_snapshot() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:missing-oracle"
    quote_asset = "0x" + "57" * 32
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
    assert state.perps is not None
    market = state.perps.markets[market_id]
    global_state = dict(market.global_state)
    global_state["oracle_seen"] = False
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(
        quote_asset=market.quote_asset,
        global_state=global_state,
        accounts=dict(market.accounts),
    )
    state = replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle_epoch=True,
    )
    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle_epoch=True,
        oracle_adapter_bridge_verifier=_perps_settle_bridge_verifier(cfg, state, market_id),
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={
            "19": [
                _op(
                    market_id,
                    "settle_epoch",
                    oracle_adapter_bridge={"schema": "test"},
                    oracle_authorization=_perps_oracle_authorization_bundle(cfg, state, market_id),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "oracle_authorization_rejected: oracle snapshot not seen"


def test_settle_epoch_requires_oracle_adapter_bridge_when_configured() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-bridge-required"
    quote_asset = "0x" + "5a" * 32
    operator = "00" * 48
    state = _settle_ready_state(market_id=market_id, quote_asset=quote_asset, operator=operator)

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_adapter_for_isolated_settle_epoch=True,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"19": [_op(market_id, "settle_epoch")]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "settle_epoch requires oracle_adapter_bridge"


def test_settle_epoch_rejects_unverified_oracle_adapter_bridge() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-bridge-unverified"
    quote_asset = "0x" + "5b" * 32
    operator = "00" * 48
    state = _settle_ready_state(market_id=market_id, quote_asset=quote_asset, operator=operator)

    cfg = PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True)
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"19": [_op(market_id, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "oracle_adapter_bridge verifier not configured"

    cfg_rejecting = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        oracle_adapter_bridge_verifier=lambda _bridge: {
            "status": "rejected",
            "errors": ["aggregate_read_not_accepted"],
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
        },
    )
    res_rejected = apply_perp_ops(
        config=cfg_rejecting,
        state=state,
        operations={"19": [_op(market_id, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res_rejected.ok is False
    assert res_rejected.error == "oracle_adapter_bridge rejected: aggregate_read_not_accepted"


def test_settle_epoch_binds_oracle_adapter_bridge_to_perps_settlement() -> None:
    from src.integration.perp_engine import (
        _ORACLE_PERPS_INDEX_QUERY_ID,
        _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        PerpEngineConfig,
        _perps_runtime_oracle_action_id,
        apply_perp_ops,
    )

    market_id = "perp:oracle-bridge-bound"
    quote_asset = "0x" + "5c" * 32
    operator = "00" * 48
    state = _settle_ready_state(market_id=market_id, quote_asset=quote_asset, operator=operator)

    cfg_wrong_action = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        oracle_adapter_bridge_verifier=lambda _bridge: {
            "status": "accepted",
            "errors": [],
            "consumer_module": "zenodex.perps",
            "action_kind": "liquidate_account",
        },
    )
    res_wrong_action = apply_perp_ops(
        config=cfg_wrong_action,
        state=state,
        operations={"19": [_op(market_id, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res_wrong_action.ok is False
    assert res_wrong_action.error == "oracle_adapter_bridge action mismatch"

    cfg_wrong_action_id = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        oracle_adapter_bridge_verifier=lambda _bridge: {
            "status": "accepted",
            "errors": [],
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": "sha256:" + "00" * 32,
        },
    )
    res_wrong_action_id = apply_perp_ops(
        config=cfg_wrong_action_id,
        state=state,
        operations={"19": [_op(market_id, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res_wrong_action_id.ok is False
    assert res_wrong_action_id.error == "oracle_adapter_bridge action_id mismatch"

    seen_bridge: dict[str, object] = {}
    assert state.perps is not None
    expected_action_id = _perps_runtime_oracle_action_id(
        PerpEngineConfig(operator_pubkey=operator, allow_isolated_markets=True),
        market_id=market_id,
        action_kind="settle_epoch",
        market=state.perps.markets[market_id],
    )

    cfg_wrong_profile = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        oracle_adapter_bridge_verifier=lambda _bridge: {
            "status": "accepted",
            "errors": [],
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": "sha256:" + "00" * 32,
            "action_id": expected_action_id,
        },
    )
    res_wrong_profile = apply_perp_ops(
        config=cfg_wrong_profile,
        state=state,
        operations={"19": [_op(market_id, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res_wrong_profile.ok is False
    assert res_wrong_profile.error == "oracle_adapter_bridge profile mismatch"

    def verifier(bridge: object) -> dict[str, object]:
        assert isinstance(bridge, dict)
        seen_bridge.update(bridge)
        return {
            "status": "accepted",
            "errors": [],
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": expected_action_id,
        }

    cfg_accepting = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        oracle_adapter_bridge_verifier=verifier,
        require_oracle_adapter_for_isolated_settle_epoch=True,
    )
    res = apply_perp_ops(
        config=cfg_accepting,
        state=state,
        operations={"19": [_op(market_id, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is True, res.error
    assert seen_bridge == {"schema": "test"}


def test_settle_epoch_requires_oracle_authorization_when_configured() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-auth-required"
    quote_asset = "0x" + "5d" * 32
    operator = "00" * 48
    state = _settle_ready_state(market_id=market_id, quote_asset=quote_asset, operator=operator)

    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle_epoch=True,
    )
    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={"19": [_op(market_id, "settle_epoch")]},
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error == "oracle_authorization_required"


def test_settle_epoch_rejects_self_attested_oracle_authorization_without_bridge() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-auth-self-attested"
    quote_asset = "0x" + "60" * 32
    operator = "00" * 48
    state = _settle_ready_state(market_id=market_id, quote_asset=quote_asset, operator=operator)
    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle_epoch=True,
    )

    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={
            "19": [
                _op(
                    market_id,
                    "settle_epoch",
                    oracle_authorization=_perps_oracle_authorization_bundle(cfg, state, market_id),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error == "settle_epoch requires oracle_adapter_bridge"


def test_settle_epoch_accepts_bound_oracle_authorization() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-auth-bound"
    quote_asset = "0x" + "5e" * 32
    operator = "00" * 48
    state = _settle_ready_state(market_id=market_id, quote_asset=quote_asset, operator=operator)
    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle_epoch=True,
    )
    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle_epoch=True,
        oracle_adapter_bridge_verifier=_perps_settle_bridge_verifier(cfg, state, market_id),
    )

    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={
            "19": [
                _op(
                    market_id,
                    "settle_epoch",
                    oracle_adapter_bridge={"schema": "test"},
                    oracle_authorization=_perps_oracle_authorization_bundle(cfg, state, market_id),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is True, res.error


def test_settle_epoch_rejects_wrong_oracle_authorization_value() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:oracle-auth-wrong-value"
    quote_asset = "0x" + "5f" * 32
    operator = "00" * 48
    state = _settle_ready_state(market_id=market_id, quote_asset=quote_asset, operator=operator)
    assert state.perps is not None
    runtime_value_e8 = int(state.perps.markets[market_id].global_state["index_price_e8"])
    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle_epoch=True,
    )
    cfg = PerpEngineConfig(
        operator_pubkey=operator,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle_epoch=True,
        oracle_adapter_bridge_verifier=_perps_settle_bridge_verifier(cfg, state, market_id),
    )

    res = apply_perp_ops(
        config=cfg,
        state=state,
        operations={
            "19": [
                _op(
                    market_id,
                    "settle_epoch",
                    oracle_adapter_bridge={"schema": "test"},
                    oracle_authorization=_perps_oracle_authorization_bundle(
                        cfg,
                        state,
                        market_id,
                        value_e8=runtime_value_e8 + 1,
                    ),
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is False
    assert res.error is not None
    assert "runtime_value_e8 mismatch" in res.error


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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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


# --- Funding settlement helpers (zero-sum bounded-sink design) ---------------


def _funding_ready_state(*, market_id, quote_asset, operator, positions, clearing_price_e8, deposit=200_000):
    """Bootstrap an isolated market to epoch 3 with `positions` open and a
    clearing price published, ready for apply_funding_auto. `positions` is a
    list of (pubkey, position_base) and need NOT be position-balanced."""
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "init_market", quote_asset=quote_asset)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])

    funded = BalanceTable()
    for (pk, asset), amt in state.balances.get_all_balances().items():
        funded.set(pk, asset, int(amt))
    for pk, _pos in positions:
        funded.set(pk, quote_asset, 1_000_000_000)
    state = replace(state, balances=funded)

    for pk, pos in positions:
        state = _apply(
            state=state,
            tx_sender_pubkey=pk,
            operator_pubkey=operator,
            ops=[
                _op(market_id, "deposit_collateral", account_pubkey=pk, amount=deposit),
                _op(market_id, "set_position", account_pubkey=pk, new_position_base=pos),
            ],
        )

    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "settle_epoch")])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "advance_epoch", delta=1)])
    state = _apply(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "publish_clearing_price", price_e8=clearing_price_e8)])
    return state


def _seed_funding_sink(state, *, market_id, k):
    """Seed the protocol sink (fee_pool_quote/fee_income/insurance_balance) by k,
    preserving the persistent identities, so a negative funding net can be absorbed."""
    assert state.perps is not None
    market = state.perps.markets[market_id]
    gs = dict(market.global_state)
    initial_insurance = int(gs.get("initial_insurance", 0))
    claims_paid = int(gs.get("claims_paid", 0))
    gs["fee_income"] = int(k)
    gs["fee_pool_quote"] = int(k)
    gs["insurance_balance"] = initial_insurance + int(k) - claims_paid
    markets = dict(state.perps.markets)
    markets[market_id] = type(market)(quote_asset=market.quote_asset, global_state=gs, accounts=dict(market.accounts))
    return replace(state, perps=type(state.perps)(version=state.perps.version, markets=markets))


def _sink(market):
    gs = market.global_state
    return (int(gs["fee_pool_quote"]), int(gs["fee_income"]), int(gs["insurance_balance"]))


def _sum_collateral(market):
    return sum(int(a.collateral_quote) for a in market.accounts.values())


def test_apply_funding_auto_balanced_book_leaves_sink_unchanged() -> None:
    # Regression #1: balanced book, projected_net == 0, sink unchanged.
    market_id = "perp:funding-balanced"
    quote_asset = "0x" + "6d" * 32
    operator = "00" * 48
    alice, bob = "aa" * 48, "bb" * 48
    state = _funding_ready_state(
        market_id=market_id, quote_asset=quote_asset, operator=operator,
        positions=[(alice, 1_000_000), (bob, -1_000_000)], clearing_price_e8=102_000_000,
    )
    pre = state.perps.markets[market_id]
    pre_sink = _sink(pre)
    res = _apply_result(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "apply_funding_auto")])
    assert res.ok is True, res.error
    eff = res.effects[0]
    assert eff["raw_projected_net_funding_quote"] == 0
    assert eff["funding_sink_delta_quote"] == 0
    m = res.state.perps.markets[market_id]  # type: ignore[union-attr]
    assert _sink(m) == pre_sink  # equal & opposite funding nets to zero; sink untouched
    assert _sum_collateral(m) == _sum_collateral(pre)


def test_apply_funding_auto_positive_net_routes_to_sink() -> None:
    # Regression #2: a NET-LONG book (old design rejected Σ position_base != 0).
    # Structural net flows to the sink; all three sink mirrors increase.
    market_id = "perp:funding-net-long"
    quote_asset = "0x" + "6e" * 32
    operator = "00" * 48
    alice, bob = "aa" * 48, "bb" * 48
    state = _funding_ready_state(
        market_id=market_id, quote_asset=quote_asset, operator=operator,
        positions=[(alice, 2_000), (bob, -1_000)], clearing_price_e8=102_000_000,
    )
    pre = state.perps.markets[market_id]
    pre_fee, pre_inc, pre_ins = _sink(pre)
    pre_coll = _sum_collateral(pre)
    res = _apply_result(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "apply_funding_auto")])
    assert res.ok is True, res.error
    eff = res.effects[0]
    # rate=100 (2% basis capped): alice(long 2000) pays 20; bob(short 1000) gets 10; net +10.
    assert eff["net_position_base"] == 1_000
    assert eff["raw_projected_net_funding_quote"] == 10
    assert eff["funding_sink_delta_quote"] == 10
    m = res.state.perps.markets[market_id]  # type: ignore[union-attr]
    fee, inc, ins = _sink(m)
    assert (fee, inc, ins) == (pre_fee + 10, pre_inc + 10, pre_ins + 10)
    assert fee == inc  # identity fee_pool_quote == fee_income preserved
    # exact conservation: Δ(Σ collateral + fee_pool) == 0
    assert _sum_collateral(m) == pre_coll - 10
    assert _sum_collateral(m) + fee == pre_coll + pre_fee


def test_apply_funding_auto_no_user_absorbs_residual() -> None:
    # Regression #5: every account's collateral moves by EXACTLY its
    # formula-derived funding payment — no user absorbs a global accounting
    # residual (unlike the removed counterparty-residual design).
    from src.core.perp_v2.math import funding_payment as _funding_payment

    market_id = "perp:funding-no-transfer"
    quote_asset = "0x" + "6f" * 32
    operator = "00" * 48
    alice, bob = "aa" * 48, "bb" * 48
    state = _funding_ready_state(
        market_id=market_id, quote_asset=quote_asset, operator=operator,
        positions=[(alice, 2_000), (bob, -1_000)], clearing_price_e8=102_000_000,
    )
    pre = state.perps.markets[market_id]
    res = _apply_result(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "apply_funding_auto")])
    assert res.ok is True, res.error
    m = res.state.perps.markets[market_id]  # type: ignore[union-attr]
    rate = int(res.effects[0]["funding_rate_bps"])
    index = int(pre.global_state["index_price_e8"])
    for pk in (alice, bob):
        pre_coll = int(pre.accounts[pk].collateral_quote)
        post_coll = int(m.accounts[pk].collateral_quote)
        fp = _funding_payment(int(pre.accounts[pk].position_base), index, rate)
        assert post_coll == pre_coll - fp  # exactly the raw funding; no residual transfer


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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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
        try:
            malformed_state = _state_with_global_override(field, value)
        except ValueError as exc:
            assert field in str(exc)
            continue
        res = _apply_result(
            state=malformed_state,
            tx_sender_pubkey=operator,
            operator_pubkey=operator,
            ops=[_op(market_id, "apply_funding_auto")],
        )
        assert res.ok is False
        assert res.error == expected_error


def test_apply_funding_auto_negative_net_empty_sink_rejects() -> None:
    # Regressions #3 + #6: a NET-SHORT book makes payees receive more than
    # payers pay (projected_net < 0). A fresh (empty) sink cannot cover it, so
    # the op fails closed BEFORE any mutation (no-op on reject).
    market_id = "perp:funding-net-short-empty"
    quote_asset = "0x" + "67" * 32
    operator = "00" * 48
    alice, bob = "aa" * 48, "bb" * 48
    state = _funding_ready_state(
        market_id=market_id, quote_asset=quote_asset, operator=operator,
        positions=[(alice, 1_000), (bob, -2_000)], clearing_price_e8=102_000_000,
    )
    pre = state.perps.markets[market_id]
    pre_sink = _sink(pre)
    pre_coll = {pk: int(a.collateral_quote) for pk, a in pre.accounts.items()}
    # alice(long 1000) pays 10; bob(short 2000) gets 20; net = -10.
    res = _apply_result(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "apply_funding_auto")])
    assert res.ok is False
    assert res.error == "apply_funding_auto would drive a protocol sink out of bounds (net=-10)"
    # no-op on reject: the input state's market is byte-for-byte untouched.
    post = state.perps.markets[market_id]
    assert _sink(post) == pre_sink
    assert {pk: int(a.collateral_quote) for pk, a in post.accounts.items()} == pre_coll
    assert all(int(a.funding_last_applied_epoch) != 3 for a in post.accounts.values())


def test_apply_funding_auto_negative_net_prefunded_sink_succeeds() -> None:
    # Regression #4: the same NET-SHORT book succeeds once the sink is prefunded
    # enough to absorb the negative net; all three sink mirrors decrease by |net|.
    market_id = "perp:funding-net-short-funded"
    quote_asset = "0x" + "68" * 32
    operator = "00" * 48
    alice, bob = "aa" * 48, "bb" * 48
    state = _funding_ready_state(
        market_id=market_id, quote_asset=quote_asset, operator=operator,
        positions=[(alice, 1_000), (bob, -2_000)], clearing_price_e8=102_000_000,
    )
    state = _seed_funding_sink(state, market_id=market_id, k=50)
    pre = state.perps.markets[market_id]
    pre_fee, pre_inc, pre_ins = _sink(pre)
    pre_coll = _sum_collateral(pre)
    res = _apply_result(state=state, tx_sender_pubkey=operator, operator_pubkey=operator, ops=[_op(market_id, "apply_funding_auto")])
    assert res.ok is True, res.error
    eff = res.effects[0]
    assert eff["raw_projected_net_funding_quote"] == -10
    assert eff["funding_sink_delta_quote"] == -10
    m = res.state.perps.markets[market_id]  # type: ignore[union-attr]
    fee, inc, ins = _sink(m)
    assert (fee, inc, ins) == (pre_fee - 10, pre_inc - 10, pre_ins - 10)
    assert fee == inc  # identity preserved
    # exact conservation: Δ(Σ collateral + fee_pool) == 0
    assert _sum_collateral(m) == pre_coll + 10
    assert _sum_collateral(m) + fee == pre_coll + pre_fee


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
    state = _with_oracle_snapshot(state, market_id=market_id, price_e8=100_000_000)
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

    # Hardening: liquidation penalty must stay positive.
    res_zero_penalty = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"liquidation_penalty_bps": 0})],
    )
    assert res_zero_penalty.ok is False
    assert res_zero_penalty.error is not None and "liquidation_penalty_bps > 0" in res_zero_penalty.error

    # Hardening: depeg buffer must remain positive (fail-closed against disabling buffer).
    res_zero_depeg = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"depeg_buffer_bps": 0})],
    )
    assert res_zero_depeg.ok is False
    assert res_zero_depeg.error is not None and "depeg_buffer_bps > 0" in res_zero_depeg.error

    # Hardening: penalty must remain funded after the worst configured oracle move.
    res_unfunded_liquidation = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"max_oracle_move_bps": 548})],
    )
    assert res_unfunded_liquidation.ok is False
    assert (
        res_unfunded_liquidation.error is not None
        and "funded liquidation" in res_unfunded_liquidation.error
    )

    # Hardening: while positions are open, do not allow increasing liquidation penalty.
    res_penalty_up = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "set_market_params", params={"liquidation_penalty_bps": 60})],
    )
    assert res_penalty_up.ok is False
    assert res_penalty_up.error is not None and "cannot increase liquidation_penalty_bps while positions are open" in res_penalty_up.error

    # Hardening: while positions are open, do not allow lowering bounty threshold.
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


def test_rust_shadow_unauthorized_settle_epoch_does_not_run_oracle_bridge_verifier() -> None:
    from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops

    market_id = "perp:shadow-settle-preauth"
    quote_asset = "0x" + "61" * 32
    operator = "00" * 48
    unauthorized_sender = "11" * 48
    state = _settle_ready_state(market_id=market_id, quote_asset=quote_asset, operator=operator)
    verifier_calls = 0

    def verifier(_bridge: object) -> dict[str, object]:
        nonlocal verifier_calls
        verifier_calls += 1
        return {"status": "accepted", "errors": []}

    set_active_authority_policy(_perp_stateful_policy(AuthorityMode.RUST_SHADOW))
    try:
        res = apply_perp_ops(
            config=PerpEngineConfig(
                operator_pubkey=operator,
                allow_isolated_markets=True,
                oracle_adapter_bridge_verifier=verifier,
            ),
            state=state,
            operations={
                "19": [_op(market_id, "settle_epoch", oracle_adapter_bridge={"schema": "test"})]
            },
            tx_sender_pubkey=unauthorized_sender,
            block_timestamp=0,
        )
    finally:
        reset_active_authority_policy()

    assert res.ok is False
    assert res.error == "operator only"
    assert verifier_calls == 0
