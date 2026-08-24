from __future__ import annotations

from collections.abc import Callable
from dataclasses import replace

import pytest

from src.core.dex import DexState
from src.core.perps import (
    PERPS_STATE_VERSION,
    PerpClearinghouse2pMarketState,
    PerpClearinghouse3pTransferMarketState,
    PerpsState,
)
from src.integration import perp_engine
from src.integration.perp_engine import (
    PerpEngineConfig,
    _isolated_settle_oracle_runtime_facts,
    apply_perp_ops,
)
from src.integration.zeno_oracle_authorization import (
    economic_envelope_hash,
    oracle_value_hash,
    semantic_hash,
)
from src.state.balances import BalanceTable
from src.state.lp import LPTable
from tests.integration.oracle_authorization_test_helpers import authorization_bundle

_FixedClearinghouseMarket = (
    PerpClearinghouse2pMarketState | PerpClearinghouse3pTransferMarketState
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


def _apply_result(
    *,
    state: DexState,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
    operator_pubkey: str,
    require_authorization: bool = False,
    receipt_graph_root: str | None = None,
):
    cfg = PerpEngineConfig(
        operator_pubkey=operator_pubkey,
        allow_isolated_markets=True,
        require_oracle_authorization_for_isolated_settle=require_authorization,
        oracle_authorization_receipt_graph_root=receipt_graph_root,
    )
    return apply_perp_ops(
        config=cfg,
        state=state,
        operations={"5": ops},
        tx_sender_pubkey=tx_sender_pubkey,
        block_timestamp=0,
    )


def _apply(
    *,
    state: DexState,
    tx_sender_pubkey: str,
    ops: list[dict[str, object]],
    operator_pubkey: str,
    require_authorization: bool = False,
) -> DexState:
    res = _apply_result(
        state=state,
        tx_sender_pubkey=tx_sender_pubkey,
        operator_pubkey=operator_pubkey,
        ops=ops,
        require_authorization=require_authorization,
    )
    assert res.ok is True, res.error
    assert res.state is not None
    return res.state


def _ready_market(*, market_id: str, operator: str, price_e8: int = 100_000_000) -> DexState:
    quote_asset = "0x" + "77" * 32
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
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=price_e8)],
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    assert hasattr(market, "global_state")
    market.global_state["oracle_seen"] = True
    market.global_state["oracle_last_update_epoch"] = max(0, int(market.global_state["now_epoch"]) - 1)
    market.global_state["index_price_e8"] = int(price_e8)
    return state


def _authorization_for(
    runtime: dict[str, object],
    *,
    observed_epoch: int,
    value_e8: int | None = None,
    evidence_class: str = "O3",
    expires_at_epoch: int | None = None,
    profile_id: str = "critical-perps-v1",
) -> dict[str, object]:
    value = int(runtime["runtime_value_e8"] if value_e8 is None else value_e8)
    query_id = str(runtime["query_id"])
    auth = {
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "action_id": str(runtime["action_id"]),
        "action_facts_hash": str(runtime["action_facts_hash"]),
        "pre_state_hash": str(runtime["pre_state_hash"]),
        "profile_id": profile_id,
        "query_id": query_id,
        "value_e8": value,
        "value_hash": oracle_value_hash(query_id=query_id, value_e8=value, observed_epoch=observed_epoch),
        "confidence_e8": 10_000,
        "deviation_bps": 5,
        "observed_epoch": int(observed_epoch),
        "expires_at_epoch": int(runtime["now_epoch"] if expires_at_epoch is None else expires_at_epoch),
        "feed_id": "feed:perps:index",
        "feed_registry_root": semantic_hash("test.feed-root", {"surface": "perps"}),
        "query_policy_root": semantic_hash("test.query-policy-root", {"surface": "perps"}),
        "source_registry_root": semantic_hash("test.source-root", {"surface": "perps"}),
        "reporter_registry_root": semantic_hash("test.reporter-root", {"surface": "perps"}),
        "evidence_class": evidence_class,
        "economic_envelope_id": "perps-critical-envelope",
        "receipt_graph_root": semantic_hash("test.receipt-graph-root", {"surface": "perps"}),
    }
    return authorization_bundle(auth)


def _ready_fixed_clearinghouse_market(
    market_kind: str,
) -> tuple[DexState, _FixedClearinghouseMarket, str, tuple[str, ...]]:
    quote_asset = "0x" + "88" * 32
    alice = "11" * 48
    bob = "22" * 48
    carol = "33" * 48
    if market_kind == "clearinghouse_2p_v1":
        market_id = "perp:ch2p:typed-oracle-admission"
        state = perp_engine._ch2p_init_state_dict()
        state, _ = perp_engine._ch2p_step(state, tag="advance_epoch", args={"delta": 1})
        state, _ = perp_engine._ch2p_step(
            state,
            tag="publish_clearing_price",
            args={"price_e8": 100_000_000},
        )
        participants = (alice, bob)
        market: _FixedClearinghouseMarket = PerpClearinghouse2pMarketState(
            quote_asset=quote_asset,
            account_a_pubkey=alice,
            account_b_pubkey=bob,
            state=state,
        )
    elif market_kind == "clearinghouse_3p_transfer_v1":
        market_id = "perp:ch3p:typed-oracle-admission"
        state = perp_engine._ch3p_init_state_dict()
        state, _ = perp_engine._ch3p_step(state, tag="advance_epoch", args={"delta": 1})
        state, _ = perp_engine._ch3p_step(
            state,
            tag="publish_clearing_price",
            args={"price_e8": 100_000_000},
        )
        participants = (alice, bob, carol)
        market = PerpClearinghouse3pTransferMarketState(
            quote_asset=quote_asset,
            account_a_pubkey=alice,
            account_b_pubkey=bob,
            account_c_pubkey=carol,
            state=state,
        )
    else:  # pragma: no cover - helper is called only by the closed parameter set.
        raise AssertionError(f"unsupported fixed clearinghouse kind: {market_kind}")

    return (
        DexState(
            balances=BalanceTable(),
            pools={},
            lp_balances=LPTable(),
            perps=PerpsState(version=PERPS_STATE_VERSION, markets={market_id: market}),
        ),
        market,
        market_id,
        participants,
    )


def _accepted_clearinghouse_bridge(
    *,
    runtime: dict[str, object],
    value_e8: int | None = None,
    action_epoch: int | None = None,
    aggregate_id: str | None = None,
) -> Callable[[object], dict[str, object]]:
    def verify(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": runtime["query_id"],
            "profile_id": perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": runtime["action_id"],
            "value_e8": runtime["runtime_value_e8"] if value_e8 is None else value_e8,
            "action_epoch": runtime["now_epoch"] if action_epoch is None else action_epoch,
            "aggregate_id": (
                semantic_hash("test.oracle.aggregate", {"query_id": runtime["query_id"]})
                if aggregate_id is None
                else aggregate_id
            ),
        }

    return verify


@pytest.mark.parametrize(
    "market_kind,version",
    [
        ("clearinghouse_2p_v1", "1.0"),
        ("clearinghouse_3p_transfer_v1", "1.1"),
    ],
)
def test_fixed_clearinghouse_settle_requires_typed_oracle_authorization(
    market_kind: str,
    version: str,
) -> None:
    # Arrange: each fixed clearinghouse has a valid, unsettled price, while the
    # release policy requires independent typed Oracle authorization.
    state, _market, market_id, _participants = _ready_fixed_clearinghouse_market(
        market_kind
    )
    config = PerpEngineConfig(
        operator_pubkey="00" * 48,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
    )

    # Act.
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={"5": [_op(market_id, "settle_epoch", version=version)]},
        tx_sender_pubkey="00" * 48,
        block_timestamp=0,
    )

    # Assert: rejection occurs before any settlement state or effects publish.
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "clearinghouse_settle_oracle_authorization_required"


@pytest.mark.parametrize(
    "market_kind,version",
    [
        ("clearinghouse_2p_v1", "1.0"),
        ("clearinghouse_3p_transfer_v1", "1.1"),
    ],
)
def test_fixed_clearinghouse_settle_accepts_exact_typed_oracle_admission(
    market_kind: str,
    version: str,
) -> None:
    # Arrange: derive the authorization and bridge from the exact mounted
    # market state, price, epoch, participants, and action identity.
    state, market, market_id, participants = _ready_fixed_clearinghouse_market(
        market_kind
    )
    base_config = PerpEngineConfig(operator_pubkey="00" * 48)
    runtime = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts(
        base_config,
        market_id=market_id,
        market_kind=market_kind,
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=participants,
    )
    authorization = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]),
        profile_id=perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    )
    config = PerpEngineConfig(
        operator_pubkey="00" * 48,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        oracle_adapter_bridge_verifier=_accepted_clearinghouse_bridge(runtime=runtime),
        oracle_authorization_receipt_graph_root=str(
            authorization["authorization"]["receipt_graph_root"]
        ),
    )

    # Act.
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_epoch",
                    version=version,
                    oracle_adapter_bridge={},
                    oracle_authorization=authorization,
                )
            ]
        },
        tx_sender_pubkey="00" * 48,
        block_timestamp=0,
    )

    # Assert.
    assert result.ok is True, result.error
    assert result.state is not None
    assert result.effects is not None


@pytest.mark.parametrize(
    "market_kind,version",
    [
        ("clearinghouse_2p_v1", "1.0"),
        ("clearinghouse_3p_transfer_v1", "1.1"),
    ],
)
def test_fixed_clearinghouse_settle_rejects_economically_invalid_envelope(
    market_kind: str,
    version: str,
) -> None:
    # Arrange: every identity and receipt binding is exact, while the economic
    # envelope makes corruption profitable by declaring zero attack cost and
    # zero slash deterrence for a positive extractable value.
    state, market, market_id, participants = _ready_fixed_clearinghouse_market(
        market_kind
    )
    base_config = PerpEngineConfig(operator_pubkey="00" * 48)
    runtime = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts(
        base_config,
        market_id=market_id,
        market_kind=market_kind,
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=participants,
    )
    authorization = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]),
        profile_id=perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    )
    envelope = authorization["economic_envelope"]
    auth = authorization["authorization"]
    assert type(envelope) is dict
    assert type(auth) is dict
    envelope["attack_cost_floor_e8"] = 0
    envelope["slash_fraction_bps"] = 0
    auth["economic_envelope_id"] = economic_envelope_hash(envelope)
    config = PerpEngineConfig(
        operator_pubkey="00" * 48,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        oracle_adapter_bridge_verifier=_accepted_clearinghouse_bridge(runtime=runtime),
        oracle_authorization_receipt_graph_root=str(auth["receipt_graph_root"]),
    )

    # Act.
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_epoch",
                    version=version,
                    oracle_adapter_bridge={},
                    oracle_authorization=authorization,
                )
            ]
        },
        tx_sender_pubkey="00" * 48,
        block_timestamp=0,
    )

    # Assert: a hash-consistent but economically unsafe envelope cannot move
    # collateral or publish effects.
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error is not None
    assert "attack_cost_floor_below_required_margin" in result.error
    assert "slash_deterrence_below_required_margin" in result.error


def test_fixed_clearinghouse_settle_rejects_understated_runtime_notional() -> None:
    # Arrange: create a matched one-base long/short position whose gross
    # settlement exposure is 220_000_000 quote-e8 at the published price.
    state, market, market_id, participants = _ready_fixed_clearinghouse_market(
        "clearinghouse_2p_v1"
    )
    market_state, _ = perp_engine._ch2p_step(
        market.state,
        tag="settle_epoch",
        args={},
    )
    for tag in ("deposit_collateral_a", "deposit_collateral_b"):
        market_state, _ = perp_engine._ch2p_step(
            market_state,
            tag=tag,
            args={"amount_e8": 100_000_000, "auth_ok": True},
        )
    market_state, _ = perp_engine._ch2p_step(
        market_state,
        tag="set_position_pair",
        args={"new_position_base_a": 1, "auth_ok": True},
    )
    market_state, _ = perp_engine._ch2p_step(
        market_state,
        tag="advance_epoch",
        args={"delta": 1},
    )
    market_state, _ = perp_engine._ch2p_step(
        market_state,
        tag="publish_clearing_price",
        args={"price_e8": 110_000_000},
    )
    market = replace(market, state=market_state)
    assert state.perps is not None
    state = replace(
        state,
        perps=replace(state.perps, markets={market_id: market}),
    )
    base_config = PerpEngineConfig(operator_pubkey="00" * 48)
    runtime = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts(
        base_config,
        market_id=market_id,
        market_kind="clearinghouse_2p_v1",
        quote_asset=market.quote_asset,
        state=market_state,
        participant_pubkeys=participants,
    )
    assert runtime["runtime_notional_value_e8"] == 220_000_000
    authorization = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]),
        profile_id=perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    )
    envelope = authorization["economic_envelope"]
    auth = authorization["authorization"]
    assert type(envelope) is dict
    assert type(auth) is dict
    envelope["notional_value_e8"] = 0
    envelope["max_extractable_value_e8"] = 0
    envelope["attack_cost_floor_e8"] = 0
    envelope["expected_cheat_gain_e8"] = 0
    auth["economic_envelope_id"] = economic_envelope_hash(envelope)
    config = PerpEngineConfig(
        operator_pubkey="00" * 48,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        oracle_adapter_bridge_verifier=_accepted_clearinghouse_bridge(runtime=runtime),
        oracle_authorization_receipt_graph_root=str(auth["receipt_graph_root"]),
    )

    # Act.
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_epoch",
                    version="1.0",
                    oracle_adapter_bridge={},
                    oracle_authorization=authorization,
                )
            ]
        },
        tx_sender_pubkey="00" * 48,
        block_timestamp=0,
    )

    # Assert: the accepted envelope must cover the runtime-derived gross
    # notional before collateral can move.
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error is not None
    assert "runtime_notional_value_e8 exceeds economic envelope" in result.error


@pytest.mark.parametrize(
    "market_kind,version",
    [
        ("clearinghouse_2p_v1", "1.0"),
        ("clearinghouse_3p_transfer_v1", "1.1"),
    ],
)
def test_fixed_clearinghouse_settle_rejects_caller_selected_receipt_root(
    market_kind: str,
    version: str,
) -> None:
    # Arrange: the caller supplies a self-consistent authorization bundle, but
    # the runtime policy has not selected its terminal receipt-graph root.
    state, market, market_id, participants = _ready_fixed_clearinghouse_market(
        market_kind
    )
    base_config = PerpEngineConfig(operator_pubkey="00" * 48)
    runtime = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts(
        base_config,
        market_id=market_id,
        market_kind=market_kind,
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=participants,
    )
    authorization = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]),
        profile_id=perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    )
    config = PerpEngineConfig(
        operator_pubkey="00" * 48,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        oracle_adapter_bridge_verifier=_accepted_clearinghouse_bridge(runtime=runtime),
    )

    # Act.
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_epoch",
                    version=version,
                    oracle_adapter_bridge={},
                    oracle_authorization=authorization,
                )
            ]
        },
        tx_sender_pubkey="00" * 48,
        block_timestamp=0,
    )

    # Assert.
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "clearinghouse_settle_oracle_authorization_root_authority_required"


@pytest.mark.parametrize(
    "market_kind,version",
    [
        ("clearinghouse_2p_v1", "1.0"),
        ("clearinghouse_3p_transfer_v1", "1.1"),
    ],
)
@pytest.mark.parametrize(
    "value_delta,epoch_delta,expected_error",
    [
        (1, 0, "oracle_adapter_bridge value_e8 mismatch"),
        (0, 1, "oracle_adapter_bridge action_epoch mismatch"),
    ],
)
def test_fixed_clearinghouse_settle_rejects_bridge_semantic_drift(
    market_kind: str,
    version: str,
    value_delta: int,
    epoch_delta: int,
    expected_error: str,
) -> None:
    # Arrange: authorization is exact while the independently verified bridge
    # is accepted for a neighboring price or epoch.
    state, market, market_id, participants = _ready_fixed_clearinghouse_market(
        market_kind
    )
    base_config = PerpEngineConfig(operator_pubkey="00" * 48)
    runtime = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts(
        base_config,
        market_id=market_id,
        market_kind=market_kind,
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=participants,
    )
    authorization = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]),
        profile_id=perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    )
    config = PerpEngineConfig(
        operator_pubkey="00" * 48,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        oracle_adapter_bridge_verifier=_accepted_clearinghouse_bridge(
            runtime=runtime,
            value_e8=int(runtime["runtime_value_e8"]) + value_delta,
            action_epoch=int(runtime["now_epoch"]) + epoch_delta,
        ),
        oracle_authorization_receipt_graph_root=str(
            authorization["authorization"]["receipt_graph_root"]
        ),
    )

    # Act.
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_epoch",
                    version=version,
                    oracle_adapter_bridge={},
                    oracle_authorization=authorization,
                )
            ]
        },
        tx_sender_pubkey="00" * 48,
        block_timestamp=0,
    )

    # Assert.
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == expected_error


@pytest.mark.parametrize(
    "market_kind,version",
    [
        ("clearinghouse_2p_v1", "1.0"),
        ("clearinghouse_3p_transfer_v1", "1.1"),
    ],
)
def test_fixed_clearinghouse_settle_rejects_bridge_from_different_oracle_occurrence(
    market_kind: str,
    version: str,
) -> None:
    # Arrange: both artifacts are independently valid for the same action,
    # value, and epoch, but they close over different Oracle aggregates.
    state, market, market_id, participants = _ready_fixed_clearinghouse_market(
        market_kind
    )
    base_config = PerpEngineConfig(operator_pubkey="00" * 48)
    runtime = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts(
        base_config,
        market_id=market_id,
        market_kind=market_kind,
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=participants,
    )
    authorization = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]),
        profile_id=perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    )
    config = PerpEngineConfig(
        operator_pubkey="00" * 48,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        oracle_adapter_bridge_verifier=_accepted_clearinghouse_bridge(
            runtime=runtime,
            aggregate_id=semantic_hash(
                "test.oracle.aggregate",
                {"query_id": runtime["query_id"], "occurrence": "different"},
            ),
        ),
        oracle_authorization_receipt_graph_root=str(
            authorization["authorization"]["receipt_graph_root"]
        ),
    )

    # Act.
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_epoch",
                    version=version,
                    oracle_adapter_bridge={},
                    oracle_authorization=authorization,
                )
            ]
        },
        tx_sender_pubkey="00" * 48,
        block_timestamp=0,
    )

    # Assert: composition must fail closed without a partial settlement.
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == "oracle_adapter_bridge aggregate_id mismatch"


def test_clearinghouse_settle_commits_owned_state_snapshot_across_bridge_callback() -> None:
    # Arrange: model a faulty in-process verifier that mutates a captured
    # caller-owned market after runtime authorization has been derived.
    state, market, market_id, participants = _ready_fixed_clearinghouse_market(
        "clearinghouse_2p_v1"
    )
    base_config = PerpEngineConfig(operator_pubkey="00" * 48)
    runtime = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts(
        base_config,
        market_id=market_id,
        market_kind="clearinghouse_2p_v1",
        quote_asset=market.quote_asset,
        state=market.state,
        participant_pubkeys=participants,
    )
    authorization = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]),
        profile_id=perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    )
    accepted_bridge = _accepted_clearinghouse_bridge(runtime=runtime)

    def mutating_verifier(bridge: object) -> dict[str, object]:
        market.state["clearing_price_e8"] = int(runtime["runtime_value_e8"]) + 1
        return accepted_bridge(bridge)

    config = PerpEngineConfig(
        operator_pubkey="00" * 48,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        oracle_adapter_bridge_verifier=mutating_verifier,
        oracle_authorization_receipt_graph_root=str(
            authorization["authorization"]["receipt_graph_root"]
        ),
    )

    # Act.
    result = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "settle_epoch",
                    version="1.0",
                    oracle_adapter_bridge={},
                    oracle_authorization=authorization,
                )
            ]
        },
        tx_sender_pubkey="00" * 48,
        block_timestamp=0,
    )

    # Assert: the published result consumes the same owned snapshot that was
    # authorized, regardless of mutation to an external alias.
    assert result.ok is True, result.error
    assert result.state is not None
    assert result.state.perps is not None
    result_market = result.state.perps.markets[market_id]
    assert isinstance(result_market, PerpClearinghouse2pMarketState)
    assert result_market.state["clearing_price_e8"] == runtime["runtime_value_e8"]


def test_isolated_settle_requires_oracle_authorization_when_configured() -> None:
    market_id = "perp:auth-required"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch")],
    )

    assert res.ok is False
    assert res.error == "oracle_authorization_required"


def test_isolated_settle_rejects_caller_selected_terminal_receipt_graph_root() -> None:
    # Arrange: the payload is internally consistent, but no verifier-selected
    # receipt graph root is installed in the runtime configuration.
    market_id = "perp:auth-ok"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))

    # Act.
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    # Assert: a self-consistent caller-selected graph carries no independent
    # authority and cannot move the market to its settled state.
    assert res.ok is False
    assert res.state is None
    assert res.effects is None
    assert res.error == "oracle_authorization_root_authority_required"


def test_isolated_settle_accepts_configured_terminal_receipt_graph_root() -> None:
    # Arrange.
    market_id = "perp:auth-configured-root"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))
    configured_root = str(auth["authorization"]["receipt_graph_root"])

    # Act.
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=configured_root,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    # Assert.
    assert res.ok is True, res.error


def test_isolated_settle_rejects_different_configured_terminal_receipt_graph_root() -> None:
    # Arrange.
    market_id = "perp:auth-wrong-configured-root"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))
    wrong_root = semantic_hash("test.wrong-configured-root", {"market_id": market_id})

    # Act.
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=wrong_root,
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    # Assert: policy-selected root mismatch closes settlement before mutation.
    assert res.ok is False
    assert res.state is None
    assert res.effects is None
    assert res.error is not None
    assert "receipt_graph_root does not match configured root" in res.error


def test_isolated_settle_rejects_authorization_for_different_oracle_value() -> None:
    market_id = "perp:auth-value-mismatch"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(
        runtime,
        observed_epoch=int(market.global_state["oracle_last_update_epoch"]),
        value_e8=int(runtime["runtime_value_e8"]) + 1,
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(auth["authorization"]["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "runtime_value_e8 mismatch" in res.error


def test_isolated_settle_rejects_authorization_bound_to_previous_index_price() -> None:
    # Arrange: settlement will consume the newly published 95 price while the
    # prior index remains 100. The action and pre-state hashes bind both values,
    # so a self-consistent bundle can still carry the wrong price occurrence.
    market_id = "perp:auth-prior-index"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator, price_e8=100_000_000)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    market.global_state["clearing_price_e8"] = 95_000_000
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    assert market.global_state["index_price_e8"] == 100_000_000
    assert runtime["runtime_value_e8"] == 95_000_000
    auth = _authorization_for(
        runtime,
        observed_epoch=int(market.global_state["oracle_last_update_epoch"]),
        value_e8=int(market.global_state["index_price_e8"]),
    )

    # Act.
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(auth["authorization"]["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    # Assert: authorization for the previous index cannot authorize effects at
    # the newly published clearing price.
    assert res.ok is False
    assert res.state is None
    assert res.effects is None
    assert res.error is not None
    assert "runtime_value_e8 mismatch" in res.error


def test_isolated_settle_rejects_understated_runtime_notional() -> None:
    # Arrange: build a reachable matched one-base long/short market, then submit
    # a hash-consistent envelope that declares zero settlement exposure.
    market_id = "perp:auth-isolated-notional"
    operator = "00" * 48
    alice = "11" * 48
    bob = "22" * 48
    state = _ready_market(market_id=market_id, operator=operator, price_e8=100_000_000)
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "settle_epoch"), _op(market_id, "advance_epoch", delta=1)],
    )
    assert state.perps is not None
    quote_asset = state.perps.markets[market_id].quote_asset
    funded = BalanceTable()
    for (pubkey, asset), amount in state.balances.get_all_balances().items():
        funded.set(pubkey, asset, int(amount))
    funded.set(alice, quote_asset, 1_000)
    funded.set(bob, quote_asset, 1_000)
    state = replace(state, balances=funded)
    state = _apply(
        state=state,
        tx_sender_pubkey=alice,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=alice, amount=100),
            _op(market_id, "set_position", account_pubkey=alice, new_position_base=1),
        ],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=bob,
        operator_pubkey=operator,
        ops=[
            _op(market_id, "deposit_collateral", account_pubkey=bob, amount=100),
            _op(market_id, "set_position", account_pubkey=bob, new_position_base=-1),
        ],
    )
    state = _apply(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        ops=[_op(market_id, "publish_clearing_price", price_e8=100_000_000)],
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    # One base-e8 atom on each side at a 1.0 quote price is one quote-e8 atom
    # per account. This catches accidental reuse of the unscaled 2P/3P/NP unit
    # convention on the isolated market family.
    assert runtime["runtime_notional_value_e8"] == 2
    auth = _authorization_for(
        runtime,
        observed_epoch=int(market.global_state["oracle_last_update_epoch"]),
    )
    envelope = auth["economic_envelope"]
    authorization = auth["authorization"]
    assert type(envelope) is dict
    assert type(authorization) is dict
    envelope["notional_value_e8"] = 0
    envelope["max_extractable_value_e8"] = 0
    envelope["attack_cost_floor_e8"] = 0
    envelope["expected_cheat_gain_e8"] = 0
    authorization["economic_envelope_id"] = economic_envelope_hash(envelope)

    # Act.
    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(authorization["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    # Assert: the runtime-derived exposure must fit the economic envelope before
    # settlement can move collateral or emit effects.
    assert res.ok is False
    assert res.state is None
    assert res.effects is None
    assert res.error is not None
    assert "runtime_notional_value_e8 exceeds economic envelope" in res.error


def test_isolated_settle_rejects_malformed_runtime_facts(monkeypatch) -> None:
    import src.integration.perp_engine as perp_engine

    market_id = "perp:auth-malformed-runtime"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))

    def malformed_runtime_facts(*, market_id: str, market) -> dict[str, object]:
        facts = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
        facts["runtime_value_e8"] = True
        facts["now_epoch"] = False
        return facts

    monkeypatch.setattr(perp_engine, "_isolated_settle_oracle_runtime_facts", malformed_runtime_facts)

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(auth["authorization"]["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error == "oracle_authorization_rejected: malformed runtime facts"


def test_isolated_settle_sanitizes_oracle_verifier_internal_error(monkeypatch) -> None:
    import src.integration.perp_engine as perp_engine

    market_id = "perp:auth-verifier-bug"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))

    def broken_verifier(*args: object, **kwargs: object) -> dict[str, object]:
        raise RuntimeError("oracle verifier implementation bug")

    monkeypatch.setattr(perp_engine, "check_critical_consumer_authorization", broken_verifier)

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(auth["authorization"]["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error == "oracle_authorization_rejected: internal error: RuntimeError"


def test_clearinghouse_settle_sanitizes_oracle_verifier_internal_error(monkeypatch) -> None:
    import src.integration.perp_engine as perp_engine

    def broken_verifier(*args: object, **kwargs: object) -> dict[str, object]:
        raise RuntimeError("clearinghouse oracle verifier implementation bug")

    monkeypatch.setattr(perp_engine, "check_critical_consumer_authorization", broken_verifier)

    err = perp_engine._check_clearinghouse_settle_oracle_authorization(
        perp_engine._ClearinghouseSettleOracleAuthorizationRequest(
            config=perp_engine.PerpEngineConfig(),
            data={"oracle_authorization": {"present": True}},
            market_id="perp:ch2p:auth-verifier-bug",
            market_kind="clearinghouse_2p_v1",
            quote_asset="zUSD",
            state={
                "now_epoch": 1,
                "clearing_price_epoch": 1,
                "clearing_price_e8": 100_000_000,
                "index_price_e8": 100_000_000,
                "oracle_last_update_epoch": 1,
                "position_base_a": 0,
                "position_base_b": 0,
            },
            participant_pubkeys=("00" * 48, "11" * 48),
        )
    )

    assert err == "clearinghouse_settle_oracle_authorization_rejected: internal error: RuntimeError"


def test_isolated_settle_rejects_authorization_for_different_pre_state() -> None:
    market_id = "perp:auth-pre-state-mismatch"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(runtime, observed_epoch=int(market.global_state["oracle_last_update_epoch"]))
    auth["authorization"]["pre_state_hash"] = semantic_hash("test.wrong-pre-state", {"market_id": market_id})

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(auth["authorization"]["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "pre_state_hash mismatch" in res.error


def test_isolated_settle_rejects_below_o3_authorization_evidence() -> None:
    market_id = "perp:auth-evidence-floor"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(
        runtime,
        observed_epoch=int(market.global_state["oracle_last_update_epoch"]),
        evidence_class="O2",
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(auth["authorization"]["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "evidence_class below required O3" in res.error


def test_isolated_settle_rejects_expired_authorization() -> None:
    market_id = "perp:auth-expired"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    observed_epoch = int(market.global_state["oracle_last_update_epoch"])
    auth = _authorization_for(
        runtime,
        observed_epoch=observed_epoch,
        expires_at_epoch=observed_epoch,
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(auth["authorization"]["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "authorization expired" in res.error


def test_isolated_settle_rejects_stale_but_unexpired_authorization() -> None:
    market_id = "perp:auth-stale-window"
    operator = "00" * 48
    state = _ready_market(market_id=market_id, operator=operator)
    assert state.perps is not None
    market = state.perps.markets[market_id]
    runtime = _isolated_settle_oracle_runtime_facts(market_id=market_id, market=market)
    auth = _authorization_for(
        runtime,
        observed_epoch=int(runtime["now_epoch"]) - 3,
        expires_at_epoch=int(runtime["now_epoch"]),
    )

    res = _apply_result(
        state=state,
        tx_sender_pubkey=operator,
        operator_pubkey=operator,
        require_authorization=True,
        receipt_graph_root=str(auth["authorization"]["receipt_graph_root"]),
        ops=[_op(market_id, "settle_epoch", oracle_authorization=auth)],
    )

    assert res.ok is False
    assert res.error is not None
    assert "authorization observed_epoch outside runtime freshness window" in res.error
