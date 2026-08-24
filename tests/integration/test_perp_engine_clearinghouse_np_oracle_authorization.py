from __future__ import annotations

import pytest

from src.core.dex import DexState
from src.integration import perp_engine
from src.integration.perp_engine import PerpEngineConfig, apply_perp_ops
from src.state.balances import BalanceTable
from src.state.lp import LPTable


def _op(market_id: str, action: str, **kwargs: object) -> dict[str, object]:
    op: dict[str, object] = {
        "module": "TauPerp",
        "version": "1.2",
        "market_id": market_id,
        "action": action,
    }
    op.update(kwargs)
    return op


def _ready_np_market(*, market_id: str, operator: str, quote_asset: str) -> DexState:
    state = DexState(balances=BalanceTable(), pools={}, lp_balances=LPTable())
    res = apply_perp_ops(
        config=PerpEngineConfig(operator_pubkey=operator),
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "init_market_np",
                    quote_asset=quote_asset,
                    index_price_e8=100_000_000,
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )
    assert res.ok is True, res.error
    assert res.state is not None and res.state.perps is not None
    market = res.state.perps.markets[market_id]
    market.global_state["clearing_price_seen"] = 1
    market.global_state["clearing_price_epoch"] = int(market.global_state["now_epoch"])
    market.global_state["clearing_price_e8"] = 100_000_000
    return res.state


def test_clearinghouse_np_rejects_malformed_runtime_facts(monkeypatch) -> None:
    market_id = "perp:chnp:auth-malformed-runtime"
    quote_asset = "0x" + "9a" * 32
    operator = "00" * 48
    state = _ready_np_market(market_id=market_id, operator=operator, quote_asset=quote_asset)
    assert state.perps is not None
    market = state.perps.markets[market_id]

    def accepted_bridge(_bridge: object) -> dict[str, object]:
        participant_pubkeys = perp_engine._chnp_participant_pubkeys(market)
        action_id = perp_engine._perps_clearinghouse_runtime_oracle_action_id(
            perp_engine._ClearinghouseOracleRuntimeRequest(
                config=config,
                market_id=market_id,
                action_kind="settle_epoch",
                market_kind=perp_engine.PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
                quote_asset=market.quote_asset,
                state=dict(market.global_state),
                participant_pubkeys=participant_pubkeys,
            )
        )
        return {
            "status": "accepted",
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": perp_engine._ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": action_id,
        }

    config = PerpEngineConfig(
        operator_pubkey=operator,
        require_oracle_authorization_for_clearinghouse_settle_epoch=True,
        oracle_adapter_bridge_verifier=accepted_bridge,
        oracle_authorization_receipt_graph_root="sha256:" + "11" * 32,
    )
    original_runtime_facts = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts

    def malformed_runtime_facts(config: PerpEngineConfig, **kwargs: object) -> dict[str, object]:
        facts = original_runtime_facts(config, **kwargs)
        facts["runtime_value_e8"] = True
        facts["now_epoch"] = False
        return facts

    monkeypatch.setattr(perp_engine, "_perps_clearinghouse_settle_oracle_runtime_facts", malformed_runtime_facts)

    res = apply_perp_ops(
        config=config,
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "run_epoch",
                    oracle_adapter_bridge={},
                    oracle_authorization={},
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )

    assert res.ok is False
    assert res.error == "clearinghouse_settle_oracle_authorization_rejected: malformed runtime facts"


@pytest.mark.parametrize(
    "value_delta,epoch_delta,expected_error",
    [
        (1, 0, "oracle_adapter_bridge value_e8 mismatch"),
        (0, 1, "oracle_adapter_bridge action_epoch mismatch"),
    ],
)
def test_clearinghouse_np_rejects_oracle_bridge_semantic_drift(
    value_delta: int,
    epoch_delta: int,
    expected_error: str,
) -> None:
    # Arrange: the bridge is accepted for the exact NP action identity while
    # carrying a neighboring clearing price or epoch.
    market_id = "perp:chnp:oracle-semantic-drift"
    quote_asset = "0x" + "9b" * 32
    operator = "00" * 48
    state = _ready_np_market(
        market_id=market_id,
        operator=operator,
        quote_asset=quote_asset,
    )
    assert state.perps is not None
    market = state.perps.markets[market_id]
    base_config = PerpEngineConfig(operator_pubkey=operator)
    participant_pubkeys = perp_engine._chnp_participant_pubkeys(market)
    runtime = perp_engine._perps_clearinghouse_settle_oracle_runtime_facts(
        base_config,
        market_id=market_id,
        market_kind=perp_engine.PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
        quote_asset=market.quote_asset,
        state=dict(market.global_state),
        participant_pubkeys=participant_pubkeys,
    )

    def accepted_neighboring_bridge(_bridge: object) -> dict[str, object]:
        return {
            "status": "accepted",
            "consumer_module": "zenodex.perps",
            "action_kind": "settle_epoch",
            "query_id": perp_engine._ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
            "action_id": runtime["action_id"],
            "value_e8": int(runtime["runtime_value_e8"]) + value_delta,
            "action_epoch": int(runtime["now_epoch"]) + epoch_delta,
        }

    # Act.
    result = apply_perp_ops(
        config=PerpEngineConfig(
            operator_pubkey=operator,
            require_oracle_adapter_for_clearinghouse_settle_epoch=True,
            oracle_adapter_bridge_verifier=accepted_neighboring_bridge,
        ),
        state=state,
        operations={
            "5": [
                _op(
                    market_id,
                    "run_epoch",
                    oracle_adapter_bridge={},
                )
            ]
        },
        tx_sender_pubkey=operator,
        block_timestamp=0,
    )

    # Assert.
    assert result.ok is False
    assert result.state is None
    assert result.effects is None
    assert result.error == expected_error
