from __future__ import annotations

from src.integration import perp_engine
from src.integration.perp_engine import PerpEngineConfig
from tools.zenodex_oracle_aggregate_adapter import AggregateAdapterResult


def test_strict_binding_accepts_real_adapter_result_with_matching_value_hash() -> None:
    authorization = {
        "authorization": {
            "value_hash": "0x" + "11" * 32,
            "observed_epoch": 7,
            "expires_at_epoch": 9,
            "receipt_graph_root": "0x" + "22" * 32,
        }
    }
    bridge_result = AggregateAdapterResult(
        status="accepted",
        errors=[],
        value_hash="0x" + "11" * 32,
    )

    assert (
        perp_engine._bind_clearinghouse_authorization_to_bridge(
            authorization,
            bridge_result=bridge_result,
        )
        is None
    )


def test_np_settlement_threads_verified_bridge_result_to_authorization(monkeypatch) -> None:
    market_id = "perp:np:bridge-binding"
    account = perp_engine._np_core.Account(pubkey="0x" + "11" * 48)
    market = perp_engine._chnp_core_to_market(
        "0x" + "22" * 32,
        perp_engine._np_core.MarketState(
            index_price_e8=100_000_000,
            params=perp_engine._np_core.MarketParams(),
            accounts=(account,),
        ),
    )
    state_for_oracle = market.global_state
    expected_action_id = perp_engine._perps_clearinghouse_runtime_oracle_action_id(
        PerpEngineConfig(),
        market_id=market_id,
        action_kind="settle_epoch",
        market_kind=perp_engine.PERP_MARKET_KIND_CLEARINGHOUSE_NP_V1,
        quote_asset=market.quote_asset,
        state=state_for_oracle,
        participant_pubkeys=(account.pubkey,),
    )
    verified_result = {
        "status": "accepted",
        "errors": [],
        "consumer_module": "zenodex.perps",
        "action_kind": "settle_epoch",
        "query_id": perp_engine._ORACLE_PERPS_INDEX_QUERY_ID,
        "profile_id": perp_engine._ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
        "action_id": expected_action_id,
        "value_hash": "0x" + "33" * 32,
    }
    config = PerpEngineConfig(
        oracle_adapter_bridge_verifier=lambda _bridge: verified_result,
        require_oracle_adapter_for_clearinghouse_settle_epoch=True,
    )
    observed: dict[str, object] = {}

    def _capture_authorization(*_args, **kwargs):
        observed["bridge_result"] = kwargs["bridge_result"]
        return None

    monkeypatch.setattr(perp_engine, "_check_clearinghouse_settle_oracle_authorization", _capture_authorization)

    error = perp_engine._chnp_settle_oracle_bridge_error(
        config,
        data={"oracle_adapter_bridge": {"schema": "test"}},
        market_id=market_id,
        market=market,
        state_for_oracle=state_for_oracle,
    )

    assert error is None
    assert observed["bridge_result"] is verified_result
