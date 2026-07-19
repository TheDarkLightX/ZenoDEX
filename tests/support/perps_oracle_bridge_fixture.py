"""Synthetic perps Oracle bridges for tests only.

The production wallet API accepts and inspects caller-supplied Oracle evidence,
but it must never synthesize evidence. Tests that need a deterministic bridge
build it here, outside ``src`` and outside every production image.
"""

from __future__ import annotations

from typing import Any, Mapping

from src.core.dex import DexState
from src.core.perps import PerpClearinghouse2pMarketState, PerpMarketState
from src.integration.perp_engine import (
    _ORACLE_PERPS_INDEX_QUERY_ID,
    _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID,
    _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    PerpEngineConfig,
    _LiquidateAccountOracleRuntimeRequest,
    _perps_clearinghouse_runtime_oracle_action_id,
    _perps_liquidate_account_runtime_oracle_action_id,
)
from tools.zenodex_oracle import ACTION_TYPE, receipt_content_hash
from tools.zenodex_oracle_adapter import ACTION_SCHEMA, PROFILE_SCHEMA, profile_content_hash
from tools.zenodex_oracle_admitted_median3 import (
    sample_admitted_median3_aggregate,
    verify_admitted_median3_aggregate,
)
from tools.zenodex_oracle_aggregate_adapter import (
    AGGREGATE_ADAPTER_SCHEMA,
    aggregate_adapter_content_hash,
    verify_aggregate_adapter_bridge,
)
from tools.zenodex_oracle_aggregate_read import (
    AGGREGATE_READ_SCHEMA,
    _bundle_for_aggregate,
    aggregate_read_value_hash,
)
from tools.zenodex_oracle_aggregate_read import (
    bridge_content_hash as aggregate_read_content_hash,
)


def build_perps_oracle_bridge_fixture(
    *,
    state: DexState,
    config: PerpEngineConfig,
    market_id: str,
    action: str,
    account_pubkey: str | None = None,
    fraction_bps: int = 0,
) -> dict[str, Any]:
    """Build deterministic, non-authoritative Oracle evidence for a test."""
    if state.perps is None:
        raise ValueError("missing_perps_state")
    market = state.perps.get_market(market_id)
    if action == "settle_epoch":
        if not isinstance(market, PerpClearinghouse2pMarketState):
            raise ValueError("settle_epoch oracle bridge fixture requires clearinghouse_2p")
        action_kind = "settle_epoch"
        profile_id = _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID
        freshness_window_epochs = 2
        action_id = _perps_clearinghouse_runtime_oracle_action_id(
            config,
            market_id=market_id,
            action_kind=action_kind,
            market_kind="clearinghouse_2p_v1",
            quote_asset=market.quote_asset,
            state=market.state,
            participant_pubkeys=(market.account_a_pubkey, market.account_b_pubkey),
        )
    elif action == "partial_liquidate":
        if not isinstance(market, PerpMarketState):
            raise ValueError("partial_liquidate oracle bridge fixture requires isolated market")
        if account_pubkey is None:
            raise ValueError("missing_account_pubkey")
        action_kind = "liquidate_account"
        profile_id = _ORACLE_PERPS_LIQUIDATE_ACCOUNT_PROFILE_ID
        freshness_window_epochs = 1
        action_id = _perps_liquidate_account_runtime_oracle_action_id(
            _LiquidateAccountOracleRuntimeRequest(
                config=config,
                market_id=market_id,
                market=market,
                account_pubkey=account_pubkey,
                fraction_bps=fraction_bps,
            )
        )
    else:
        raise ValueError("unsupported_oracle_bridge_action")

    aggregate = sample_admitted_median3_aggregate()
    aggregate_result = verify_admitted_median3_aggregate(aggregate)
    if aggregate_result.status != "accepted":
        raise ValueError("local oracle aggregate fixture rejected")
    if aggregate_result.query_id != _ORACLE_PERPS_INDEX_QUERY_ID:
        raise ValueError("local oracle aggregate fixture query mismatch")

    value_hash = aggregate_read_value_hash(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=str(aggregate_result.query_id),
        value_e8=int(aggregate_result.value_e8),
        confidence_e8=int(aggregate_result.confidence_e8),
        deviation_bps=int(aggregate_result.deviation_bps),
        observed_epoch=int(aggregate_result.observed_epoch),
        report_count=int(aggregate_result.report_count),
        admission_count=int(aggregate_result.admission_count),
    )
    bundle = _bundle_for_aggregate(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=str(aggregate_result.query_id),
        value_hash=value_hash,
        observed_epoch=int(aggregate_result.observed_epoch),
        freshness_window_epochs=freshness_window_epochs,
    )
    read_receipt_id = str(bundle["terminal"]["read_receipt_id"])
    read_receipt = next(
        receipt
        for receipt in bundle["receipts"]
        if isinstance(receipt, Mapping) and receipt.get("id") == read_receipt_id
    )
    action_epoch = int(aggregate_result.observed_epoch) + 1
    action_receipt: dict[str, Any] = {
        "type": ACTION_TYPE,
        "status": "accepted",
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "action_id": action_id,
        "action_epoch": action_epoch,
        "freshness_window_epochs": freshness_window_epochs,
        "query_id": str(aggregate_result.query_id),
        "value_hash": value_hash,
        "read_receipt_id": read_receipt_id,
        "critical": True,
        "emergency_oracle_bypass": False,
        "depends_on": [read_receipt_id],
    }
    action_receipt["id"] = receipt_content_hash(action_receipt)
    bundle["receipts"] = [dict(read_receipt), action_receipt]
    bundle["terminal"]["consumer_action_receipt_id"] = action_receipt["id"]

    aggregate_read: dict[str, Any] = {
        "schema": AGGREGATE_READ_SCHEMA,
        "freshness_window_epochs": freshness_window_epochs,
        "aggregate": dict(aggregate),
        "receipt_bundle": bundle,
    }
    aggregate_read["bridge_id"] = aggregate_read_content_hash(aggregate_read)

    adapter_action = {
        "schema": ACTION_SCHEMA,
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "action_id": action_id,
        "action_epoch": action_epoch,
        "query_id": str(aggregate_result.query_id),
        "value_hash": value_hash,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": freshness_window_epochs,
        "read_receipt_id": read_receipt_id,
        "consumer_action_receipt_id": action_receipt["id"],
        "critical": True,
    }
    profile = {
        "schema": PROFILE_SCHEMA,
        "consumer_module": "zenodex.perps",
        "action_kind": action_kind,
        "query_id": str(aggregate_result.query_id),
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": freshness_window_epochs,
        "critical": True,
    }
    profile["profile_id"] = profile_content_hash(profile)
    if profile["profile_id"] != profile_id:
        raise ValueError("local oracle profile fixture mismatch")

    bridge = {
        "schema": AGGREGATE_ADAPTER_SCHEMA,
        "aggregate_read": aggregate_read,
        "action": adapter_action,
        "profile": profile,
    }
    bridge["bridge_id"] = aggregate_adapter_content_hash(bridge)
    verify_result = verify_aggregate_adapter_bridge(bridge).to_json_obj()
    if verify_result.get("status") != "accepted":
        raise ValueError(f"local oracle bridge fixture rejected: {verify_result.get('errors')}")
    return {
        "schema": "zenodex.tests.perps_oracle_bridge_fixture.v1",
        "ok": True,
        "fixture_kind": "test_only_o3_aggregate_adapter",
        "production_authority": False,
        "market_id": market_id,
        "action": action,
        "target": {
            "query_id": _ORACLE_PERPS_INDEX_QUERY_ID,
            "profile_id": profile_id,
            "action_id": action_id,
            "consumer_module": "zenodex.perps",
            "action_kind": action_kind,
            "wallet_action": action,
        },
        "bridge": bridge,
        "verify_result": verify_result,
    }
