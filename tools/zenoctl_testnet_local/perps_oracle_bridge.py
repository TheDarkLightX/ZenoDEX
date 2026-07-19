"""Local-testnet-only ZenoOracle bridge construction for perps smoke runs.

This module is part of the operator tooling, not the production HTTP surface.
It binds deterministic O3 replay evidence to a live clearinghouse market
snapshot so local lifecycle checks can exercise the same verifier boundary
without asking a production handler to manufacture evidence.
"""

from __future__ import annotations

from typing import Any, Mapping

from src.integration.perp_engine import (
    _ORACLE_PERPS_INDEX_QUERY_ID,
    _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID,
    PerpEngineConfig,
    _perps_clearinghouse_runtime_oracle_action_id,
)
from tools.zenodex_oracle import ACTION_TYPE, receipt_content_hash
from tools.zenodex_oracle_adapter import (
    ACTION_SCHEMA,
    PROFILE_SCHEMA,
    profile_content_hash,
)
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

_MARKET_KIND = "clearinghouse_2p_v1"
_ACTION_KIND = "settle_epoch"
_FRESHNESS_WINDOW_EPOCHS = 2


def _required_text(value: object, *, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"{label} must be a non-empty string")
    return value


def _market_state_from_summary(market: Mapping[str, Any]) -> dict[str, int]:
    state: dict[str, int] = {}
    for field in (
        "now_epoch",
        "clearing_price_epoch",
        "clearing_price_e8",
        "index_price_e8",
        "oracle_last_update_epoch",
    ):
        value = market.get(field)
        if not isinstance(value, int) or isinstance(value, bool) or value < 0:
            raise ValueError(f"market.{field} must be a non-negative integer")
        state[field] = int(value)
    return state


def build_local_settle_epoch_bridge(
    *,
    chain_id: str,
    market: Mapping[str, Any],
) -> dict[str, Any]:
    """Build verified, non-production O3 evidence for one live market snapshot."""

    chain_id = _required_text(chain_id, label="chain_id")
    market_id = _required_text(market.get("market_id"), label="market.market_id")
    market_kind = _required_text(market.get("kind"), label="market.kind")
    if market_kind != _MARKET_KIND:
        raise ValueError(f"unsupported local perps market kind: {market_kind}")
    quote_asset = _required_text(market.get("quote_asset"), label="market.quote_asset")
    participant_pubkeys = (
        _required_text(market.get("account_a_pubkey"), label="market.account_a_pubkey"),
        _required_text(market.get("account_b_pubkey"), label="market.account_b_pubkey"),
    )
    state = _market_state_from_summary(market)
    action_id = _perps_clearinghouse_runtime_oracle_action_id(
        PerpEngineConfig(chain_id=chain_id),
        market_id=market_id,
        action_kind=_ACTION_KIND,
        market_kind=market_kind,
        quote_asset=quote_asset,
        state=state,
        participant_pubkeys=participant_pubkeys,
    )

    aggregate = sample_admitted_median3_aggregate()
    aggregate_result = verify_admitted_median3_aggregate(aggregate)
    if aggregate_result.status != "accepted":
        raise ValueError("local oracle aggregate fixture rejected")
    if aggregate_result.query_id is None:
        raise ValueError("local oracle aggregate fixture has no query id")

    query_id = str(aggregate_result.query_id)
    if query_id != _ORACLE_PERPS_INDEX_QUERY_ID:
        raise ValueError("local oracle aggregate fixture query mismatch")
    value_hash = aggregate_read_value_hash(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=query_id,
        value_e8=int(aggregate_result.value_e8),
        confidence_e8=int(aggregate_result.confidence_e8),
        deviation_bps=int(aggregate_result.deviation_bps),
        observed_epoch=int(aggregate_result.observed_epoch),
        report_count=int(aggregate_result.report_count),
        admission_count=int(aggregate_result.admission_count),
    )
    bundle = _bundle_for_aggregate(
        aggregate_id=str(aggregate_result.aggregate_id),
        query_id=query_id,
        value_hash=value_hash,
        observed_epoch=int(aggregate_result.observed_epoch),
        freshness_window_epochs=_FRESHNESS_WINDOW_EPOCHS,
    )
    read_receipt_id = str(bundle["terminal"]["read_receipt_id"])
    read_receipt = next(
        receipt
        for receipt in bundle["receipts"]
        if isinstance(receipt, Mapping) and receipt.get("id") == read_receipt_id
    )
    action_receipt: dict[str, Any] = {
        "type": ACTION_TYPE,
        "status": "accepted",
        "consumer_module": "zenodex.perps",
        "action_kind": _ACTION_KIND,
        "action_id": action_id,
        "action_epoch": int(aggregate_result.observed_epoch) + 1,
        "freshness_window_epochs": _FRESHNESS_WINDOW_EPOCHS,
        "query_id": query_id,
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
        "freshness_window_epochs": _FRESHNESS_WINDOW_EPOCHS,
        "aggregate": dict(aggregate),
        "receipt_bundle": bundle,
    }
    aggregate_read["bridge_id"] = aggregate_read_content_hash(aggregate_read)

    action = {
        "schema": ACTION_SCHEMA,
        "consumer_module": "zenodex.perps",
        "action_kind": _ACTION_KIND,
        "action_id": action_id,
        "action_epoch": int(aggregate_result.observed_epoch) + 1,
        "query_id": query_id,
        "value_hash": value_hash,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": _FRESHNESS_WINDOW_EPOCHS,
        "read_receipt_id": read_receipt_id,
        "consumer_action_receipt_id": action_receipt["id"],
        "critical": True,
    }
    profile = {
        "schema": PROFILE_SCHEMA,
        "consumer_module": "zenodex.perps",
        "action_kind": _ACTION_KIND,
        "query_id": query_id,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": _FRESHNESS_WINDOW_EPOCHS,
        "critical": True,
    }
    profile["profile_id"] = profile_content_hash(profile)
    if profile["profile_id"] != _ORACLE_PERPS_SETTLE_EPOCH_PROFILE_ID:
        raise ValueError("local oracle profile fixture mismatch")

    bridge = {
        "schema": AGGREGATE_ADAPTER_SCHEMA,
        "aggregate_read": aggregate_read,
        "action": action,
        "profile": profile,
    }
    bridge["bridge_id"] = aggregate_adapter_content_hash(bridge)
    verify_result = verify_aggregate_adapter_bridge(bridge)
    if verify_result.status != "accepted":
        raise ValueError(f"local oracle bridge fixture rejected: {verify_result.errors}")
    return bridge
