"""Typed ZenoOracle authorization checks for critical settlements."""

from __future__ import annotations

import hashlib
from typing import Any, Mapping

from ..core.settlement import Settlement
from ..core.settlement_normal_form import normalize_settlement_op_for_commitment
from ..state.canonical import canonical_json_bytes
from .operations import create_settlement_operation
from .zeno_oracle_authorization import check_critical_consumer_authorization, semantic_hash


_ORACLE_CONSUMER_PROFILE_SCHEMA = "zenodex.oracle.consumer_profile.v1"
_CRITICAL_SETTLEMENT_QUERY_ID = (
    "sha256:" + hashlib.sha256(b"zenodex.oracle.query.settlement.price_curr_e8").hexdigest()
)


def critical_settlement_query_id() -> str:
    return _CRITICAL_SETTLEMENT_QUERY_ID


def critical_settlement_profile_id() -> str:
    payload = {
        "schema": _ORACLE_CONSUMER_PROFILE_SCHEMA,
        "consumer_module": "zenodex.settlement",
        "action_kind": "critical_settlement",
        "query_id": _CRITICAL_SETTLEMENT_QUERY_ID,
        "required_evidence_floor": "O3",
        "max_freshness_window_epochs": 1,
        "critical": True,
    }
    return "sha256:" + hashlib.sha256(canonical_json_bytes(payload)).hexdigest()


def normalized_settlement_hash(settlement: Settlement) -> str:
    op = create_settlement_operation(settlement).get("3")
    if not isinstance(op, dict):
        raise TypeError("internal error: settlement operation must be an object")
    normalized = normalize_settlement_op_for_commitment(op)
    return semantic_hash("zenodex.settlement.normalized.v1", normalized)


def critical_settlement_runtime_facts(
    *,
    settlement: Settlement,
    pre_state_hash: str,
    price_history: tuple[int, int, int],
    now_epoch: int,
) -> dict[str, Any]:
    if not isinstance(pre_state_hash, str) or not pre_state_hash:
        raise ValueError("pre_state_hash must be a non-empty string")
    if not isinstance(price_history, tuple) or len(price_history) != 3:
        raise ValueError("price_history must be a 3-tuple: (price_pp, price_prev, price_curr)")
    price_pp, price_prev, price_curr = price_history
    for name, value in (
        ("price_pp", price_pp),
        ("price_prev", price_prev),
        ("price_curr", price_curr),
    ):
        if not isinstance(value, int) or isinstance(value, bool):
            raise ValueError(f"{name} must be an int")
        if int(value) < 0:
            raise ValueError(f"{name} must be non-negative")
    if not isinstance(now_epoch, int) or isinstance(now_epoch, bool) or int(now_epoch) < 0:
        raise ValueError("now_epoch must be a non-negative int")

    settlement_hash = normalized_settlement_hash(settlement)
    query_id = critical_settlement_query_id()
    facts_payload = {
        "action_kind": "critical_settlement",
        "consumer_module": "zenodex.settlement",
        "included_intent_ids": [str(intent_id) for intent_id, _action in settlement.included_intents],
        "pre_state_hash": pre_state_hash,
        "price_curr": int(price_curr),
        "price_pp": int(price_pp),
        "price_prev": int(price_prev),
        "query_id": query_id,
        "settlement_hash": settlement_hash,
    }
    action_facts_hash = semantic_hash("zenodex.settlement.critical_settlement.facts.v1", facts_payload)
    action_id = semantic_hash(
        "zenodex.settlement.critical_settlement.action.v1",
        {
            "action_facts_hash": action_facts_hash,
            "settlement_hash": settlement_hash,
        },
    )
    return {
        "action_facts_hash": action_facts_hash,
        "action_id": action_id,
        "now_epoch": int(now_epoch),
        "pre_state_hash": pre_state_hash,
        "query_id": query_id,
        "runtime_value_e8": int(price_curr),
        "settlement_hash": settlement_hash,
    }


def check_critical_settlement_oracle_authorization(
    *,
    authorization_payload: Mapping[str, Any],
    settlement: Settlement,
    pre_state_hash: str,
    price_history: tuple[int, int, int],
    now_epoch: int,
) -> dict[str, Any]:
    runtime = critical_settlement_runtime_facts(
        settlement=settlement,
        pre_state_hash=pre_state_hash,
        price_history=price_history,
        now_epoch=now_epoch,
    )
    return check_critical_consumer_authorization(
        authorization_payload,
        consumer_module="zenodex.settlement",
        action_kind="critical_settlement",
        action_id=str(runtime["action_id"]),
        action_facts_hash=str(runtime["action_facts_hash"]),
        pre_state_hash=str(runtime["pre_state_hash"]),
        profile_id=critical_settlement_profile_id(),
        query_id=str(runtime["query_id"]),
        runtime_value_e8=int(runtime["runtime_value_e8"]),
        now_epoch=int(runtime["now_epoch"]),
        require_authenticated_receipt_graph=True,
    )
