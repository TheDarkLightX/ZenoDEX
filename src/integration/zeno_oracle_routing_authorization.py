"""Typed ZenoOracle authorization checks for protected routing swaps."""

from __future__ import annotations

from typing import Any, Mapping

from ..state.intents import Intent
from .zeno_oracle_authorization import check_critical_consumer_authorization, semantic_hash


def protected_swap_query_id(*, kind: str, asset_in: str, asset_out: str) -> str:
    value_kind = "amount_out" if kind == "exact_in" else "amount_in"
    return f"zenodex.routing.{kind}.{asset_in}.{asset_out}.{value_kind}"


def _receipt_body(receipt: Mapping[str, Any]) -> Mapping[str, Any]:
    body = receipt.get("body")
    if not isinstance(body, Mapping):
        raise ValueError("invalid quote receipt body")
    return body


def _matching_quote_leg(intent: Intent, receipt: Mapping[str, Any]) -> tuple[int, Mapping[str, Any], Mapping[str, Any]]:
    body = _receipt_body(receipt)
    legs = body.get("legs")
    if not isinstance(legs, list) or not legs:
        raise ValueError("invalid quote receipt legs")
    leg_index = intent.get_field("quote_receipt_leg_index")
    if not isinstance(leg_index, int) or isinstance(leg_index, bool) or leg_index < 0:
        raise ValueError("missing quote_receipt_leg_index")
    if int(leg_index) >= len(legs):
        raise ValueError("quote receipt leg index out of range")
    leg = legs[int(leg_index)]
    if not isinstance(leg, Mapping):
        raise ValueError("invalid quote receipt leg")
    hops = leg.get("hops")
    if not isinstance(hops, list) or len(hops) != 1 or not isinstance(hops[0], Mapping):
        raise ValueError("quote receipt multi-hop leg unsupported for protected swap authorization")
    hop = hops[0]
    pool_id = intent.get_field("pool_id")
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(pool_id, str) or not isinstance(asset_in, str) or not isinstance(asset_out, str):
        raise ValueError("invalid protected swap intent fields")
    if (
        str(hop.get("pool_id", "")).strip() != pool_id
        or str(hop.get("asset_in", "")).strip() != asset_in
        or str(hop.get("asset_out", "")).strip() != asset_out
    ):
        raise ValueError("protected swap quote leg mismatch")
    return int(leg_index), leg, hop


def protected_swap_runtime_facts(
    *,
    intent: Intent,
    receipt: Mapping[str, Any],
    now_epoch: int,
) -> dict[str, Any]:
    body = _receipt_body(receipt)
    kind = str(body.get("kind", "")).strip().lower()
    if kind not in {"exact_in", "exact_out"}:
        raise ValueError("unsupported quote receipt kind")
    expected_kind = "exact_in" if intent.kind.value == "SWAP_EXACT_IN" else "exact_out"
    if kind != expected_kind:
        raise ValueError("quote receipt kind mismatch")

    leg_index, leg, hop = _matching_quote_leg(intent, receipt)
    hop_amount_in = hop.get("amount_in")
    hop_amount_out = hop.get("amount_out")
    if not isinstance(hop_amount_in, int) or isinstance(hop_amount_in, bool):
        raise ValueError("invalid quote hop amount_in")
    if not isinstance(hop_amount_out, int) or isinstance(hop_amount_out, bool):
        raise ValueError("invalid quote hop amount_out")

    if kind == "exact_in":
        amount_in = intent.get_field("amount_in")
        min_amount_out = intent.get_field("min_amount_out")
        if not isinstance(amount_in, int) or isinstance(amount_in, bool) or int(amount_in) <= 0:
            raise ValueError("invalid exact-in amount_in")
        if not isinstance(min_amount_out, int) or isinstance(min_amount_out, bool) or int(min_amount_out) < 0:
            raise ValueError("invalid exact-in min_amount_out")
        if int(amount_in) != int(hop_amount_in) or int(min_amount_out) > int(hop_amount_out):
            raise ValueError("exact-in protected swap quote mismatch")
        runtime_value = int(hop_amount_out)
        amount_constraint = {"amount_in": int(amount_in), "min_amount_out": int(min_amount_out)}
    else:
        amount_out = intent.get_field("amount_out")
        max_amount_in = intent.get_field("max_amount_in")
        if not isinstance(amount_out, int) or isinstance(amount_out, bool) or int(amount_out) <= 0:
            raise ValueError("invalid exact-out amount_out")
        if not isinstance(max_amount_in, int) or isinstance(max_amount_in, bool) or int(max_amount_in) < 0:
            raise ValueError("invalid exact-out max_amount_in")
        if int(amount_out) != int(hop_amount_out) or int(max_amount_in) < int(hop_amount_in):
            raise ValueError("exact-out protected swap quote mismatch")
        runtime_value = int(hop_amount_in)
        amount_constraint = {"amount_out": int(amount_out), "max_amount_in": int(max_amount_in)}

    pools = body.get("pools")
    if not isinstance(pools, Mapping):
        raise ValueError("invalid quote receipt pools")
    receipt_hash = receipt.get("receipt_hash")
    if not isinstance(receipt_hash, str) or not receipt_hash:
        raise ValueError("invalid quote receipt hash")
    pool_id = str(intent.get_field("pool_id"))
    asset_in = str(intent.get_field("asset_in"))
    asset_out = str(intent.get_field("asset_out"))
    quote_epoch = body.get("quote_epoch", 0)
    if not isinstance(quote_epoch, int) or isinstance(quote_epoch, bool) or int(quote_epoch) < 0:
        raise ValueError("invalid quote_epoch")

    query_id = protected_swap_query_id(kind=kind, asset_in=asset_in, asset_out=asset_out)
    pre_state_hash = semantic_hash(
        "zenodex.routing.protected_swap.pre_state.v1",
        {
            "pool_fingerprints": {str(k): pools[k] for k in sorted(pools.keys())},
            "quote_epoch": int(quote_epoch),
            "receipt_hash": receipt_hash,
        },
    )
    facts_payload: dict[str, Any] = {
        "action_kind": "protected_swap",
        "asset_in": asset_in,
        "asset_out": asset_out,
        "consumer_module": "zenodex.routing",
        "intent_id": intent.intent_id,
        "kind": kind,
        "leg": {
            "amount_in": int(leg.get("amount_in", 0)),
            "amount_out": int(leg.get("amount_out", 0)),
            "index": int(leg_index),
        },
        "pool_id": pool_id,
        "pre_state_hash": pre_state_hash,
        "query_id": query_id,
        "quote_receipt_hash": receipt_hash,
        "sender_pubkey": intent.sender_pubkey,
        **amount_constraint,
    }
    action_facts_hash = semantic_hash("zenodex.routing.protected_swap.facts.v1", facts_payload)
    action_id = semantic_hash(
        "zenodex.routing.protected_swap.action.v1",
        {
            "action_facts_hash": action_facts_hash,
            "intent_id": intent.intent_id,
        },
    )
    return {
        "action_facts_hash": action_facts_hash,
        "action_id": action_id,
        "now_epoch": int(now_epoch),
        "pre_state_hash": pre_state_hash,
        "query_id": query_id,
        "runtime_value_e8": int(runtime_value),
    }


def check_protected_swap_oracle_authorization(
    *,
    authorization_payload: Mapping[str, Any],
    intent: Intent,
    receipt: Mapping[str, Any],
    now_epoch: int,
) -> dict[str, Any]:
    runtime = protected_swap_runtime_facts(intent=intent, receipt=receipt, now_epoch=now_epoch)
    return check_critical_consumer_authorization(
        authorization_payload,
        consumer_module="zenodex.routing",
        action_kind="protected_swap",
        action_id=str(runtime["action_id"]),
        action_facts_hash=str(runtime["action_facts_hash"]),
        pre_state_hash=str(runtime["pre_state_hash"]),
        query_id=str(runtime["query_id"]),
        runtime_value_e8=int(runtime["runtime_value_e8"]),
        now_epoch=int(runtime["now_epoch"]),
        require_authenticated_receipt_graph=True,
    )
