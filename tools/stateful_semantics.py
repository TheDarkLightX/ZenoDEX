"""Semantic-state extractors for stateful weird-machine exploration tooling.

These helpers normalize payload families into protocol-relevant state classes so
frontier search can prioritize semantic novelty instead of only input novelty.
"""

from __future__ import annotations

from collections.abc import Mapping
from dataclasses import asdict, is_dataclass
from typing import Any, Callable, cast


def outcome_class(outcome_label: str) -> str:
    if outcome_label.startswith("ok"):
        return "ok"
    if outcome_label.startswith("reject:"):
        return "reject"
    if outcome_label.startswith("handled:"):
        return "handled"
    return outcome_label.split(":", 1)[0] or "unknown"


def _stable(value: Any) -> Any:
    if value is None or isinstance(value, (bool, int, float, str)):
        return value
    if is_dataclass(value) and not isinstance(value, type):
        return _stable(asdict(value))
    if isinstance(value, dict):
        return {str(key): _stable(val) for key, val in sorted(value.items(), key=lambda item: str(item[0]))}
    if isinstance(value, (list, tuple)):
        return [_stable(item) for item in value]
    if isinstance(value, set):
        return sorted(_stable(item) for item in value)
    return repr(value)


def _mapping_get(mapping: Any, key: str) -> Any:
    if isinstance(mapping, dict):
        if key in mapping:
            return mapping[key]
        try:
            int_key = int(key)
        except Exception:
            return None
        return mapping.get(int_key)
    return None


def _list_or_empty(value: Any) -> list[Any]:
    return value if isinstance(value, list) else []


def _dict_or_empty(value: Any) -> dict[str, Any]:
    return value if isinstance(value, dict) else {}


def _shape(value: Any, *, depth: int = 2, max_items: int = 4) -> Any:
    if depth <= 0:
        if isinstance(value, dict):
            return {"type": "dict", "len": len(value)}
        if isinstance(value, (list, tuple, set)):
            return {"type": type(value).__name__, "len": len(value)}
        return _scalar(value)
    if value is None or isinstance(value, (bool, int, float, str)):
        return _scalar(value)
    if is_dataclass(value) and not isinstance(value, type):
        return _shape(asdict(value), depth=depth, max_items=max_items)
    if isinstance(value, dict):
        items = list(sorted(value.items(), key=lambda item: str(item[0])))
        return {
            "type": "dict",
            "len": len(items),
            "keys": [str(key) for key, _ in items[:max_items]],
            "items": {str(key): _shape(val, depth=depth - 1, max_items=max_items) for key, val in items[:max_items]},
        }
    if isinstance(value, (list, tuple)):
        rows = list(value)
        return {
            "type": type(value).__name__,
            "len": len(rows),
            "items": [_shape(item, depth=depth - 1, max_items=max_items) for item in rows[:max_items]],
        }
    if isinstance(value, set):
        rows = sorted(_stable(item) for item in value)
        return {"type": "set", "len": len(rows), "items": [_shape(item, depth=depth - 1, max_items=max_items) for item in rows[:max_items]]}
    return {"type": type(value).__name__}


def _scalar(value: Any) -> Any:
    if value is None:
        return {"type": "none"}
    if isinstance(value, bool):
        return {"type": "bool", "value": value}
    if isinstance(value, int) and not isinstance(value, bool):
        if value < 0:
            bucket = "neg"
        elif value == 0:
            bucket = "zero"
        elif value == 1:
            bucket = "one"
        elif value <= 8:
            bucket = "small"
        elif value <= 1024:
            bucket = "medium"
        else:
            bucket = "large"
        return {"type": "int", "bucket": bucket}
    if isinstance(value, float):
        return {"type": "float", "repr": repr(value)}
    if isinstance(value, str):
        if not value:
            return {"type": "str", "shape": "empty"}
        if value.startswith("0x"):
            return {"type": "hex", "len": len(value) - 2}
        return {"type": "str", "len": len(value)}
    return {"type": type(value).__name__}


def default_action_summary(prev_payload: object, next_payload: object, mutation_name: str) -> object:
    return {
        "kind": mutation_name,
        "prev_shape": _shape(prev_payload, depth=1),
        "next_shape": _shape(next_payload, depth=1),
    }


def api_boundary_semantic_state(target_name: str):
    expected_flags = (
        "cpmm_ok",
        "balance_ok",
        "token_ok",
        "buyback_floor_ok",
        "buyback_floor_fixedpoint_ok",
        "rebate_ok",
        "lock_weight_ok",
        "proof_ok",
        "binding_ok",
    )

    def _state(payload: object, outcome_label: str, _path_id: str, _line_trace: tuple[str, ...], target_hits: tuple[str, ...], _waypoint_tags: tuple[str, ...], _harness_id: str) -> object:
        summary: dict[str, Any] = {
            "target": target_name,
            "outcome_class": outcome_class(outcome_label),
            "target_hits": list(target_hits),
            "payload_shape": _shape(payload, depth=1),
        }
        if target_name == "price_history" and isinstance(payload, list):
            summary["semantic_state"] = {
                "length": len(payload),
                "item_types": [type(item).__name__ for item in payload],
                "negative_positions": [idx for idx, item in enumerate(payload) if isinstance(item, int) and not isinstance(item, bool) and item < 0],
                "bool_positions": [idx for idx, item in enumerate(payload) if isinstance(item, bool)],
            }
            return summary
        if target_name == "settlement_proof_flags" and isinstance(payload, dict):
            ints = [key for key, value in payload.items() if isinstance(value, int) and not isinstance(value, bool)]
            summary["semantic_state"] = {
                "present_flags": sorted(str(key) for key in payload.keys()),
                "missing_flags": [key for key in expected_flags if key not in payload],
                "bool_flags": sorted(str(key) for key, value in payload.items() if isinstance(value, bool)),
                "nonbinary_int_flags": sorted(str(key) for key in ints if payload[key] not in (0, 1)),
            }
            return summary
        if target_name in {"balance_table", "lp_balances"} and isinstance(payload, list):
            entries = [row for row in payload if isinstance(row, dict)]
            amount_key = "amount"
            asset_key = "asset" if target_name == "balance_table" else "pool_id"
            ids = [(str(row.get("pubkey", "")), str(row.get(asset_key, ""))) for row in entries]
            summary["semantic_state"] = {
                "entry_count": len(payload),
                "invalid_entry_count": len(payload) - len(entries),
                "empty_pubkeys": sum(1 for row in entries if not row.get("pubkey")),
                "empty_secondary_ids": sum(1 for row in entries if not row.get(asset_key)),
                "negative_amounts": sum(1 for row in entries if isinstance(row.get(amount_key), int) and row.get(amount_key, 0) < 0),
                "duplicate_entries": len(ids) - len(set(ids)),
            }
            return summary
        if target_name == "feature_extension_inputs" and isinstance(payload, dict):
            summary["semantic_state"] = {
                "field_count": len(payload),
                "missing_required_count": len([key for key in ("trade_amount", "fee_charged", "proof_ok") if key not in payload]),
                "nonpositive_numeric_fields": sorted(
                    str(key)
                    for key, value in payload.items()
                    if isinstance(value, int) and not isinstance(value, bool) and value <= 0
                )[:6],
            }
            return summary
        return summary

    return _state


def state_boundary_semantic_state(target_name: str):
    def _intent_nonce(intent: Any) -> Any:
        fields = getattr(intent, "fields", None)
        if isinstance(fields, Mapping):
            return fields.get("nonce")
        if isinstance(intent, dict):
            return _mapping_get(intent, "nonce")
        return None

    def _intent_sender(intent: Any) -> str:
        sender = getattr(intent, "sender_pubkey", None)
        if isinstance(sender, str):
            return sender
        if isinstance(intent, dict):
            raw = _mapping_get(intent, "sender_pubkey")
            return str(raw or "")
        return ""

    def _nonce_pattern(nonces: list[Any]) -> str:
        if not nonces:
            return "empty"
        if any(nonce is None for nonce in nonces) and any(nonce is not None for nonce in nonces):
            return "mixed_presence"
        if any(nonce is None for nonce in nonces):
            return "missing"
        ints = [int(nonce) for nonce in nonces if isinstance(nonce, int) and not isinstance(nonce, bool)]
        if len(ints) != len(nonces):
            return "nonint"
        if len(set(ints)) != len(ints):
            return "duplicate"
        ordered = sorted(ints)
        if ordered != list(range(ordered[0], ordered[-1] + 1)):
            return "gap"
        return "contiguous"

    def _state(payload: object, outcome_label: str, _path_id: str, _line_trace: tuple[str, ...], target_hits: tuple[str, ...], _waypoint_tags: tuple[str, ...], _harness_id: str) -> object:
        summary: dict[str, Any] = {
            "target": target_name,
            "outcome_class": outcome_class(outcome_label),
            "target_hits": list(target_hits),
        }
        if target_name == "validate_and_apply_intent_nonce_batch" and isinstance(payload, dict):
            intents = _mapping_get(payload, "intents") or []
            nonces = [_intent_nonce(intent) for intent in intents] if isinstance(intents, list) else []
            senders = [_intent_sender(intent) for intent in intents] if isinstance(intents, list) else []
            nonce_table = _mapping_get(payload, "nonces")
            first_sender = next((sender for sender in senders if sender), "")
            table_last = None
            if first_sender and hasattr(nonce_table, "get_last"):
                try:
                    table_last = nonce_table.get_last(first_sender)
                except Exception:
                    table_last = None
            summary["semantic_state"] = {
                "intent_count": len(intents) if isinstance(intents, list) else 0,
                "sender_count": len({sender for sender in senders if sender}),
                "nonce_pattern": _nonce_pattern(nonces),
                "require_all_nonces": bool(_mapping_get(payload, "require_all_nonces")),
                "nonce_table_last": table_last,
            }
            return summary
        summary["semantic_state"] = {"payload_shape": _shape(payload, depth=1)}
        return summary

    return _state


def receipt_boundary_semantic_state(target_name: str):
    def _receipt_summary(receipt: Any, pools: Any) -> object:
        body = _mapping_get(receipt, "body") if isinstance(receipt, dict) else None
        if not isinstance(body, dict):
            return {"family": "unknown", "payload_shape": _shape(receipt, depth=1)}
        schema = str(body.get("schema", ""))
        if schema == "zenodex/route_quote_receipt/v1":
            cert = _dict_or_empty(body.get("canonical_route_certificate"))
            body_pools = _dict_or_empty(body.get("pools"))
            pool_keys = sorted(str(key) for key in body_pools)
            provided_pool_keys = sorted(str(key) for key in pools) if isinstance(pools, dict) else []
            return {
                "family": "quote_receipt",
                "kind": str(body.get("kind", "")),
                "receipt_hash_present": bool(receipt.get("receipt_hash")),
                "pool_key_count": len(pool_keys),
                "provided_pool_key_count": len(provided_pool_keys),
                "pool_key_match": pool_keys == provided_pool_keys,
                "candidate_count": len(cert.get("candidates", [])) if isinstance(cert, dict) else 0,
                "winner_index": cert.get("winner_index") if isinstance(cert, dict) else None,
            }
        return {
            "family": "confidential_extension",
            "receipt_hash_present": bool(receipt.get("receipt_hash")),
            "policy_digest_present": bool(body.get("policy_digest")),
            "measurement_present": bool(body.get("measurement")),
            "do_execute": body.get("do_execute"),
        }

    def _state(payload: object, outcome_label: str, _path_id: str, _line_trace: tuple[str, ...], target_hits: tuple[str, ...], _waypoint_tags: tuple[str, ...], _harness_id: str) -> object:
        summary: dict[str, Any] = {"target": target_name, "outcome_class": outcome_class(outcome_label), "target_hits": list(target_hits)}
        if isinstance(payload, tuple) and len(payload) == 2:
            summary["semantic_state"] = _receipt_summary(payload[0], payload[1])
            return summary
        if isinstance(payload, dict):
            summary["semantic_state"] = _receipt_summary(payload, {})
            return summary
        summary["semantic_state"] = {"payload_shape": _shape(payload, depth=1)}
        return summary

    return _state


def _quote_summary(quote: Any) -> dict[str, Any]:
    amount_in = getattr(quote, "amount_in", None)
    amount_out = getattr(quote, "amount_out", None)
    legs = getattr(quote, "legs", None)
    if legs is None and isinstance(quote, dict):
        amount_in = quote.get("amount_in")
        amount_out = quote.get("amount_out")
        legs = quote.get("legs")
    leg_rows = list(legs) if isinstance(legs, (list, tuple)) else []
    pool_sequence: list[str] = []
    hop_count = 0
    for leg in leg_rows:
        hops = getattr(leg, "hops", None)
        if hops is None and isinstance(leg, dict):
            hops = leg.get("hops")
        for hop in list(hops) if isinstance(hops, (list, tuple)) else []:
            pool_id = getattr(hop, "pool_id", None)
            if pool_id is None and isinstance(hop, dict):
                pool_id = hop.get("pool_id")
            pool_sequence.append(str(pool_id or ""))
            hop_count += 1
    return {
        "amount_in": amount_in,
        "amount_out": amount_out,
        "leg_count": len(leg_rows),
        "hop_count": hop_count,
        "pool_sequence": tuple(pool_sequence),
    }


def _changed_fields(left: dict[str, Any], right: dict[str, Any]) -> list[str]:
    keys = sorted(set(left) | set(right))
    return [key for key in keys if left.get(key) != right.get(key)]


def route_certificate_semantic_state(payload: object, outcome_label: str, _path_id: str, _line_trace: tuple[str, ...], target_hits: tuple[str, ...], _waypoint_tags: tuple[str, ...], _harness_id: str) -> object:
    if not isinstance(payload, dict):
        return {"outcome_class": outcome_class(outcome_label), "target_hits": list(target_hits), "payload_shape": _shape(payload, depth=1)}
    initial_quotes = _list_or_empty(payload.get("initial_quotes"))
    steps = _list_or_empty(payload.get("steps"))
    step_quotes: list[Any] = []
    if steps and isinstance(steps[0], dict):
        candidate_quotes = steps[0].get("quotes")
        if isinstance(candidate_quotes, list):
            step_quotes = candidate_quotes
    initial = [_quote_summary(quote) for quote in initial_quotes]
    current = [_quote_summary(quote) for quote in step_quotes]
    initial_pairs = [(row["pool_sequence"], row["amount_out"]) for row in initial]
    current_pairs = [(row["pool_sequence"], row["amount_out"]) for row in current]
    if current_pairs == initial_pairs:
        relation = "same_candidate_set"
    elif sorted(current_pairs) == sorted(initial_pairs):
        relation = "reordered_candidate_set"
    elif len(current_pairs) > len(initial_pairs) and set(initial_pairs).issubset(set(current_pairs)) and current_pairs:
        relation = "expanded_candidate_set"
    elif len(set(current_pairs)) < len(current_pairs):
        relation = "duplicate_candidate_set"
    elif {row[0] for row in initial_pairs} == {row[0] for row in current_pairs}:
        relation = "repriced_candidate_set"
    else:
        relation = "candidate_set_drift"
    return {
        "outcome_class": outcome_class(outcome_label),
        "target_hits": list(target_hits),
        "candidate_relation": relation,
        "initial_candidate_count": len(initial),
        "current_candidate_count": len(current),
        "initial_best_amount_out": max((row["amount_out"] for row in initial if isinstance(row["amount_out"], int)), default=None),
        "current_best_amount_out": max((row["amount_out"] for row in current if isinstance(row["amount_out"], int)), default=None),
        "current_pool_sequences": [list(row["pool_sequence"]) for row in current],
    }


def route_certificate_action_summary(prev_payload: object, next_payload: object, mutation_name: str) -> object:
    prev_state = cast(dict[str, Any], route_certificate_semantic_state(prev_payload, "ok", "", (), (), (), ""))
    next_state = cast(dict[str, Any], route_certificate_semantic_state(next_payload, "ok", "", (), (), (), ""))
    return {
        "kind": mutation_name,
        "candidate_relation": next_state.get("candidate_relation"),
        "changed_fields": _changed_fields(prev_state, next_state),
    }


def operations_signature_semantic_state(payload: object, outcome_label: str, _path_id: str, _line_trace: tuple[str, ...], target_hits: tuple[str, ...], _waypoint_tags: tuple[str, ...], _harness_id: str) -> object:
    entries = _mapping_get(payload, "2")
    if not isinstance(entries, list):
        entries = []
    duplicate_modes: list[str] = []
    senders: set[str] = set()
    intent_kinds: set[str] = set()
    inner_sig_count = 0
    outer_sig_count = 0
    for entry in entries:
        if not isinstance(entry, (list, tuple)) or not entry:
            continue
        intent = entry[0]
        outer_sig = entry[1] if len(entry) > 1 else None
        if isinstance(intent, dict):
            senders.add(str(intent.get("sender_pubkey", "")))
            intent_kinds.add(str(intent.get("kind", "")))
            inner_sig = intent.get("signature")
            if isinstance(inner_sig, str) and inner_sig:
                inner_sig_count += 1
                if isinstance(outer_sig, str) and outer_sig:
                    duplicate_modes.append("same" if inner_sig == outer_sig else "different")
        if isinstance(outer_sig, str) and outer_sig:
            outer_sig_count += 1
    return {
        "outcome_class": outcome_class(outcome_label),
        "target_hits": list(target_hits),
        "entry_count": len(entries),
        "sender_count": len({sender for sender in senders if sender}),
        "intent_kind_count": len({kind for kind in intent_kinds if kind}),
        "inner_signature_count": inner_sig_count,
        "outer_signature_count": outer_sig_count,
        "duplicate_binding_modes": sorted(set(duplicate_modes)) or ["none"],
    }


def sequence_action_summary(
    state_fn: Callable[[object, str, str, tuple[str, ...], tuple[str, ...], tuple[str, ...], str], object],
    prev_payload: object,
    next_payload: object,
    mutation_name: str,
) -> object:
    prev_state = cast(dict[str, Any], state_fn(prev_payload, "ok", "", (), (), (), ""))
    next_state = cast(dict[str, Any], state_fn(next_payload, "ok", "", (), (), (), ""))
    return {
        "kind": mutation_name,
        "changed_fields": _changed_fields(prev_state, next_state),
    }


def quote_receipt_sequence_semantic_state(payload: object, outcome_label: str, _path_id: str, _line_trace: tuple[str, ...], target_hits: tuple[str, ...], _waypoint_tags: tuple[str, ...], _harness_id: str) -> object:
    steps = _list_or_empty(payload.get("steps")) if isinstance(payload, dict) else []
    summaries: list[dict[str, Any]] = []
    for step in steps:
        operations = step.get("operations") if isinstance(step, dict) else {}
        intents = _mapping_get(operations, "2")
        first_intent = intents[0] if isinstance(intents, list) and intents else {}
        receipt = first_intent.get("quote_receipt") if isinstance(first_intent, dict) else None
        body = receipt.get("body") if isinstance(receipt, dict) else {}
        cert = body.get("canonical_route_certificate") if isinstance(body, dict) else {}
        summaries.append(
            {
                "intent_count": len(intents) if isinstance(intents, list) else 0,
                "pool_id": str(first_intent.get("pool_id", "")) if isinstance(first_intent, dict) else "",
                "receipt_kind": str(body.get("kind", "")) if isinstance(body, dict) else "",
                "receipt_hash_present": bool(receipt.get("receipt_hash")) if isinstance(receipt, dict) else False,
                "quote_hash_present": bool(first_intent.get("quote_receipt_hash")) if isinstance(first_intent, dict) else False,
                "candidate_count": len(cert.get("candidates", [])) if isinstance(cert, dict) else 0,
            }
        )
    changed_fields = _changed_fields(summaries[0], summaries[-1]) if len(summaries) >= 2 else []
    return {
        "outcome_class": outcome_class(outcome_label),
        "target_hits": list(target_hits),
        "initial_mode": str(payload.get("initial", "")) if isinstance(payload, dict) else "",
        "step_summaries": summaries,
        "changed_fields": changed_fields,
    }


def stale_settlement_semantic_state(payload: object, outcome_label: str, _path_id: str, _line_trace: tuple[str, ...], target_hits: tuple[str, ...], _waypoint_tags: tuple[str, ...], _harness_id: str) -> object:
    steps = _list_or_empty(payload.get("steps")) if isinstance(payload, dict) else []
    summaries: list[dict[str, Any]] = []
    for step in steps:
        operations = step.get("operations") if isinstance(step, dict) else {}
        intents = _mapping_get(operations, "2")
        settlement = _mapping_get(operations, "3")
        fills = _list_or_empty(settlement.get("fills")) if isinstance(settlement, dict) else []
        reserve_deltas = _list_or_empty(settlement.get("reserve_deltas")) if isinstance(settlement, dict) else []
        included = _list_or_empty(settlement.get("included_intents")) if isinstance(settlement, dict) else []
        summaries.append(
            {
                "intent_count": len(intents) if isinstance(intents, list) else 0,
                "has_settlement": isinstance(settlement, dict),
                "fill_count": len(fills),
                "included_intent_count": len(included),
                "reserve_delta_count": len(reserve_deltas),
                "allow_missing_settlement": bool(step.get("config", {}).get("allow_missing_settlement")) if isinstance(step, dict) and isinstance(step.get("config"), dict) else False,
                "filled_amount_out_total": sum(int(fill.get("amount_out_filled", 0) or 0) for fill in fills if isinstance(fill, dict)),
            }
        )
    changed_fields = _changed_fields(summaries[0], summaries[-1]) if len(summaries) >= 2 else []
    return {
        "outcome_class": outcome_class(outcome_label),
        "target_hits": list(target_hits),
        "step_summaries": summaries,
        "changed_fields": changed_fields,
    }


def settlement_attestation_semantic_state(attestation_mode: str):
    signed_at_epoch = 100

    def _state(payload: object, outcome_label: str, _path_id: str, _line_trace: tuple[str, ...], target_hits: tuple[str, ...], _waypoint_tags: tuple[str, ...], _harness_id: str) -> object:
        steps = _list_or_empty(payload.get("steps")) if isinstance(payload, dict) else []
        summaries: list[dict[str, Any]] = []
        for step in steps:
            if not isinstance(step, dict):
                continue
            now_epoch = int(step.get("consumer_now_epoch", 0) or 0)
            age = now_epoch - signed_at_epoch
            allowed_sources = sorted(str(item) for item in step.get("allowed_sources", []) if isinstance(item, str))
            if step.get("tamper_signature"):
                step_class = "tamper_signature"
            elif step.get("tamper_packet_hash"):
                step_class = "tamper_packet_hash"
            elif age < 0:
                step_class = "future"
            elif age > 5:
                step_class = "stale"
            elif allowed_sources != ["oracle:a", "oracle:b"]:
                step_class = "policy_drift"
            else:
                step_class = "valid"
            summaries.append(
                {
                    "consumer_now_epoch": now_epoch,
                    "attestation_age": age,
                    "allowlist_size": len(allowed_sources),
                    "step_class": step_class,
                }
            )
        return {
            "outcome_class": outcome_class(outcome_label),
            "target_hits": list(target_hits),
            "attestation_mode": attestation_mode,
            "step_summaries": summaries,
            "second_step_class": summaries[1]["step_class"] if len(summaries) > 1 else "none",
        }

    return _state
