"""
Settlement normal forms (canonical encodings) for quotient-style commitments.

Many settlement fields (especially delta lists) are order-insensitive with
respect to the resulting state transition. This module defines a canonical
ordering so commitments and comparisons can be stable across equivalent encoders.
"""

from __future__ import annotations

import json
from typing import Any, Dict, Mapping


def _require_non_empty_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str):
        raise TypeError(f"{name} must be a string")
    if not value:
        raise TypeError(f"{name} must be a non-empty string")
    return value


def _int_or_0(value: Any, *, name: str) -> int:
    if value is None:
        return 0
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{name} must be an int")
    return int(value)


def _canonical_json_key(value: object) -> str:
    # Use a strict, deterministic JSON string for ordering tie-breaks.
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        allow_nan=False,
    )


def _normalize_included_intents(included: Any) -> list[list[str]]:
    if included is None:
        included = []
    if not isinstance(included, list):
        raise TypeError("settlement.included_intents must be a list")
    norm_included = []
    for entry in included:
        if not isinstance(entry, (list, tuple)) or len(entry) != 2:
            raise TypeError("included_intents entries must be [intent_id, action]")
        intent_id, action = entry[0], entry[1]
        norm_included.append(
            [
                _require_non_empty_str(
                    intent_id,
                    name="included_intents.intent_id",
                ),
                _require_non_empty_str(
                    action,
                    name="included_intents.action",
                ),
            ]
        )
    norm_included.sort(key=lambda t: (t[0], t[1]))
    return norm_included


def _normalize_fills(fills: Any) -> list[Dict[str, Any]]:
    if fills is None:
        fills = []
    if not isinstance(fills, list):
        raise TypeError("settlement.fills must be a list")
    compact_fills: list[Dict[str, Any]] = []
    for fill in fills:
        if not isinstance(fill, Mapping):
            raise TypeError("fill must be an object")
        d = {k: v for k, v in dict(fill).items() if v is not None and k != "reason"}
        d["intent_id"] = _require_non_empty_str(
            d.get("intent_id"),
            name="fill.intent_id",
        )
        d["action"] = _require_non_empty_str(
            d.get("action"),
            name="fill.action",
        )
        compact_fills.append(d)
    compact_fills.sort(
        key=lambda d: (
            d.get("intent_id", ""),
            d.get("action", ""),
            _canonical_json_key(d),
        )
    )
    return compact_fills


def _normalize_deltas(
    name: str,
    raw: Any,
    *,
    key_fields: tuple[str, ...],
) -> list[Dict[str, Any]]:
    if raw is None:
        raw = []
    if not isinstance(raw, list):
        raise TypeError(f"settlement.{name} must be a list")
    acc: dict[tuple[str, ...], tuple[int, int]] = {}
    for entry in raw:
        if not isinstance(entry, Mapping):
            raise TypeError(f"{name} entries must be objects")
        entry_d = dict(entry)
        key = tuple(
            _require_non_empty_str(entry_d.get(f), name=f"{name}.{f}")
            for f in key_fields
        )
        delta_add = _int_or_0(entry_d.get("delta_add", 0), name=f"{name}.delta_add")
        delta_sub = _int_or_0(entry_d.get("delta_sub", 0), name=f"{name}.delta_sub")
        if delta_add == 0 and delta_sub == 0:
            continue
        prev = acc.get(key)
        if prev is None:
            acc[key] = (int(delta_add), int(delta_sub))
        else:
            acc[key] = (int(prev[0]) + int(delta_add), int(prev[1]) + int(delta_sub))

    items: list[Dict[str, Any]] = []
    for key in sorted(acc.keys()):
        d: Dict[str, Any] = {key_fields[i]: key[i] for i in range(len(key_fields))}
        delta_add, delta_sub = acc[key]
        d["delta_add"] = int(delta_add)
        d["delta_sub"] = int(delta_sub)
        items.append(d)
    return items


def normalize_settlement_op_for_commitment(op3: Mapping[str, Any]) -> Dict[str, Any]:
    """
    Return a canonical dict suitable for hashing/commitment.

    Normalization:
    - drop non-transition metadata: `batch_ref`, `events`
    - for each fill: drop `reason` and any `None` values
    - sort `included_intents`, `fills`, and all delta lists by deterministic keys
    - aggregate deltas by key (semantic normal form)
    """
    if not isinstance(op3, Mapping):
        raise TypeError("op3 must be a mapping")
    op = dict(op3)

    out: Dict[str, Any] = {k: v for k, v in op.items() if k not in ("batch_ref", "events")}
    out["included_intents"] = _normalize_included_intents(out.get("included_intents"))
    out["fills"] = _normalize_fills(out.get("fills"))
    out["balance_deltas"] = _normalize_deltas(
        "balance_deltas",
        out.get("balance_deltas"),
        key_fields=("pubkey", "asset"),
    )
    out["reserve_deltas"] = _normalize_deltas(
        "reserve_deltas",
        out.get("reserve_deltas"),
        key_fields=("pool_id", "asset"),
    )
    out["lp_deltas"] = _normalize_deltas(
        "lp_deltas",
        out.get("lp_deltas"),
        key_fields=("pubkey", "pool_id"),
    )

    return out
