"""
Settlement normal forms (canonical encodings) for quotient-style commitments.

Many settlement fields (especially delta lists) are order-insensitive with
respect to the resulting state transition. This module defines a canonical
ordering so commitments and comparisons can be stable across equivalent encoders.
"""

from __future__ import annotations

from typing import Any, Dict, Mapping


def normalize_settlement_op_for_commitment(op3: Mapping[str, Any]) -> Dict[str, Any]:
    """
    Return a canonical dict suitable for hashing/commitment.

    Normalization:
    - drop non-transition metadata: `batch_ref`, `events`
    - for each fill: drop `reason` and any `None` values
    - sort `included_intents`, `fills`, and all delta lists by deterministic keys
    """
    if not isinstance(op3, Mapping):
        raise TypeError("op3 must be a mapping")
    op = dict(op3)

    out: Dict[str, Any] = {k: v for k, v in op.items() if k not in ("batch_ref", "events")}

    included = out.get("included_intents")
    if included is None:
        included = []
    if not isinstance(included, list):
        raise TypeError("settlement.included_intents must be a list")
    norm_included = []
    for entry in included:
        if not isinstance(entry, (list, tuple)) or len(entry) != 2:
            raise TypeError("included_intents entries must be [intent_id, action]")
        intent_id, action = entry[0], entry[1]
        if not isinstance(intent_id, str) or not intent_id:
            raise TypeError("included_intents.intent_id must be a non-empty string")
        if not isinstance(action, str) or not action:
            raise TypeError("included_intents.action must be a non-empty string")
        norm_included.append([intent_id, action])
    norm_included.sort(key=lambda t: (t[0], t[1]))
    out["included_intents"] = norm_included

    fills = out.get("fills")
    if fills is None:
        fills = []
    if not isinstance(fills, list):
        raise TypeError("settlement.fills must be a list")
    compact_fills: list[Dict[str, Any]] = []
    for fill in fills:
        if not isinstance(fill, Mapping):
            raise TypeError("fill must be an object")
        d = {k: v for k, v in dict(fill).items() if v is not None and k != "reason"}
        intent_id = d.get("intent_id")
        action = d.get("action")
        if not isinstance(intent_id, str) or not intent_id:
            raise TypeError("fill.intent_id must be a non-empty string")
        if not isinstance(action, str) or not action:
            raise TypeError("fill.action must be a non-empty string")
        compact_fills.append(d)
    compact_fills.sort(key=lambda d: (d.get("intent_id", ""), d.get("action", "")))
    out["fills"] = compact_fills

    def _sort_deltas(name: str, *, key_fields: tuple[str, ...]) -> None:
        raw = out.get(name)
        if raw is None:
            raw = []
        if not isinstance(raw, list):
            raise TypeError(f"settlement.{name} must be a list")
        items: list[Dict[str, Any]] = []
        for entry in raw:
            if not isinstance(entry, Mapping):
                raise TypeError(f"{name} entries must be objects")
            items.append(dict(entry))

        def _k(d: Dict[str, Any]) -> tuple[Any, ...]:
            return tuple(d.get(f) for f in key_fields) + (d.get("delta_add"), d.get("delta_sub"))

        items.sort(key=_k)
        out[name] = items

    _sort_deltas("balance_deltas", key_fields=("pubkey", "asset"))
    _sort_deltas("reserve_deltas", key_fields=("pool_id", "asset"))
    _sort_deltas("lp_deltas", key_fields=("pubkey", "pool_id"))

    return out

