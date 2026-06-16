"""Pre-replay settlement index construction.

Strong settlement validation first binds the submitted settlement to the exact
input intent set. This module builds the intent/fill lookup maps and rejects
duplicate, missing, or extra entries before any pool or balance replay occurs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from ..state.intents import Intent
from .settlement import Fill, FillAction, Settlement


@dataclass(frozen=True)
class SettlementIndex:
    intents_by_id: Dict[str, Intent]
    fill_by_id: Dict[str, Fill]


def _build_intents_by_id(intents: List[Intent]) -> Tuple[Optional[Dict[str, Intent]], Optional[str]]:
    intent_ids = [it.intent_id for it in intents]
    if len(intent_ids) != len(set(intent_ids)):
        return None, "duplicate intent_id in input intents"
    return {it.intent_id: it for it in intents}, None


def _validate_included_intent_ids(
    *,
    settlement: Settlement,
    intent_ids: List[str],
) -> Optional[str]:
    included_ids = [intent_id for intent_id, _action in settlement.included_intents]
    if set(included_ids) != set(intent_ids):
        missing = sorted(set(intent_ids) - set(included_ids))
        extra = sorted(set(included_ids) - set(intent_ids))
        return f"settlement included_intents mismatch: missing={missing} extra={extra}"
    if len(included_ids) != len(set(included_ids)):
        return "settlement included_intents contains duplicate intent_id entries"
    return None


def _build_fill_by_id(
    *,
    settlement: Settlement,
    intent_ids: List[str],
) -> Tuple[Optional[Dict[str, Fill]], Optional[str]]:
    fill_ids = [f.intent_id for f in settlement.fills]
    if len(fill_ids) != len(set(fill_ids)):
        return None, "settlement fills contains duplicate intent_id entries"
    extra_fill_ids = sorted(set(fill_ids) - set(intent_ids))
    if extra_fill_ids:
        return None, f"settlement fills contains intent_ids not in input intents: {extra_fill_ids}"
    return {f.intent_id: f for f in settlement.fills}, None


def _validate_included_fill_actions(
    *,
    settlement: Settlement,
    fill_by_id: Dict[str, Fill],
) -> Optional[str]:
    for intent_id, action in settlement.included_intents:
        fill = fill_by_id.get(intent_id)
        if fill is None:
            if action == FillAction.FILL:
                return f"missing Fill for filled intent_id: {intent_id}"
            continue
        if fill.action != action:
            return f"Fill.action mismatch for intent_id={intent_id}: {fill.action} != {action}"
    return None


def build_settlement_index(
    *,
    settlement: Settlement,
    intents: List[Intent],
) -> Tuple[Optional[SettlementIndex], Optional[str]]:
    intent_ids = [it.intent_id for it in intents]
    intents_by_id, err = _build_intents_by_id(intents)
    if intents_by_id is None:
        return None, err
    err = _validate_included_intent_ids(settlement=settlement, intent_ids=intent_ids)
    if err is not None:
        return None, err
    fill_by_id, err = _build_fill_by_id(settlement=settlement, intent_ids=intent_ids)
    if fill_by_id is None:
        return None, err
    err = _validate_included_fill_actions(settlement=settlement, fill_by_id=fill_by_id)
    if err is not None:
        return None, err
    return SettlementIndex(intents_by_id=intents_by_id, fill_by_id=fill_by_id), None
