"""COW pair index validation for strong settlement replay.

The strong validator only accepts COW-netted fills when each filled exact-in
swap has exactly one reciprocal counterparty with matching pool, assets, and
filled amounts. This module keeps that pre-replay shape check separate from
state mutation and balance-delta replay.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from ..state.balances import AssetId
from ..state.intents import Intent, IntentKind
from .domain_limits import is_strict_int
from .settlement import Fill, FillAction, Settlement


@dataclass(frozen=True)
class _CowPairEntry:
    intent_id: str
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in_filled: int
    amount_out_filled: int


@dataclass(frozen=True)
class _CowPairIntentFields:
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId
    amount_in: int
    min_out: int


@dataclass(frozen=True)
class _CowPairFillAmounts:
    amount_in_filled: int
    amount_out_filled: int


_CowPairKey = Tuple[str, AssetId, AssetId, int, int]


def _cow_pair_key(entry: _CowPairEntry) -> _CowPairKey:
    return (
        entry.pool_id,
        entry.asset_in,
        entry.asset_out,
        entry.amount_in_filled,
        entry.amount_out_filled,
    )


def _cow_pair_reciprocal_key(entry: _CowPairEntry) -> _CowPairKey:
    return (
        entry.pool_id,
        entry.asset_out,
        entry.asset_in,
        entry.amount_out_filled,
        entry.amount_in_filled,
    )


def _validate_cow_pair_shape(*, intent_id: str, intent: Intent, fill: Fill) -> Optional[str]:
    if fill.action != FillAction.FILL:
        return f"COW_NETTED requires filled action: intent_id={intent_id}"
    if intent.kind != IntentKind.SWAP_EXACT_IN:
        return f"COW_NETTED only supported for SWAP_EXACT_IN: intent_id={intent_id}"
    return None


def _parse_cow_pair_intent_fields(
    *,
    intent_id: str,
    intent: Intent,
) -> Tuple[Optional[_CowPairIntentFields], Optional[str]]:
    pool_id = intent.get_field("pool_id")
    if not isinstance(pool_id, str) or not pool_id:
        return None, f"missing pool_id for intent_id={intent_id}"
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    if not isinstance(asset_in, str) or not isinstance(asset_out, str):
        return None, f"invalid asset_in/out for intent_id={intent_id}"
    amount_in = intent.get_field("amount_in")
    min_out = intent.get_field("min_amount_out", 0)
    if not is_strict_int(amount_in) or int(amount_in) <= 0:
        return None, f"invalid amount_in for intent_id={intent_id}"
    if not is_strict_int(min_out) or int(min_out) < 0:
        return None, f"invalid min_amount_out for intent_id={intent_id}"
    return (
        _CowPairIntentFields(
            pool_id=pool_id,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=int(amount_in),
            min_out=int(min_out),
        ),
        None,
    )


def _check_cow_pair_fill_fee(*, intent_id: str, fill: Fill) -> Optional[str]:
    if int(fill.fee_paid or 0) != 0:
        return f"COW_NETTED fee_paid must be 0: intent_id={intent_id}"
    return None


def _parse_cow_pair_amount_in_filled(
    *,
    intent_id: str,
    fill: Fill,
    fields: _CowPairIntentFields,
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(fill.amount_in_filled) or int(fill.amount_in_filled or 0) != fields.amount_in:
        return None, f"COW_NETTED amount_in_filled mismatch: intent_id={intent_id}"
    return int(fill.amount_in_filled or 0), None


def _parse_cow_pair_amount_out_filled(
    *,
    intent_id: str,
    fill: Fill,
    fields: _CowPairIntentFields,
) -> Tuple[Optional[int], Optional[str]]:
    if not is_strict_int(fill.amount_out_filled):
        return None, f"COW_NETTED amount_out_filled invalid: intent_id={intent_id}"
    out_amt = int(fill.amount_out_filled or 0)
    if out_amt < fields.min_out:
        return None, f"COW_NETTED slippage: intent_id={intent_id}"
    return out_amt, None


def _parse_cow_pair_fill_amounts(
    *,
    intent_id: str,
    fill: Fill,
    fields: _CowPairIntentFields,
) -> Tuple[Optional[_CowPairFillAmounts], Optional[str]]:
    err = _check_cow_pair_fill_fee(intent_id=intent_id, fill=fill)
    if err is not None:
        return None, err
    amount_in_filled, err = _parse_cow_pair_amount_in_filled(intent_id=intent_id, fill=fill, fields=fields)
    if amount_in_filled is None:
        return None, err
    amount_out_filled, err = _parse_cow_pair_amount_out_filled(intent_id=intent_id, fill=fill, fields=fields)
    if amount_out_filled is None:
        return None, err
    return _CowPairFillAmounts(amount_in_filled=amount_in_filled, amount_out_filled=amount_out_filled), None


def _parse_cow_pair_entry(
    *,
    intent_id: str,
    intent: Intent,
    fill: Fill,
) -> Tuple[Optional[_CowPairEntry], Optional[str]]:
    shape_error = _validate_cow_pair_shape(intent_id=intent_id, intent=intent, fill=fill)
    if shape_error is not None:
        return None, shape_error
    fields, field_error = _parse_cow_pair_intent_fields(intent_id=intent_id, intent=intent)
    if fields is None:
        return None, field_error
    amounts, amount_error = _parse_cow_pair_fill_amounts(intent_id=intent_id, fill=fill, fields=fields)
    if amounts is None:
        return None, amount_error
    return (
        _CowPairEntry(
            intent_id=intent_id,
            pool_id=fields.pool_id,
            asset_in=fields.asset_in,
            asset_out=fields.asset_out,
            amount_in_filled=amounts.amount_in_filled,
            amount_out_filled=amounts.amount_out_filled,
        ),
        None,
    )


def _build_cow_pair_entries(
    *,
    cow_ids: List[str],
    intents_by_id: Dict[str, Intent],
    fill_by_id: Dict[str, Fill],
) -> Tuple[Optional[Dict[str, _CowPairEntry]], Optional[str]]:
    entries: Dict[str, _CowPairEntry] = {}
    for intent_id in cow_ids:
        entry, err = _parse_cow_pair_entry(
            intent_id=intent_id,
            intent=intents_by_id[intent_id],
            fill=fill_by_id[intent_id],
        )
        if entry is None:
            return None, err or f"COW_NETTED amount_out_filled invalid: intent_id={intent_id}"
        entries[intent_id] = entry
    return entries, None


def _index_cow_pair_entries(entries: Dict[str, _CowPairEntry]) -> Dict[_CowPairKey, List[str]]:
    indexed: Dict[_CowPairKey, List[str]] = {}
    for intent_id, entry in entries.items():
        indexed.setdefault(_cow_pair_key(entry), []).append(intent_id)
    return indexed


def _validate_cow_pair_reciprocity(entries: Dict[str, _CowPairEntry]) -> Tuple[bool, Optional[str]]:
    # Indexed reciprocal lookup preserves the legacy match list order while
    # keeping matching linear in the number of COW fills.
    indexed = _index_cow_pair_entries(entries)
    pair_for: Dict[str, str] = {}
    for intent_id, entry in entries.items():
        matches = [other_id for other_id in indexed.get(_cow_pair_reciprocal_key(entry), []) if other_id != intent_id]
        if len(matches) != 1:
            return (
                False,
                f"COW_NETTED fill requires exactly one reciprocal counterparty: intent_id={intent_id} matches={matches}",
            )
        pair_for[intent_id] = matches[0]

    for intent_id, counterparty_id in pair_for.items():
        if pair_for.get(counterparty_id) != intent_id:
            return False, f"COW_NETTED reciprocal pair is not symmetric: intent_id={intent_id}"
    return True, None


def validate_cow_pair_index(
    *,
    settlement: Settlement,
    intents_by_id: Dict[str, Intent],
    fill_by_id: Dict[str, Fill],
    allow_cow_netting: bool,
) -> Tuple[bool, Optional[str]]:
    cow_ids = [fill.intent_id for fill in settlement.fills if fill.reason == "COW_NETTED"]
    if not cow_ids:
        return True, None
    if not allow_cow_netting:
        return False, f"COW_NETTED not allowed for intent_id={cow_ids[0]}"

    entries, err = _build_cow_pair_entries(
        cow_ids=cow_ids,
        intents_by_id=intents_by_id,
        fill_by_id=fill_by_id,
    )
    if entries is None:
        return False, err
    return _validate_cow_pair_reciprocity(entries)
