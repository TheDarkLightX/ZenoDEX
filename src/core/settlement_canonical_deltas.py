"""Canonical settlement delta aggregation and validation."""

from __future__ import annotations

from typing import Any, Callable, Dict, List, Optional, Tuple

from ..state.balances import AssetId, PubKey
from .domain_limits import is_strict_int
from .settlement import BalanceDelta, LPDelta, ReserveDelta, Settlement


def _require_non_negative_delta_limb(value: Any, *, what: str) -> int:
    if not is_strict_int(value):
        raise TypeError(f"{what} must be a non-negative int")
    if value < 0:
        raise TypeError(f"{what} must be a non-negative int")
    return int(value)


def aggregate_balance_deltas(deltas: List[BalanceDelta]) -> List[BalanceDelta]:
    acc: Dict[Tuple[PubKey, AssetId], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pubkey, d.asset)
        add_prev, sub_prev = acc.get(key, (0, 0))
        delta_add = _require_non_negative_delta_limb(d.delta_add, what="balance_deltas.delta_add")
        delta_sub = _require_non_negative_delta_limb(d.delta_sub, what="balance_deltas.delta_sub")
        acc[key] = (int(add_prev) + delta_add, int(sub_prev) + delta_sub)
    out: List[BalanceDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(BalanceDelta(pubkey=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def aggregate_reserve_deltas(deltas: List[ReserveDelta]) -> List[ReserveDelta]:
    acc: Dict[Tuple[str, AssetId], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pool_id, d.asset)
        add_prev, sub_prev = acc.get(key, (0, 0))
        delta_add = _require_non_negative_delta_limb(d.delta_add, what="reserve_deltas.delta_add")
        delta_sub = _require_non_negative_delta_limb(d.delta_sub, what="reserve_deltas.delta_sub")
        acc[key] = (int(add_prev) + delta_add, int(sub_prev) + delta_sub)
    out: List[ReserveDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(ReserveDelta(pool_id=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def aggregate_lp_deltas(deltas: List[LPDelta]) -> List[LPDelta]:
    acc: Dict[Tuple[PubKey, str], Tuple[int, int]] = {}
    for d in deltas:
        key = (d.pubkey, d.pool_id)
        add_prev, sub_prev = acc.get(key, (0, 0))
        delta_add = _require_non_negative_delta_limb(d.delta_add, what="lp_deltas.delta_add")
        delta_sub = _require_non_negative_delta_limb(d.delta_sub, what="lp_deltas.delta_sub")
        acc[key] = (int(add_prev) + delta_add, int(sub_prev) + delta_sub)
    out: List[LPDelta] = []
    for key in sorted(acc.keys()):
        delta_add, delta_sub = acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(LPDelta(pubkey=key[0], pool_id=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _check_unique_sorted_delta_keys(keys: List[Tuple], what: str) -> Tuple[bool, Optional[str]]:
    if keys != sorted(keys):
        return False, f"{what} not sorted canonically"
    if len(keys) != len(set(keys)):
        return False, f"{what} contains duplicate keys"
    return True, None


def _check_canonical_delta_entries(
    *,
    deltas: list[Any],
    what: str,
    key_fn: Callable[[Any], Tuple],
) -> Tuple[bool, Optional[str]]:
    keys: List[Tuple] = []
    for delta in deltas:
        delta_add = delta.delta_add
        delta_sub = delta.delta_sub
        if not is_strict_int(delta_add) or delta_add < 0:
            return False, f"{what} contains invalid delta_add"
        if not is_strict_int(delta_sub) or delta_sub < 0:
            return False, f"{what} contains invalid delta_sub"
        if delta_add == 0 and delta_sub == 0:
            return False, f"{what} contains a zero entry"
        keys.append(key_fn(delta))
    return _check_unique_sorted_delta_keys(keys, what)


def _check_canonical_balance_deltas(deltas: List[BalanceDelta]) -> Tuple[bool, Optional[str]]:
    return _check_canonical_delta_entries(
        deltas=list(deltas),
        what="balance_deltas",
        key_fn=lambda delta: (delta.pubkey, delta.asset),
    )


def _check_canonical_reserve_deltas(deltas: List[ReserveDelta]) -> Tuple[bool, Optional[str]]:
    return _check_canonical_delta_entries(
        deltas=list(deltas),
        what="reserve_deltas",
        key_fn=lambda delta: (delta.pool_id, delta.asset),
    )


def _check_canonical_lp_deltas(deltas: List[LPDelta]) -> Tuple[bool, Optional[str]]:
    return _check_canonical_delta_entries(
        deltas=list(deltas),
        what="lp_deltas",
        key_fn=lambda delta: (delta.pubkey, delta.pool_id),
    )


def check_canonical_deltas(settlement: Settlement) -> Tuple[bool, Optional[str]]:
    # Ensure deltas are canonical (one entry per key, sorted, and with non-negative fields).
    ok, err = _check_canonical_balance_deltas(settlement.balance_deltas)
    if not ok:
        return ok, err
    ok, err = _check_canonical_reserve_deltas(settlement.reserve_deltas)
    if not ok:
        return ok, err
    ok, err = _check_canonical_lp_deltas(settlement.lp_deltas)
    if not ok:
        return ok, err
    return True, None
