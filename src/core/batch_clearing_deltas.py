"""Pure settlement delta aggregation helpers for batch clearing."""

from __future__ import annotations

from typing import Dict, List, Tuple

from ..state.balances import Amount, AssetId, PubKey
from .settlement import BalanceDelta, LPDelta, ReserveDelta


def _aggregate_balance_deltas_chunked(
    deltas: List[BalanceDelta], *, chunk_size: int
) -> List[BalanceDelta]:
    global_acc: Dict[Tuple[PubKey, AssetId], Tuple[Amount, Amount]] = {}
    step = max(1, int(chunk_size))
    for i in range(0, len(deltas), step):
        chunk_acc: Dict[Tuple[PubKey, AssetId], Tuple[Amount, Amount]] = {}
        for d in deltas[i : i + step]:
            key = (d.pubkey, d.asset)
            add_prev, sub_prev = chunk_acc.get(key, (0, 0))
            chunk_acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
        for key, (add_chunk, sub_chunk) in chunk_acc.items():
            add_prev, sub_prev = global_acc.get(key, (0, 0))
            global_acc[key] = (int(add_prev) + int(add_chunk), int(sub_prev) + int(sub_chunk))

    out: List[BalanceDelta] = []
    for key in sorted(global_acc.keys()):
        delta_add, delta_sub = global_acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(BalanceDelta(pubkey=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _aggregate_reserve_deltas_chunked(
    deltas: List[ReserveDelta], *, chunk_size: int
) -> List[ReserveDelta]:
    global_acc: Dict[Tuple[str, AssetId], Tuple[Amount, Amount]] = {}
    step = max(1, int(chunk_size))
    for i in range(0, len(deltas), step):
        chunk_acc: Dict[Tuple[str, AssetId], Tuple[Amount, Amount]] = {}
        for d in deltas[i : i + step]:
            key = (d.pool_id, d.asset)
            add_prev, sub_prev = chunk_acc.get(key, (0, 0))
            chunk_acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
        for key, (add_chunk, sub_chunk) in chunk_acc.items():
            add_prev, sub_prev = global_acc.get(key, (0, 0))
            global_acc[key] = (int(add_prev) + int(add_chunk), int(sub_prev) + int(sub_chunk))

    out: List[ReserveDelta] = []
    for key in sorted(global_acc.keys()):
        delta_add, delta_sub = global_acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(ReserveDelta(pool_id=key[0], asset=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out


def _aggregate_lp_deltas_chunked(deltas: List[LPDelta], *, chunk_size: int) -> List[LPDelta]:
    global_acc: Dict[Tuple[PubKey, str], Tuple[Amount, Amount]] = {}
    step = max(1, int(chunk_size))
    for i in range(0, len(deltas), step):
        chunk_acc: Dict[Tuple[PubKey, str], Tuple[Amount, Amount]] = {}
        for d in deltas[i : i + step]:
            key = (d.pubkey, d.pool_id)
            add_prev, sub_prev = chunk_acc.get(key, (0, 0))
            chunk_acc[key] = (int(add_prev) + int(d.delta_add), int(sub_prev) + int(d.delta_sub))
        for key, (add_chunk, sub_chunk) in chunk_acc.items():
            add_prev, sub_prev = global_acc.get(key, (0, 0))
            global_acc[key] = (int(add_prev) + int(add_chunk), int(sub_prev) + int(sub_chunk))

    out: List[LPDelta] = []
    for key in sorted(global_acc.keys()):
        delta_add, delta_sub = global_acc[key]
        if delta_add == 0 and delta_sub == 0:
            continue
        out.append(LPDelta(pubkey=key[0], pool_id=key[1], delta_add=int(delta_add), delta_sub=int(delta_sub)))
    return out
