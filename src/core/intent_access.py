"""
Intent read/write access sets (for commutativity / quotient reasoning).

This module computes conservative state access sets for a batch of intents.
Two intents that touch disjoint state can be treated as commuting (under a
chosen semantics), enabling partial-order reductions and parallel verification.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, List, Mapping, Optional, Sequence, Set, Tuple

from ..state.balances import AssetId, PubKey
from ..state.intents import Intent, IntentKind
from ..state.pools import PoolState, compute_pool_id


_Key = Tuple[str, str, str]


def _k_bal(pubkey: PubKey, asset: AssetId) -> _Key:
    return ("BAL", pubkey, asset)


def _k_pool(pool_id: str) -> _Key:
    return ("POL", pool_id, "")


def _k_lp(pubkey: PubKey, pool_id: str) -> _Key:
    return ("LPB", pubkey, pool_id)


LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48


@dataclass(frozen=True)
class IntentAccess:
    reads: Set[_Key]
    writes: Set[_Key]


def _created_pools_assets(intents: Sequence[Intent]) -> Mapping[str, Tuple[str, str]]:
    out: dict[str, Tuple[str, str]] = {}
    for intent in intents:
        if intent.kind != IntentKind.CREATE_POOL:
            continue
        asset0 = intent.get_field("asset0")
        asset1 = intent.get_field("asset1")
        fee_bps = intent.get_field("fee_bps")
        if not isinstance(asset0, str) or not asset0:
            continue
        if not isinstance(asset1, str) or not asset1:
            continue
        if not isinstance(fee_bps, int) or isinstance(fee_bps, bool):
            continue
        try:
            pool_id = compute_pool_id(asset0, asset1, fee_bps, curve_tag="CPMM", curve_params="")
        except Exception:
            continue
        out[pool_id] = (asset0, asset1)
    return out


def access_for_intent(
    intent: Intent,
    *,
    pools: Mapping[str, PoolState],
    created_pools: Mapping[str, Tuple[str, str]],
) -> IntentAccess:
    reads: set[_Key] = set()
    writes: set[_Key] = set()

    sender = intent.sender_pubkey

    if intent.kind == IntentKind.CREATE_POOL:
        asset0 = intent.get_field("asset0")
        asset1 = intent.get_field("asset1")
        fee_bps = intent.get_field("fee_bps")
        if isinstance(asset0, str) and asset0:
            reads.add(_k_bal(sender, asset0))
            writes.add(_k_bal(sender, asset0))
        if isinstance(asset1, str) and asset1:
            reads.add(_k_bal(sender, asset1))
            writes.add(_k_bal(sender, asset1))
        if isinstance(asset0, str) and isinstance(asset1, str) and isinstance(fee_bps, int) and not isinstance(fee_bps, bool):
            try:
                pool_id = compute_pool_id(asset0, asset1, fee_bps, curve_tag="CPMM", curve_params="")
                reads.add(_k_pool(pool_id))  # existence check
                writes.add(_k_pool(pool_id))  # create
                writes.add(_k_lp(sender, pool_id))
                writes.add(_k_lp(LP_LOCK_PUBKEY, pool_id))
            except Exception:
                pass
        return IntentAccess(reads=reads, writes=writes)

    pool_id = intent.get_field("pool_id")
    if isinstance(pool_id, str) and pool_id:
        reads.add(_k_pool(pool_id))
        writes.add(_k_pool(pool_id))

    if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        asset_in = intent.get_field("asset_in")
        asset_out = intent.get_field("asset_out")
        recipient = intent.get_field("recipient", sender)
        if isinstance(asset_in, str) and asset_in:
            reads.add(_k_bal(sender, asset_in))
            writes.add(_k_bal(sender, asset_in))
        if isinstance(asset_out, str) and asset_out and isinstance(recipient, str) and recipient:
            writes.add(_k_bal(recipient, asset_out))
        return IntentAccess(reads=reads, writes=writes)

    if intent.kind == IntentKind.ADD_LIQUIDITY:
        recipient = intent.get_field("recipient", sender)
        if isinstance(pool_id, str) and pool_id:
            asset_pair: Optional[Tuple[str, str]] = None
            if pool_id in pools:
                pool = pools[pool_id]
                asset_pair = (pool.asset0, pool.asset1)
            elif pool_id in created_pools:
                asset_pair = created_pools[pool_id]
            if asset_pair is not None:
                a0, a1 = asset_pair
                reads.add(_k_bal(sender, a0))
                reads.add(_k_bal(sender, a1))
                writes.add(_k_bal(sender, a0))
                writes.add(_k_bal(sender, a1))
                if isinstance(recipient, str) and recipient:
                    writes.add(_k_lp(recipient, pool_id))
        return IntentAccess(reads=reads, writes=writes)

    if intent.kind == IntentKind.REMOVE_LIQUIDITY:
        recipient = intent.get_field("recipient", sender)
        if isinstance(pool_id, str) and pool_id:
            reads.add(_k_lp(sender, pool_id))
            writes.add(_k_lp(sender, pool_id))
            asset_pair: Optional[Tuple[str, str]] = None
            if pool_id in pools:
                pool = pools[pool_id]
                asset_pair = (pool.asset0, pool.asset1)
            elif pool_id in created_pools:
                asset_pair = created_pools[pool_id]
            if asset_pair is not None and isinstance(recipient, str) and recipient:
                a0, a1 = asset_pair
                writes.add(_k_bal(recipient, a0))
                writes.add(_k_bal(recipient, a1))
        return IntentAccess(reads=reads, writes=writes)

    return IntentAccess(reads=reads, writes=writes)


def intents_conflict(a: IntentAccess, b: IntentAccess) -> bool:
    b_touch = b.reads | b.writes
    a_touch = a.reads | a.writes
    return bool(a.writes & b_touch) or bool(b.writes & a_touch)


def partition_independent_intents(
    intents: Sequence[Intent],
    *,
    pools: Mapping[str, PoolState],
) -> List[List[Intent]]:
    """
    Partition intents into connected components under the conflict relation.

    Returns groups in deterministic order (by smallest intent_id in each group).
    """
    created = _created_pools_assets(intents)
    accesses = [access_for_intent(i, pools=pools, created_pools=created) for i in intents]

    parent = list(range(len(intents)))

    def find(x: int) -> int:
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    def union(x: int, y: int) -> None:
        rx = find(x)
        ry = find(y)
        if rx != ry:
            parent[ry] = rx

    for i in range(len(intents)):
        for j in range(i + 1, len(intents)):
            if intents_conflict(accesses[i], accesses[j]):
                union(i, j)

    groups: dict[int, list[int]] = {}
    for i in range(len(intents)):
        r = find(i)
        groups.setdefault(r, []).append(i)

    out: list[list[Intent]] = []
    for idxs in groups.values():
        out.append([intents[i] for i in idxs])

    out.sort(key=lambda g: min(i.intent_id for i in g))
    return out


def iter_group_support_keys(groups: Sequence[Sequence[Intent]]) -> Iterable[Tuple[int, str]]:
    """
    Helper for debugging: yields (group_index, intent_id) in stable order.
    """
    for gi, group in enumerate(groups):
        for intent in sorted(group, key=lambda i: i.intent_id):
            yield gi, intent.intent_id

