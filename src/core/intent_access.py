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
from ..state.pools import PoolState, compute_pool_id, normalize_curve_config

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


@dataclass(frozen=True)
class _PoolAccessContext:
    pool_id: object
    pools: Mapping[str, PoolState]
    created_pools: Mapping[str, Tuple[str, str]]
    reads: set[_Key]
    writes: set[_Key]


def _created_pool_assets_entry(intent: Intent) -> Optional[Tuple[str, Tuple[str, str]]]:
    if intent.kind != IntentKind.CREATE_POOL:
        return None
    asset0 = intent.get_field("asset0")
    asset1 = intent.get_field("asset1")
    if not isinstance(asset0, str) or not asset0:
        return None
    if not isinstance(asset1, str) or not asset1:
        return None
    pool_id = _created_pool_id(intent)
    if pool_id is None:
        return None
    return pool_id, (asset0, asset1)


def _created_pools_assets(intents: Sequence[Intent]) -> Mapping[str, Tuple[str, str]]:
    out: dict[str, Tuple[str, str]] = {}
    for intent in intents:
        entry = _created_pool_assets_entry(intent)
        if entry is None:
            continue
        pool_id, assets = entry
        out[pool_id] = assets
    return out


def _touch_balance(reads: set[_Key], writes: set[_Key], pubkey: PubKey, asset: object) -> None:
    if not isinstance(asset, str) or not asset:
        return
    key = _k_bal(pubkey, asset)
    reads.add(key)
    writes.add(key)


def _created_pool_id(intent: Intent) -> Optional[str]:
    asset0 = intent.get_field("asset0")
    asset1 = intent.get_field("asset1")
    fee_bps = intent.get_field("fee_bps")
    if not isinstance(asset0, str) or not asset0:
        return None
    if not isinstance(asset1, str) or not asset1:
        return None
    if not isinstance(fee_bps, int) or isinstance(fee_bps, bool):
        return None
    curve_tag = intent.get_field("curve_tag", None)
    curve_params = intent.get_wire_field("curve_params", None)
    try:
        curve_tag_norm, curve_params_norm = normalize_curve_config(
            curve_tag=curve_tag,
            curve_params=curve_params,
        )
        return compute_pool_id(
            asset0,
            asset1,
            fee_bps,
            curve_tag=curve_tag_norm,
            curve_params=curve_params_norm,
        )
    except (TypeError, ValueError):
        return None


def _asset_pair_for_pool(
    *,
    pool_id: str,
    pools: Mapping[str, PoolState],
    created_pools: Mapping[str, Tuple[str, str]],
) -> Optional[Tuple[str, str]]:
    if pool_id in pools:
        pool = pools[pool_id]
        return pool.asset0, pool.asset1
    return created_pools.get(pool_id)


def _access_for_create_pool(intent: Intent) -> IntentAccess:
    reads: set[_Key] = set()
    writes: set[_Key] = set()
    sender = intent.sender_pubkey
    asset0 = intent.get_field("asset0")
    asset1 = intent.get_field("asset1")
    _touch_balance(reads, writes, sender, asset0)
    _touch_balance(reads, writes, sender, asset1)

    pool_id = _created_pool_id(intent)
    if pool_id is not None:
        reads.add(_k_pool(pool_id))  # existence check
        writes.add(_k_pool(pool_id))  # create
        writes.add(_k_lp(sender, pool_id))
        writes.add(_k_lp(LP_LOCK_PUBKEY, pool_id))
    return IntentAccess(reads=reads, writes=writes)


def _access_for_swap(intent: Intent, *, reads: set[_Key], writes: set[_Key]) -> IntentAccess:
    sender = intent.sender_pubkey
    asset_in = intent.get_field("asset_in")
    asset_out = intent.get_field("asset_out")
    recipient = intent.get_field("recipient", sender)
    _touch_balance(reads, writes, sender, asset_in)
    if isinstance(asset_out, str) and asset_out and isinstance(recipient, str) and recipient:
        writes.add(_k_bal(recipient, asset_out))
    return IntentAccess(reads=reads, writes=writes)


def _access_for_add_liquidity(
    intent: Intent,
    *,
    context: _PoolAccessContext,
) -> IntentAccess:
    recipient = intent.get_field("recipient", intent.sender_pubkey)
    pool_id = context.pool_id
    if not isinstance(pool_id, str) or not pool_id:
        return IntentAccess(reads=context.reads, writes=context.writes)

    asset_pair = _asset_pair_for_pool(pool_id=pool_id, pools=context.pools, created_pools=context.created_pools)
    if asset_pair is None:
        return IntentAccess(reads=context.reads, writes=context.writes)

    a0, a1 = asset_pair
    _touch_balance(context.reads, context.writes, intent.sender_pubkey, a0)
    _touch_balance(context.reads, context.writes, intent.sender_pubkey, a1)
    if isinstance(recipient, str) and recipient:
        context.writes.add(_k_lp(recipient, pool_id))
    return IntentAccess(reads=context.reads, writes=context.writes)


def _access_for_remove_liquidity(
    intent: Intent,
    *,
    context: _PoolAccessContext,
) -> IntentAccess:
    recipient = intent.get_field("recipient", intent.sender_pubkey)
    pool_id = context.pool_id
    if not isinstance(pool_id, str) or not pool_id:
        return IntentAccess(reads=context.reads, writes=context.writes)

    context.reads.add(_k_lp(intent.sender_pubkey, pool_id))
    context.writes.add(_k_lp(intent.sender_pubkey, pool_id))
    asset_pair = _asset_pair_for_pool(pool_id=pool_id, pools=context.pools, created_pools=context.created_pools)
    if asset_pair is not None and isinstance(recipient, str) and recipient:
        a0, a1 = asset_pair
        context.writes.add(_k_bal(recipient, a0))
        context.writes.add(_k_bal(recipient, a1))
    return IntentAccess(reads=context.reads, writes=context.writes)


def access_for_intent(
    intent: Intent,
    *,
    pools: Mapping[str, PoolState],
    created_pools: Mapping[str, Tuple[str, str]],
) -> IntentAccess:
    reads: set[_Key] = set()
    writes: set[_Key] = set()

    if intent.kind == IntentKind.CREATE_POOL:
        return _access_for_create_pool(intent)

    pool_id = intent.get_field("pool_id")
    if isinstance(pool_id, str) and pool_id:
        reads.add(_k_pool(pool_id))
        writes.add(_k_pool(pool_id))

    if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
        return _access_for_swap(intent, reads=reads, writes=writes)

    if intent.kind == IntentKind.ADD_LIQUIDITY:
        return _access_for_add_liquidity(
            intent,
            context=_PoolAccessContext(
                pool_id=pool_id,
                pools=pools,
                created_pools=created_pools,
                reads=reads,
                writes=writes,
            ),
        )

    if intent.kind == IntentKind.REMOVE_LIQUIDITY:
        return _access_for_remove_liquidity(
            intent,
            context=_PoolAccessContext(
                pool_id=pool_id,
                pools=pools,
                created_pools=created_pools,
                reads=reads,
                writes=writes,
            ),
        )

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
