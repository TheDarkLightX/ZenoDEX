"""
Projected (support) state commitments for quotient-style verification.

This module defines a smaller "state root" that commits only to the subset of
state that a batch needs to read in order to validate and recompute settlement.

Intuition: quotient the full state space by an equivalence relation:
  s ~ t  iff  s and t agree on the batch's support (read-set).

This enables proof/certificate schemes whose witness carries only a projected
snapshot instead of the entire global state.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping, Sequence, Tuple

from .balances import AssetId, BalanceTable, PubKey
from .canonical import domain_sep_bytes, encode_bytes, encode_uvarint, hex_to_bytes_fixed, sha256_hex
from .intents import Intent, IntentKind
from .lp import LPTable
from .pools import PoolState, PoolStatus, compute_pool_id


SUPPORT_ROOT_VERSION = 1

LP_LOCK_PUBKEY: PubKey = "0x" + "00" * 48

_POOL_STATUS_CODE: dict[PoolStatus, int] = {
    PoolStatus.ACTIVE: 1,
    PoolStatus.FROZEN: 2,
    PoolStatus.DISABLED: 3,
}


@dataclass(frozen=True)
class BatchStateSupport:
    """
    Deterministic, sorted support sets.

    These sets are intentionally *conservative* and can evolve over time; they
    are versioned by `SUPPORT_ROOT_VERSION`.
    """

    balance_keys: Tuple[Tuple[PubKey, AssetId], ...]
    pool_ids: Tuple[str, ...]
    lp_keys: Tuple[Tuple[PubKey, str], ...]


def derive_batch_state_support(
    intents: Sequence[Intent],
    *,
    pools: Mapping[str, PoolState],
) -> BatchStateSupport:
    """
    Derive the batch read-set from intents (and pool metadata, when needed).

    The support is used to compute a projected pre-state commitment (support root).
    """
    balance_keys: set[tuple[str, str]] = set()
    pool_ids: set[str] = set()
    lp_keys: set[tuple[str, str]] = set()

    created_pool_assets: dict[str, tuple[str, str]] = {}
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
        created_pool_assets[pool_id] = (asset0, asset1)

    for intent in intents:
        sender = intent.sender_pubkey

        if intent.kind == IntentKind.CREATE_POOL:
            asset0 = intent.get_field("asset0")
            asset1 = intent.get_field("asset1")
            fee_bps = intent.get_field("fee_bps")
            if isinstance(asset0, str) and isinstance(asset1, str):
                balance_keys.add((sender, asset0))
                balance_keys.add((sender, asset1))
                if isinstance(fee_bps, int) and not isinstance(fee_bps, bool):
                    try:
                        pool_id = compute_pool_id(asset0, asset1, fee_bps, curve_tag="CPMM", curve_params="")
                        pool_ids.add(pool_id)
                    except Exception:
                        # Invalid CREATE_POOL params; keep support minimal and let validation reject.
                        pass
            continue

        pool_id = intent.get_field("pool_id")
        if isinstance(pool_id, str) and pool_id:
            pool_ids.add(pool_id)

        if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            asset_in = intent.get_field("asset_in")
            if isinstance(asset_in, str) and asset_in:
                balance_keys.add((sender, asset_in))
            continue

        if intent.kind == IntentKind.ADD_LIQUIDITY:
            if isinstance(pool_id, str) and pool_id:
                if pool_id in pools:
                    pool = pools[pool_id]
                    balance_keys.add((sender, pool.asset0))
                    balance_keys.add((sender, pool.asset1))
                elif pool_id in created_pool_assets:
                    asset0, asset1 = created_pool_assets[pool_id]
                    balance_keys.add((sender, asset0))
                    balance_keys.add((sender, asset1))
            continue

        if intent.kind == IntentKind.REMOVE_LIQUIDITY:
            if isinstance(pool_id, str) and pool_id:
                lp_keys.add((sender, pool_id))
            continue

    return BatchStateSupport(
        balance_keys=tuple(sorted(balance_keys, key=lambda t: (t[0], t[1]))),
        pool_ids=tuple(sorted(pool_ids)),
        lp_keys=tuple(sorted(lp_keys, key=lambda t: (t[0], t[1]))),
    )


def compute_support_state_root(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    support: BatchStateSupport,
) -> str:
    """
    Compute a deterministic commitment over the batch's support.

    Entries with zero balance / missing pools are omitted, mirroring the full
    `compute_state_root()` sparsity behavior.
    """
    if not isinstance(balances, BalanceTable):
        raise TypeError("balances must be a BalanceTable")
    if not isinstance(lp_balances, LPTable):
        raise TypeError("lp_balances must be an LPTable")
    if not isinstance(support, BatchStateSupport):
        raise TypeError("support must be a BatchStateSupport")

    bal_out = bytearray()
    bal_entries: list[tuple[bytes, bytes, int]] = []
    bal_seen: set[tuple[bytes, bytes]] = set()
    for pubkey, asset in support.balance_keys:
        amount = balances.get(pubkey, asset)
        if amount == 0:
            continue
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        asset_b = hex_to_bytes_fixed(asset, nbytes=32, name="asset")
        key = (pk_b, asset_b)
        if key in bal_seen:
            raise ValueError("duplicate decoded (pubkey, asset) in support balances")
        bal_seen.add(key)
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError(f"invalid balance amount: {amount!r}")
        bal_entries.append((pk_b, asset_b, amount))
    bal_entries.sort(key=lambda t: (t[0], t[1]))
    bal_out += encode_uvarint(len(bal_entries))
    for pk_b, asset_b, amount in bal_entries:
        bal_out += pk_b
        bal_out += asset_b
        bal_out += encode_uvarint(amount)
    balances_section = bytes(bal_out)

    pool_out = bytearray()
    pool_entries: list[tuple[bytes, PoolState]] = []
    pool_seen: set[bytes] = set()
    for pool_id in support.pool_ids:
        pool = pools.get(pool_id)
        if pool is None:
            continue
        pool_b = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        if pool_b in pool_seen:
            raise ValueError("duplicate decoded pool_id in support pools")
        pool_seen.add(pool_b)
        if pool.pool_id != pool_id:
            raise ValueError(f"pool_id mismatch: key={pool_id} pool.pool_id={pool.pool_id}")
        pool_entries.append((pool_b, pool))
    pool_entries.sort(key=lambda t: t[0])
    pool_out += encode_uvarint(len(pool_entries))
    for pool_b, pool in pool_entries:
        asset0_b = hex_to_bytes_fixed(pool.asset0, nbytes=32, name="asset0")
        asset1_b = hex_to_bytes_fixed(pool.asset1, nbytes=32, name="asset1")
        status_code = _POOL_STATUS_CODE.get(pool.status)
        if status_code is None:
            raise ValueError(f"unknown pool status: {pool.status}")
        for name, v in (
            ("reserve0", pool.reserve0),
            ("reserve1", pool.reserve1),
            ("fee_bps", pool.fee_bps),
            ("lp_supply", pool.lp_supply),
            ("created_at", pool.created_at),
        ):
            if not isinstance(v, int) or isinstance(v, bool) or v < 0:
                raise ValueError(f"invalid pool {name}: {v!r}")
        if pool.fee_bps > 10_000:
            raise ValueError(f"invalid pool fee_bps: {pool.fee_bps!r}")
        pool_out += pool_b
        pool_out += asset0_b
        pool_out += asset1_b
        pool_out += encode_uvarint(pool.reserve0)
        pool_out += encode_uvarint(pool.reserve1)
        pool_out += encode_uvarint(pool.fee_bps)
        pool_out += encode_uvarint(pool.lp_supply)
        pool_out += encode_uvarint(status_code)
        pool_out += encode_uvarint(pool.created_at)
    pools_section = bytes(pool_out)

    lp_out = bytearray()
    lp_entries: list[tuple[bytes, bytes, int]] = []
    lp_seen: set[tuple[bytes, bytes]] = set()
    for pubkey, pool_id in support.lp_keys:
        amount = lp_balances.get(pubkey, pool_id)
        if amount == 0:
            continue
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        pool_b = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        key = (pk_b, pool_b)
        if key in lp_seen:
            raise ValueError("duplicate decoded (pubkey, pool_id) in support lp_balances")
        lp_seen.add(key)
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError(f"invalid LP amount: {amount!r}")
        lp_entries.append((pk_b, pool_b, amount))
    lp_entries.sort(key=lambda t: (t[0], t[1]))
    lp_out += encode_uvarint(len(lp_entries))
    for pk_b, pool_b, amount in lp_entries:
        lp_out += pk_b
        lp_out += pool_b
        lp_out += encode_uvarint(amount)
    lp_section = bytes(lp_out)

    payload = (
        domain_sep_bytes("state_support_root", version=SUPPORT_ROOT_VERSION)
        + b"BAL"
        + encode_bytes(balances_section)
        + b"POL"
        + encode_bytes(pools_section)
        + b"LPB"
        + encode_bytes(lp_section)
    )
    return sha256_hex(payload)


def compute_support_state_root_for_batch(
    *,
    intents: Sequence[Intent],
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
) -> str:
    support = derive_batch_state_support(intents, pools=pools)
    return compute_support_state_root(balances=balances, pools=pools, lp_balances=lp_balances, support=support)
