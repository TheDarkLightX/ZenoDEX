"""
Deterministic state root hashing (v1).

This is intended for:
- debugging / audit (stable hashes for the same logical state),
- parity checking between kernels (Python vs reference models),
- future integration where state commitment is required.
"""

from __future__ import annotations

from typing import Mapping

from .balances import BalanceTable
from .canonical import domain_sep_bytes, encode_bytes, encode_uvarint, hex_to_bytes_fixed, sha256_hex
from .lp import LPTable
from .pools import PoolState, PoolStatus


STATE_ROOT_VERSION = 1

_POOL_STATUS_CODE: dict[PoolStatus, int] = {
    PoolStatus.ACTIVE: 1,
    PoolStatus.FROZEN: 2,
    PoolStatus.DISABLED: 3,
}


def _sorted_balance_entries(balances: BalanceTable) -> list[tuple[bytes, bytes, int]]:
    entries: list[tuple[bytes, bytes, int]] = []
    seen: set[tuple[bytes, bytes]] = set()
    for (pubkey, asset), amount in balances.get_all_balances().items():
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        asset_b = hex_to_bytes_fixed(asset, nbytes=32, name="asset")
        key = (pk_b, asset_b)
        if key in seen:
            raise ValueError("duplicate decoded (pubkey, asset) in balances")
        seen.add(key)
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError(f"invalid balance amount: {amount!r}")
        entries.append((pk_b, asset_b, amount))
    entries.sort(key=lambda t: (t[0], t[1]))
    return entries


def _sorted_lp_entries(lp_balances: LPTable) -> list[tuple[bytes, bytes, int]]:
    entries: list[tuple[bytes, bytes, int]] = []
    seen: set[tuple[bytes, bytes]] = set()
    for (pubkey, pool_id), amount in lp_balances.get_all_balances().items():
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        pool_b = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        key = (pk_b, pool_b)
        if key in seen:
            raise ValueError("duplicate decoded (pubkey, pool_id) in lp_balances")
        seen.add(key)
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise ValueError(f"invalid LP amount: {amount!r}")
        entries.append((pk_b, pool_b, amount))
    entries.sort(key=lambda t: (t[0], t[1]))
    return entries


def _sorted_pool_entries(pools: Mapping[str, PoolState]) -> list[tuple[bytes, PoolState]]:
    entries: list[tuple[bytes, PoolState]] = []
    seen: set[bytes] = set()
    for pool_id, pool in pools.items():
        pool_b = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        if pool_b in seen:
            raise ValueError("duplicate decoded pool_id in pools")
        seen.add(pool_b)
        if pool.pool_id != pool_id:
            raise ValueError(f"pool_id mismatch: key={pool_id} pool.pool_id={pool.pool_id}")
        entries.append((pool_b, pool))
    entries.sort(key=lambda t: t[0])
    return entries


def _encode_balances_section(balances: BalanceTable) -> bytes:
    out = bytearray()
    entries = _sorted_balance_entries(balances)
    out += encode_uvarint(len(entries))
    for pk_b, asset_b, amount in entries:
        out += pk_b
        out += asset_b
        out += encode_uvarint(amount)
    return bytes(out)


def _encode_pools_section(pools: Mapping[str, PoolState]) -> bytes:
    out = bytearray()
    entries = _sorted_pool_entries(pools)
    out += encode_uvarint(len(entries))
    for pool_b, pool in entries:
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

        out += pool_b
        out += asset0_b
        out += asset1_b
        out += encode_uvarint(pool.reserve0)
        out += encode_uvarint(pool.reserve1)
        out += encode_uvarint(pool.fee_bps)
        out += encode_uvarint(pool.lp_supply)
        out += encode_uvarint(status_code)
        out += encode_uvarint(pool.created_at)

    return bytes(out)


def _encode_lp_section(lp_balances: LPTable) -> bytes:
    out = bytearray()
    entries = _sorted_lp_entries(lp_balances)
    out += encode_uvarint(len(entries))
    for pk_b, pool_b, amount in entries:
        out += pk_b
        out += pool_b
        out += encode_uvarint(amount)
    return bytes(out)


def compute_state_root(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
) -> str:
    """
    Compute a deterministic state root hash for the DEX state.

    Returns a 0x-prefixed sha256 digest.
    """
    if not isinstance(balances, BalanceTable):
        raise TypeError("balances must be a BalanceTable")
    if not isinstance(lp_balances, LPTable):
        raise TypeError("lp_balances must be an LPTable")

    balances_section = _encode_balances_section(balances)
    pools_section = _encode_pools_section(pools)
    lp_section = _encode_lp_section(lp_balances)

    payload = (
        domain_sep_bytes("state_root", version=STATE_ROOT_VERSION)
        + b"BAL"
        + encode_bytes(balances_section)
        + b"POL"
        + encode_bytes(pools_section)
        + b"LPB"
        + encode_bytes(lp_section)
    )
    return sha256_hex(payload)
