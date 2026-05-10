"""
Deterministic state root hashing (v4).

This is intended for:
- debugging / audit (stable hashes for the same logical state),
- parity checking between kernels (Python vs reference models),
- future integration where state commitment is required.
"""

from __future__ import annotations

from typing import Mapping

from .balances import BalanceTable
from .canonical import (
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)
from .lp import LPDurationRiskMetadata, LPTable
from .nonces import NonceTable
from .pools import POOL_FEE_BPS_MAX, PoolState, PoolStatus

STATE_ROOT_VERSION = 4

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


def _sorted_lp_duration_risk_entries(
    lp_balances: LPTable,
) -> list[tuple[bytes, bytes, LPDurationRiskMetadata]]:
    entries: list[tuple[bytes, bytes, LPDurationRiskMetadata]] = []
    seen: set[tuple[bytes, bytes]] = set()
    for (pubkey, pool_id), metadata in lp_balances.get_all_duration_risk_metadata().items():
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        pool_b = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        key = (pk_b, pool_b)
        if key in seen:
            raise ValueError("duplicate decoded (pubkey, pool_id) in lp_duration_risk")
        seen.add(key)
        for name, timestamp in (
            ("LP mint timestamp", metadata.last_mint_timestamp),
            ("LP remove timestamp", metadata.last_remove_timestamp),
            ("LP churn update timestamp", metadata.last_churn_update_timestamp),
        ):
            if timestamp is not None and (
                not isinstance(timestamp, int) or isinstance(timestamp, bool) or timestamp < 0
            ):
                raise ValueError(f"invalid {name}: {timestamp!r}")
        if (
            not isinstance(metadata.churn_tier, int)
            or isinstance(metadata.churn_tier, bool)
            or metadata.churn_tier < 0
        ):
            raise ValueError(f"invalid LP churn tier: {metadata.churn_tier!r}")
        entries.append((pk_b, pool_b, metadata))
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
        if pool.fee_bps > POOL_FEE_BPS_MAX:
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
        out += encode_bytes(pool.curve_tag.encode("utf-8"))
        out += encode_bytes(pool.curve_params.encode("utf-8"))

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


def _encode_lp_duration_risk_section(lp_balances: LPTable) -> bytes:
    out = bytearray()
    entries = _sorted_lp_duration_risk_entries(lp_balances)
    out += encode_uvarint(len(entries))
    for pk_b, pool_b, metadata in entries:
        out += pk_b
        out += pool_b
        for timestamp in (
            metadata.last_mint_timestamp,
            metadata.last_remove_timestamp,
        ):
            out += encode_uvarint(1 if timestamp is not None else 0)
            if timestamp is not None:
                out += encode_uvarint(timestamp)
        out += encode_uvarint(metadata.churn_tier)
        out += encode_uvarint(1 if metadata.last_churn_update_timestamp is not None else 0)
        if metadata.last_churn_update_timestamp is not None:
            out += encode_uvarint(metadata.last_churn_update_timestamp)
    return bytes(out)


def _encode_nonce_section(nonces: NonceTable) -> bytes:
    out = bytearray()
    entries: list[tuple[bytes, int]] = []
    seen: set[bytes] = set()
    for pubkey, last_nonce in nonces.get_all().items():
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        if pk_b in seen:
            raise ValueError("duplicate decoded pubkey in nonces")
        seen.add(pk_b)
        if not isinstance(last_nonce, int) or isinstance(last_nonce, bool) or last_nonce < 0:
            raise ValueError(f"invalid nonce amount: {last_nonce!r}")
        entries.append((pk_b, last_nonce))
    entries.sort(key=lambda t: t[0])
    out += encode_uvarint(len(entries))
    for pk_b, last_nonce in entries:
        out += pk_b
        out += encode_uvarint(last_nonce)
    return bytes(out)


def compute_state_root(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    nonces: NonceTable | None = None,
) -> str:
    """
    Compute a deterministic state root hash for the DEX state.

    Returns a 0x-prefixed sha256 digest.
    """
    if not isinstance(balances, BalanceTable):
        raise TypeError("balances must be a BalanceTable")
    if not isinstance(lp_balances, LPTable):
        raise TypeError("lp_balances must be an LPTable")
    nonce_table = NonceTable() if nonces is None else nonces
    if not isinstance(nonce_table, NonceTable):
        raise TypeError("nonces must be a NonceTable")

    balances_section = _encode_balances_section(balances)
    pools_section = _encode_pools_section(pools)
    lp_section = _encode_lp_section(lp_balances)
    lp_duration_risk_section = _encode_lp_duration_risk_section(lp_balances)
    nonce_section = _encode_nonce_section(nonce_table)

    payload = (
        domain_sep_bytes("state_root", version=STATE_ROOT_VERSION)
        + b"BAL"
        + encode_bytes(balances_section)
        + b"POL"
        + encode_bytes(pools_section)
        + b"LPB"
        + encode_bytes(lp_section)
        + b"LPA"
        + encode_bytes(lp_duration_risk_section)
        + b"NNC"
        + encode_bytes(nonce_section)
    )
    return sha256_hex(payload)
