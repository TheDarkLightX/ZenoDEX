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
from .canonical import (
    domain_sep_bytes,
    encode_bytes,
    encode_uvarint,
    hex_to_bytes_fixed,
    sha256_hex,
)
from .intents import Intent, IntentKind
from .lp import LPDurationRiskMetadata, LPTable
from .nonces import NonceTable
from .pools import PoolState, PoolStatus, compute_pool_id, normalize_curve_config

SUPPORT_ROOT_VERSION = 4

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
    nonce_keys: Tuple[PubKey, ...]


@dataclass
class _SupportAccumulator:
    balance_keys: set[tuple[str, str]]
    pool_ids: set[str]
    lp_keys: set[tuple[str, str]]
    nonce_keys: set[str]


@dataclass
class _SupportDerivationContext:
    pools: Mapping[str, PoolState]
    created_pool_assets: Mapping[str, tuple[str, str]]
    acc: _SupportAccumulator


def _created_pool_id_for_intent(intent: Intent) -> str | None:
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


def _created_pool_assets_for_intents(intents: Sequence[Intent]) -> dict[str, tuple[str, str]]:
    created_pool_assets: dict[str, tuple[str, str]] = {}
    for intent in intents:
        if intent.kind != IntentKind.CREATE_POOL:
            continue
        asset0 = intent.get_field("asset0")
        asset1 = intent.get_field("asset1")
        if not isinstance(asset0, str) or not asset0:
            continue
        if not isinstance(asset1, str) or not asset1:
            continue
        pool_id = _created_pool_id_for_intent(intent)
        if pool_id is None:
            continue
        created_pool_assets[pool_id] = (asset0, asset1)
    return created_pool_assets


def _add_create_pool_support(intent: Intent, *, sender: str, acc: _SupportAccumulator) -> None:
    asset0 = intent.get_field("asset0")
    asset1 = intent.get_field("asset1")
    if not isinstance(asset0, str) or not isinstance(asset1, str):
        return

    acc.balance_keys.add((sender, asset0))
    acc.balance_keys.add((sender, asset1))
    pool_id = _created_pool_id_for_intent(intent)
    if pool_id is None:
        # Invalid CREATE_POOL params; keep support minimal and let validation reject.
        return
    acc.pool_ids.add(pool_id)


def _add_add_liquidity_support(
    intent: Intent,
    *,
    sender: str,
    pool_id: str,
    context: _SupportDerivationContext,
) -> None:
    recipient = intent.get_field("recipient", sender)
    if isinstance(recipient, str) and recipient:
        context.acc.lp_keys.add((recipient, pool_id))
    if pool_id in context.pools:
        pool = context.pools[pool_id]
        context.acc.balance_keys.add((sender, pool.asset0))
        context.acc.balance_keys.add((sender, pool.asset1))
    elif pool_id in context.created_pool_assets:
        asset0, asset1 = context.created_pool_assets[pool_id]
        context.acc.balance_keys.add((sender, asset0))
        context.acc.balance_keys.add((sender, asset1))


def derive_batch_state_support(
    intents: Sequence[Intent],
    *,
    pools: Mapping[str, PoolState],
) -> BatchStateSupport:
    """
    Derive the batch read-set from intents (and pool metadata, when needed).

    The support is used to compute a projected pre-state commitment (support root).
    """
    acc = _SupportAccumulator(balance_keys=set(), pool_ids=set(), lp_keys=set(), nonce_keys=set())
    created_pool_assets = _created_pool_assets_for_intents(intents)
    context = _SupportDerivationContext(pools=pools, created_pool_assets=created_pool_assets, acc=acc)

    for intent in intents:
        sender = intent.sender_pubkey
        acc.nonce_keys.add(sender)

        if intent.kind == IntentKind.CREATE_POOL:
            _add_create_pool_support(intent, sender=sender, acc=acc)
            continue

        pool_id = intent.get_field("pool_id")
        if isinstance(pool_id, str) and pool_id:
            acc.pool_ids.add(pool_id)

        if intent.kind in (IntentKind.SWAP_EXACT_IN, IntentKind.SWAP_EXACT_OUT):
            asset_in = intent.get_field("asset_in")
            if isinstance(asset_in, str) and asset_in:
                acc.balance_keys.add((sender, asset_in))
            continue

        if intent.kind == IntentKind.ADD_LIQUIDITY:
            if isinstance(pool_id, str) and pool_id:
                _add_add_liquidity_support(
                    intent,
                    sender=sender,
                    pool_id=pool_id,
                    context=context,
                )
            continue

        if intent.kind == IntentKind.REMOVE_LIQUIDITY:
            if isinstance(pool_id, str) and pool_id:
                acc.lp_keys.add((sender, pool_id))
            continue

    return BatchStateSupport(
        balance_keys=tuple(sorted(acc.balance_keys, key=lambda t: (t[0], t[1]))),
        pool_ids=tuple(sorted(acc.pool_ids)),
        lp_keys=tuple(sorted(acc.lp_keys, key=lambda t: (t[0], t[1]))),
        nonce_keys=tuple(sorted(acc.nonce_keys)),
    )


def _encode_support_balances_section(*, balances: BalanceTable, support: BatchStateSupport) -> bytes:
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
    return bytes(bal_out)


def _encode_support_pools_section(*, pools: Mapping[str, PoolState], support: BatchStateSupport) -> bytes:
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
        pool_out += encode_bytes(pool.curve_tag.encode("utf-8"))
        pool_out += encode_bytes(pool.curve_params.encode("utf-8"))
    return bytes(pool_out)


def _encode_support_lp_balances_section(*, lp_balances: LPTable, support: BatchStateSupport) -> bytes:
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
    return bytes(lp_out)


def _encode_support_lp_duration_section(*, lp_balances: LPTable, support: BatchStateSupport) -> bytes:
    lp_duration_out = bytearray()
    lp_duration_entries: list[tuple[bytes, bytes, LPDurationRiskMetadata]] = []
    lp_duration_seen: set[tuple[bytes, bytes]] = set()
    for pubkey, pool_id in support.lp_keys:
        metadata = lp_balances.get_duration_risk_metadata(pubkey, pool_id)
        if (
            metadata.last_mint_timestamp is None
            and metadata.last_remove_timestamp is None
            and metadata.churn_tier == 0
            and metadata.last_churn_update_timestamp is None
        ):
            continue
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        pool_b = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        key = (pk_b, pool_b)
        if key in lp_duration_seen:
            raise ValueError("duplicate decoded (pubkey, pool_id) in support lp_duration_risk")
        lp_duration_seen.add(key)
        for name, timestamp in (
            ("LP mint timestamp", metadata.last_mint_timestamp),
            ("LP remove timestamp", metadata.last_remove_timestamp),
            ("LP churn update timestamp", metadata.last_churn_update_timestamp),
        ):
            if timestamp is not None and (
                not isinstance(timestamp, int) or isinstance(timestamp, bool) or timestamp < 0
            ):
                raise ValueError(f"invalid support {name}: {timestamp!r}")
        if (
            not isinstance(metadata.churn_tier, int)
            or isinstance(metadata.churn_tier, bool)
            or metadata.churn_tier < 0
        ):
            raise ValueError(f"invalid support LP churn tier: {metadata.churn_tier!r}")
        lp_duration_entries.append((pk_b, pool_b, metadata))
    lp_duration_entries.sort(key=lambda t: (t[0], t[1]))
    lp_duration_out += encode_uvarint(len(lp_duration_entries))
    for pk_b, pool_b, metadata in lp_duration_entries:
        lp_duration_out += pk_b
        lp_duration_out += pool_b
        for timestamp in (
            metadata.last_mint_timestamp,
            metadata.last_remove_timestamp,
        ):
            lp_duration_out += encode_uvarint(1 if timestamp is not None else 0)
            if timestamp is not None:
                lp_duration_out += encode_uvarint(timestamp)
        lp_duration_out += encode_uvarint(metadata.churn_tier)
        lp_duration_out += encode_uvarint(1 if metadata.last_churn_update_timestamp is not None else 0)
        if metadata.last_churn_update_timestamp is not None:
            lp_duration_out += encode_uvarint(metadata.last_churn_update_timestamp)
    return bytes(lp_duration_out)


def _encode_support_nonces_section(*, nonce_table: NonceTable, support: BatchStateSupport) -> bytes:
    nonce_out = bytearray()
    nonce_entries: list[tuple[bytes, int]] = []
    nonce_seen: set[bytes] = set()
    for pubkey in support.nonce_keys:
        last_nonce = nonce_table.get_last(pubkey)
        if last_nonce == 0:
            continue
        pk_b = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
        if pk_b in nonce_seen:
            raise ValueError("duplicate decoded pubkey in support nonces")
        nonce_seen.add(pk_b)
        nonce_entries.append((pk_b, int(last_nonce)))
    nonce_entries.sort(key=lambda t: t[0])
    nonce_out += encode_uvarint(len(nonce_entries))
    for pk_b, last_nonce in nonce_entries:
        nonce_out += pk_b
        nonce_out += encode_uvarint(last_nonce)
    return bytes(nonce_out)


def compute_support_state_root(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    support: BatchStateSupport,
    nonces: NonceTable | None = None,
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
    nonce_table = NonceTable() if nonces is None else nonces
    if not isinstance(nonce_table, NonceTable):
        raise TypeError("nonces must be a NonceTable")

    payload = (
        domain_sep_bytes("state_support_root", version=SUPPORT_ROOT_VERSION)
        + b"BAL"
        + encode_bytes(_encode_support_balances_section(balances=balances, support=support))
        + b"POL"
        + encode_bytes(_encode_support_pools_section(pools=pools, support=support))
        + b"LPB"
        + encode_bytes(_encode_support_lp_balances_section(lp_balances=lp_balances, support=support))
        + b"LPA"
        + encode_bytes(_encode_support_lp_duration_section(lp_balances=lp_balances, support=support))
        + b"NNC"
        + encode_bytes(_encode_support_nonces_section(nonce_table=nonce_table, support=support))
    )
    return sha256_hex(payload)


def compute_support_state_root_for_batch(
    *,
    intents: Sequence[Intent],
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    nonces: NonceTable | None = None,
) -> str:
    support = derive_batch_state_support(intents, pools=pools)
    return compute_support_state_root(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonces,
    )
