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
from typing import TYPE_CHECKING, Mapping, Sequence, Tuple

from .balance_commitment import LogicalBalanceEntryV1, _encode_logical_balance_entries_v1
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
from .pools import PoolState, PoolStatus, compute_pool_id

if TYPE_CHECKING:
    from .owned_collections import OwnedMapV1
    from .state_snapshot_values import (
        CommittedBalanceTableV1,
        CommittedLPTableV1,
        CommittedNonceTableV1,
        CommittedPoolStateV1,
    )

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
    nonce_keys: set[str] = set()

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
        nonce_keys.add(sender)

        if intent.kind == IntentKind.CREATE_POOL:
            asset0 = intent.get_field("asset0")
            asset1 = intent.get_field("asset1")
            fee_bps = intent.get_field("fee_bps")
            if isinstance(asset0, str) and isinstance(asset1, str):
                balance_keys.add((sender, asset0))
                balance_keys.add((sender, asset1))
                if isinstance(fee_bps, int) and not isinstance(fee_bps, bool):
                    try:
                        pool_id = compute_pool_id(
                            asset0, asset1, fee_bps, curve_tag="CPMM", curve_params=""
                        )
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
                recipient = intent.get_field("recipient", sender)
                if isinstance(recipient, str) and recipient:
                    lp_keys.add((recipient, pool_id))
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
        nonce_keys=tuple(sorted(nonce_keys)),
    )


def _encode_legacy_support_balances_section_v1(
    balances: BalanceTable,
    support: BatchStateSupport,
) -> bytes:
    logical_entries = tuple(
        ((pubkey, asset), amount)
        for pubkey, asset in support.balance_keys
        if (amount := balances.get(pubkey, asset)) != 0
    )
    return _encode_logical_balance_entries_v1(
        logical_entries,
        duplicate_error="duplicate decoded (pubkey, asset) in support balances",
    )


def _encode_committed_support_balances_section_v1(
    balances: CommittedBalanceTableV1,
    support: BatchStateSupport,
) -> bytes:
    from .state_snapshot_values import CommittedBalanceTableV1
    from .state_snapshots import snapshot_balance_table

    if type(balances) is not CommittedBalanceTableV1:
        raise TypeError("balances must be an exact CommittedBalanceTableV1")
    admitted = snapshot_balance_table(balances)
    logical_entries: tuple[LogicalBalanceEntryV1, ...] = tuple(
        ((pubkey, asset), amount)
        for pubkey, asset in support.balance_keys
        if (amount := admitted.get(pubkey, asset)) != 0
    )
    return _encode_logical_balance_entries_v1(
        logical_entries,
        duplicate_error="duplicate decoded (pubkey, asset) in support balances",
    )


def _hash_support_sections_v1(
    *,
    balances_section: bytes,
    pools_section: bytes,
    lp_section: bytes,
    lp_duration_section: bytes,
    nonce_section: bytes,
) -> str:
    """Hash five already canonical support-root-v4 sections."""

    sections = (
        (b"BAL", balances_section),
        (b"POL", pools_section),
        (b"LPB", lp_section),
        (b"LPA", lp_duration_section),
        (b"NNC", nonce_section),
    )
    if any(type(section) is not bytes for _label, section in sections):
        raise TypeError("support-root sections must be exact bytes")
    payload = bytearray(domain_sep_bytes("state_support_root", version=SUPPORT_ROOT_VERSION))
    for label, section in sections:
        payload += label
        payload += encode_bytes(section)
    return sha256_hex(bytes(payload))


def _compute_support_state_root_from_balances_section_v1(
    *,
    balances_section: bytes,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    support: BatchStateSupport,
    nonces: NonceTable | None = None,
) -> str:
    """
    Join one canonical balance section with the remaining support sections.

    Entries with zero balance / missing pools are omitted, mirroring the full
    `compute_state_root()` sparsity behavior.
    """
    if type(balances_section) is not bytes:
        raise TypeError("balances_section must be exact bytes")
    if not isinstance(lp_balances, LPTable):
        raise TypeError("lp_balances must be an LPTable")
    if not isinstance(support, BatchStateSupport):
        raise TypeError("support must be a BatchStateSupport")
    nonce_table = NonceTable() if nonces is None else nonces
    if not isinstance(nonce_table, NonceTable):
        raise TypeError("nonces must be a NonceTable")

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
        lp_duration_out += encode_uvarint(
            1 if metadata.last_churn_update_timestamp is not None else 0
        )
        if metadata.last_churn_update_timestamp is not None:
            lp_duration_out += encode_uvarint(metadata.last_churn_update_timestamp)
    lp_duration_section = bytes(lp_duration_out)

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
    nonce_section = bytes(nonce_out)

    return _hash_support_sections_v1(
        balances_section=balances_section,
        pools_section=pools_section,
        lp_section=lp_section,
        lp_duration_section=lp_duration_section,
        nonce_section=nonce_section,
    )


def compute_support_state_root(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    support: BatchStateSupport,
    nonces: NonceTable | None = None,
) -> str:
    """Compute the existing support-root v4 from one legacy balance table."""

    if not isinstance(balances, BalanceTable):
        raise TypeError("balances must be a BalanceTable")
    if not isinstance(lp_balances, LPTable):
        raise TypeError("lp_balances must be an LPTable")
    if not isinstance(support, BatchStateSupport):
        raise TypeError("support must be a BatchStateSupport")
    nonce_table = NonceTable() if nonces is None else nonces
    if not isinstance(nonce_table, NonceTable):
        raise TypeError("nonces must be a NonceTable")
    return _compute_support_state_root_from_balances_section_v1(
        balances_section=_encode_legacy_support_balances_section_v1(balances, support),
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonce_table,
    )


def compute_support_state_root_with_committed_balances_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    support: BatchStateSupport,
    nonces: NonceTable | None = None,
) -> str:
    """Compute support-root v4 from an exact committed balance snapshot.

    The function is migration-scoped and unmounted. It changes only the source
    of the BAL section, then joins that section through the same support-root
    implementation used by the legacy reader.
    """

    from .state_snapshot_values import CommittedBalanceTableV1

    if type(balances) is not CommittedBalanceTableV1:
        raise TypeError("balances must be an exact CommittedBalanceTableV1")
    if not isinstance(lp_balances, LPTable):
        raise TypeError("lp_balances must be an LPTable")
    if not isinstance(support, BatchStateSupport):
        raise TypeError("support must be a BatchStateSupport")
    nonce_table = NonceTable() if nonces is None else nonces
    if not isinstance(nonce_table, NonceTable):
        raise TypeError("nonces must be a NonceTable")
    return _compute_support_state_root_from_balances_section_v1(
        balances_section=_encode_committed_support_balances_section_v1(balances, support),
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonce_table,
    )


def compute_support_state_root_with_committed_spot_state_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    support: BatchStateSupport,
    nonces: CommittedNonceTableV1,
) -> str:
    """Compute support-root v4 directly from exact committed spot state.

    This is a migration-scoped shadow reader. It re-admits every committed
    input through the closed state profile and preserves the existing support
    omission, ordering, field, and framing semantics byte for byte.
    """

    from .committed_spot_roots import (
        compute_support_state_root_with_committed_spot_state_v1 as _read_exact_support,
    )

    return _read_exact_support(
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonces,
    )


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
