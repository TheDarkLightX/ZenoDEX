"""Shadow root readers for the exact committed spot-state graph.

These functions preserve the existing state-root v5 and mounted support-root
v4 byte languages while consuming only exact committed FCIS values.  The
route-complete support-root v5 encoder is separate and unmounted.  Every exact
reader remains unmounted until its verifier/runtime parity gate is complete.
"""

from __future__ import annotations

from .canonical import encode_bytes, encode_uvarint, hex_to_bytes_fixed
from .owned_collections import OwnedMapV1
from .pools import validate_pool_id_format
from .state_root import (
    _encode_committed_balances_section_v1,
    _state_root_preimage_from_sections_v1,
)
from .state_snapshot_values import (
    CommittedBalanceTableV1,
    CommittedFeeAccumulatorStateV1,
    CommittedLPTableV1,
    CommittedNonceTableV1,
    CommittedPoolStateV1,
)
from .state_snapshots import (
    snapshot_fee_accumulator,
    snapshot_lp_table,
    snapshot_nonce_table,
    snapshot_pool_map,
)
from .support_root_primitives import (
    INCOMPLETE_SUPPORT_ROOT_PROTOTYPE_VERSION_V1,
    SUPPORT_ROOT_VERSION,
    BatchStateSupport,
)
from .support_root_primitives import (
    encode_committed_support_balances_section_v1 as _encode_committed_support_balances_section_v1,
)
from .support_root_primitives import (
    hash_support_sections_for_version_v1 as _hash_support_sections_for_version_v1,
)


def _admit_exact_pools_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> OwnedMapV1[str, CommittedPoolStateV1]:
    if type(pools) is not OwnedMapV1:
        raise TypeError("pools must be an exact OwnedMapV1")
    return snapshot_pool_map(pools)


def _admit_exact_lp_v1(lp_balances: CommittedLPTableV1) -> CommittedLPTableV1:
    if type(lp_balances) is not CommittedLPTableV1:
        raise TypeError("lp_balances must be an exact CommittedLPTableV1")
    return snapshot_lp_table(lp_balances)


def _admit_exact_nonces_v1(nonces: CommittedNonceTableV1) -> CommittedNonceTableV1:
    if type(nonces) is not CommittedNonceTableV1:
        raise TypeError("nonces must be an exact CommittedNonceTableV1")
    return snapshot_nonce_table(nonces)


def _admit_exact_fees_v1(
    fees: CommittedFeeAccumulatorStateV1,
) -> CommittedFeeAccumulatorStateV1:
    if type(fees) is not CommittedFeeAccumulatorStateV1:
        raise TypeError("fee_accumulator must be an exact CommittedFeeAccumulatorStateV1")
    return snapshot_fee_accumulator(fees)


def _require_exact_support_v1(support: BatchStateSupport) -> BatchStateSupport:
    if type(support) is not BatchStateSupport:
        raise TypeError("support must be an exact BatchStateSupport")
    for field_name in ("balance_keys", "pool_ids", "lp_keys", "nonce_keys"):
        values = object.__getattribute__(support, field_name)
        if type(values) is not tuple:
            raise TypeError(f"support {field_name} must be an exact tuple")
        if field_name in {"balance_keys", "lp_keys"}:
            for value in values:
                if (
                    type(value) is not tuple
                    or len(value) != 2
                    or type(value[0]) is not str
                    or type(value[1]) is not str
                ):
                    raise TypeError(f"support {field_name} must contain exact string pairs")
        elif any(type(value) is not str for value in values):
            raise TypeError(f"support {field_name} must contain exact strings")
        if values != tuple(sorted(values)):
            raise ValueError(f"support {field_name} must use canonical protocol order")
        if any(values[index - 1] == values[index] for index in range(1, len(values))):
            raise ValueError(f"support {field_name} must be duplicate-free")
    return support


def _encode_pool_body_v1(pool: CommittedPoolStateV1) -> bytes:
    asset0 = hex_to_bytes_fixed(pool.asset0, nbytes=32, name="asset0")
    asset1 = hex_to_bytes_fixed(pool.asset1, nbytes=32, name="asset1")
    if asset0 >= asset1:
        raise ValueError(f"non-canonical pool assets: {pool.asset0} < {pool.asset1}")
    out = bytearray(asset0)
    out += asset1
    out += encode_uvarint(pool.reserve0)
    out += encode_uvarint(pool.reserve1)
    out += encode_uvarint(pool.fee_bps)
    out += encode_uvarint(pool.lp_supply)
    out += encode_uvarint(pool.status.member_ordinal + 1)
    out += encode_uvarint(pool.created_at)
    out += encode_bytes(pool.curve_tag.encode("utf-8"))
    out += encode_bytes(pool.curve_params.encode("utf-8"))
    return bytes(out)


def _encode_pool_entries_v1(
    entries: list[tuple[bytes, CommittedPoolStateV1]],
) -> bytes:
    entries.sort(key=lambda entry: entry[0])
    out = bytearray(encode_uvarint(len(entries)))
    for pool_id, pool in entries:
        out += pool_id
        out += _encode_pool_body_v1(pool)
    return bytes(out)


def _encode_full_pools_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
) -> bytes:
    entries: list[tuple[bytes, CommittedPoolStateV1]] = []
    seen: set[bytes] = set()
    for pool_id, pool in pools.entries:
        decoded = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        if decoded in seen:
            raise ValueError("duplicate decoded pool_id in committed pools")
        seen.add(decoded)
        entries.append((decoded, pool))
    return _encode_pool_entries_v1(entries)


def _encode_support_pools_v1(
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    support: BatchStateSupport,
) -> bytes:
    entries: list[tuple[bytes, CommittedPoolStateV1]] = []
    seen: set[bytes] = set()
    for pool_id in support.pool_ids:
        pool = pools.get(pool_id)
        if pool is None:
            continue
        decoded = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        if decoded in seen:
            raise ValueError("duplicate decoded pool_id in committed support pools")
        seen.add(decoded)
        entries.append((decoded, pool))
    return _encode_pool_entries_v1(entries)


def _encode_lp_balance_entries_v1(entries: list[tuple[bytes, bytes, int]]) -> bytes:
    entries.sort(key=lambda entry: (entry[0], entry[1]))
    out = bytearray(encode_uvarint(len(entries)))
    for pubkey, pool_id, amount in entries:
        out += pubkey
        out += pool_id
        out += encode_uvarint(amount)
    return bytes(out)


def _decode_lp_key_v1(pubkey: str, pool_id: str) -> tuple[bytes, bytes]:
    decoded_pubkey = hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey")
    validate_pool_id_format(pool_id, allow_symbolic=False)
    decoded_pool = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
    return decoded_pubkey, decoded_pool


def _encode_full_lp_balances_v1(lp_balances: CommittedLPTableV1) -> bytes:
    entries: list[tuple[bytes, bytes, int]] = []
    seen: set[tuple[bytes, bytes]] = set()
    for (pubkey, pool_id), amount in lp_balances.balance_entries:
        key = _decode_lp_key_v1(pubkey, pool_id)
        if key in seen:
            raise ValueError("duplicate decoded LP key in committed balances")
        seen.add(key)
        entries.append((*key, amount))
    return _encode_lp_balance_entries_v1(entries)


def _encode_support_lp_balances_v1(
    lp_balances: CommittedLPTableV1,
    support: BatchStateSupport,
) -> bytes:
    entries: list[tuple[bytes, bytes, int]] = []
    seen: set[tuple[bytes, bytes]] = set()
    for pubkey, pool_id in support.lp_keys:
        amount = lp_balances.get(pubkey, pool_id)
        if amount == 0:
            continue
        key = _decode_lp_key_v1(pubkey, pool_id)
        if key in seen:
            raise ValueError("duplicate decoded LP key in committed support state")
        seen.add(key)
        entries.append((*key, amount))
    return _encode_lp_balance_entries_v1(entries)


def _encode_lp_risk_entries_v1(
    entries: list[tuple[bytes, bytes, int | None, int | None, int, int | None]],
) -> bytes:
    entries.sort(key=lambda entry: (entry[0], entry[1]))
    out = bytearray(encode_uvarint(len(entries)))
    for pubkey, pool_id, last_mint, last_remove, churn_tier, last_churn_update in entries:
        out += pubkey
        out += pool_id
        for timestamp in (last_mint, last_remove):
            out += encode_uvarint(1 if timestamp is not None else 0)
            if timestamp is not None:
                out += encode_uvarint(timestamp)
        out += encode_uvarint(churn_tier)
        out += encode_uvarint(1 if last_churn_update is not None else 0)
        if last_churn_update is not None:
            out += encode_uvarint(last_churn_update)
    return bytes(out)


def _lp_risk_entry_v1(
    lp_balances: CommittedLPTableV1,
    pubkey: str,
    pool_id: str,
) -> tuple[bytes, bytes, int | None, int | None, int, int | None]:
    decoded_pubkey, decoded_pool = _decode_lp_key_v1(pubkey, pool_id)
    return (
        decoded_pubkey,
        decoded_pool,
        lp_balances.get_last_mint_timestamp(pubkey, pool_id),
        lp_balances.get_last_remove_timestamp(pubkey, pool_id),
        lp_balances.get_churn_tier(pubkey, pool_id),
        lp_balances.get_last_churn_update_timestamp(pubkey, pool_id),
    )


def _encode_full_lp_risk_v1(lp_balances: CommittedLPTableV1) -> bytes:
    logical_keys = [
        key
        for entries in (
            lp_balances.last_mint_entries,
            lp_balances.last_remove_entries,
            lp_balances.churn_tier_entries,
            lp_balances.last_churn_update_entries,
        )
        for key, _value in entries
    ]
    logical_keys.sort()
    unique_keys = [
        key
        for index, key in enumerate(logical_keys)
        if index == 0 or key != logical_keys[index - 1]
    ]
    entries = [_lp_risk_entry_v1(lp_balances, *key) for key in unique_keys]
    if len({(entry[0], entry[1]) for entry in entries}) != len(entries):
        raise ValueError("duplicate decoded LP risk key in committed state")
    return _encode_lp_risk_entries_v1(entries)


def _encode_support_lp_risk_v1(
    lp_balances: CommittedLPTableV1,
    support: BatchStateSupport,
) -> bytes:
    entries = [_lp_risk_entry_v1(lp_balances, *key) for key in support.lp_keys]
    entries = [entry for entry in entries if entry[2:] != (None, None, 0, None)]
    if len({(entry[0], entry[1]) for entry in entries}) != len(entries):
        raise ValueError("duplicate decoded LP risk key in committed support state")
    return _encode_lp_risk_entries_v1(entries)


def _encode_nonce_entries_v1(entries: list[tuple[bytes, int]]) -> bytes:
    entries.sort(key=lambda entry: entry[0])
    out = bytearray(encode_uvarint(len(entries)))
    for pubkey, nonce in entries:
        out += pubkey
        out += encode_uvarint(nonce)
    return bytes(out)


def _encode_full_nonces_v1(nonces: CommittedNonceTableV1) -> bytes:
    entries = [
        (hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey"), nonce)
        for pubkey, nonce in nonces.entries
    ]
    if len({entry[0] for entry in entries}) != len(entries):
        raise ValueError("duplicate decoded pubkey in committed nonces")
    return _encode_nonce_entries_v1(entries)


def _encode_support_nonces_v1(
    nonces: CommittedNonceTableV1,
    support: BatchStateSupport,
) -> bytes:
    entries = [
        (hex_to_bytes_fixed(pubkey, nbytes=48, name="pubkey"), nonces.get_last(pubkey))
        for pubkey in support.nonce_keys
        if nonces.get_last(pubkey) != 0
    ]
    if len({entry[0] for entry in entries}) != len(entries):
        raise ValueError("duplicate decoded pubkey in committed support nonces")
    return _encode_nonce_entries_v1(entries)


def state_root_preimage_with_committed_spot_state_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    nonces: CommittedNonceTableV1,
    fee_accumulator: CommittedFeeAccumulatorStateV1,
) -> bytes:
    """Build root-v5 bytes after closed re-admission of all spot fields."""

    admitted_pools = _admit_exact_pools_v1(pools)
    admitted_lp = _admit_exact_lp_v1(lp_balances)
    admitted_nonces = _admit_exact_nonces_v1(nonces)
    admitted_fees = _admit_exact_fees_v1(fee_accumulator)
    return _state_root_preimage_from_sections_v1(
        balances_section=_encode_committed_balances_section_v1(balances),
        pools_section=_encode_full_pools_v1(admitted_pools),
        lp_balances_section=_encode_full_lp_balances_v1(admitted_lp),
        lp_duration_risk_section=_encode_full_lp_risk_v1(admitted_lp),
        nonces_section=_encode_full_nonces_v1(admitted_nonces),
        fee_section=encode_uvarint(admitted_fees.dust),
    )


def compute_support_state_root_with_committed_spot_state_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    support: BatchStateSupport,
    nonces: CommittedNonceTableV1,
) -> str:
    """Build support-root v4 after closed re-admission of spot fields."""

    return _compute_support_state_root_for_version_v1(
        support_root_version=SUPPORT_ROOT_VERSION,
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonces,
    )


def compute_support_state_root_v5_with_committed_spot_state_v1(
    *,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    support: BatchStateSupport,
    nonces: CommittedNonceTableV1,
) -> str:
    """Build the frozen incomplete pre-M5 differential prototype."""

    return _compute_support_state_root_for_version_v1(
        support_root_version=INCOMPLETE_SUPPORT_ROOT_PROTOTYPE_VERSION_V1,
        balances=balances,
        pools=pools,
        lp_balances=lp_balances,
        support=support,
        nonces=nonces,
    )


def _compute_support_state_root_for_version_v1(
    *,
    support_root_version: int,
    balances: CommittedBalanceTableV1,
    pools: OwnedMapV1[str, CommittedPoolStateV1],
    lp_balances: CommittedLPTableV1,
    support: BatchStateSupport,
    nonces: CommittedNonceTableV1,
) -> str:
    """Encode one exact support set under an explicit root profile."""

    support = _require_exact_support_v1(support)
    admitted_pools = _admit_exact_pools_v1(pools)
    admitted_lp = _admit_exact_lp_v1(lp_balances)
    admitted_nonces = _admit_exact_nonces_v1(nonces)
    return _hash_support_sections_for_version_v1(
        support_root_version=support_root_version,
        balances_section=_encode_committed_support_balances_section_v1(balances, support),
        pools_section=_encode_support_pools_v1(admitted_pools, support),
        lp_section=_encode_support_lp_balances_v1(admitted_lp, support),
        lp_duration_section=_encode_support_lp_risk_v1(admitted_lp, support),
        nonce_section=_encode_support_nonces_v1(admitted_nonces, support),
    )
