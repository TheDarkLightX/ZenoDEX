"""
Deterministic state root hashing (v5).

This is intended for:
- debugging / audit (stable hashes for the same logical state),
- parity checking between kernels (Python vs reference models),
- the spot-DEX ledger state commitment (header pre/post_state_root via
  ``dex_state_root_v0``) and the recompute_batch v1/v2 proof schemes.

Scope (spot-DEX lane): this root commits the spot-DEX state mutated by the
DEX-lane apply path: balances, pools, LP balances + duration-risk metadata,
nonces, and (since v5) the ``fee_accumulator`` dust carry. ``apply_ops``
advances the dust accumulator on fee-bearing settlement and the snapshot
persists it, so it must be bound by the committed root. Other ledger lanes
(zUSD, perps, oracle, and vault) maintain their own per-lane roots; they are
outside this spot-DEX root because this apply path does not mutate them.

v5 added the FEE section. v4 omitted fee_accumulator.
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
from .pools import PoolState, PoolStatus, validate_pool_id_format, validate_pool_identity

STATE_ROOT_VERSION = 5

_POOL_STATUS_CODE: dict[PoolStatus, int] = {
    PoolStatus.ACTIVE: 1,
    PoolStatus.FROZEN: 2,
    PoolStatus.DISABLED: 3,
}

_POOL_STATUS_LABEL: dict[PoolStatus, str] = {
    PoolStatus.ACTIVE: "active",
    PoolStatus.FROZEN: "frozen",
    PoolStatus.DISABLED: "disabled",
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
        validate_pool_id_format(pool_id, allow_symbolic=False)
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
        validate_pool_id_format(pool_id, allow_symbolic=False)
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
        if not isinstance(pool, PoolState):
            raise TypeError("pools values must be PoolState instances")
        if pool.pool_id != pool_id:
            raise ValueError(f"pool_id mismatch: key={pool_id} pool.pool_id={pool.pool_id}")
        validate_pool_identity(pool, allow_symbolic=False)
        pool_b = hex_to_bytes_fixed(pool_id, nbytes=32, name="pool_id")
        if pool_b in seen:
            raise ValueError("duplicate decoded pool_id in pools")
        seen.add(pool_b)
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
        if asset0_b >= asset1_b:
            raise ValueError(f"non-canonical pool assets: {pool.asset0} < {pool.asset1}")
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


def _fee_accumulator_dust(fee_accumulator: object | None) -> int:
    """Extract and validate the fee-accumulator dust carry.

    Accepts ``None`` (treated as an empty accumulator, dust == 0, identical to
    ``FeeAccumulatorState()``) or any object exposing a non-negative int
    ``dust`` attribute. The class is intentionally not imported here so that
    ``src/state`` stays a leaf layer with no dependency on ``src/core``.
    """
    if fee_accumulator is None:
        return 0
    dust = getattr(fee_accumulator, "dust", None)
    if not isinstance(dust, int) or isinstance(dust, bool) or dust < 0:
        raise ValueError(f"invalid fee_accumulator dust: {dust!r}")
    return int(dust)


def _encode_fee_section(fee_accumulator: object | None) -> bytes:
    # FEE section (state-root v5): currently the single dust carry. If
    # FeeAccumulatorState gains fields, append them here and bump the state-root
    # version so the committed root keeps binding all consensus-relevant fee
    # state.
    return encode_uvarint(_fee_accumulator_dust(fee_accumulator))


def _fee_accumulator_json(fee_accumulator: object | None) -> dict[str, int]:
    return {"dust": _fee_accumulator_dust(fee_accumulator)}


def _state_root_json(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    nonces: NonceTable,
    fee_accumulator: object | None = None,
) -> dict[str, object]:
    """Build the normalized JSON state consumed by the Rust state-root CLI."""

    return {
        "balances": [
            {"pubkey": pubkey, "asset": asset, "amount": amount}
            for (pubkey, asset), amount in balances.get_all_balances().items()
        ],
        "pools": [
            {
                "pool_id": pool.pool_id,
                "asset0": pool.asset0,
                "asset1": pool.asset1,
                "reserve0": pool.reserve0,
                "reserve1": pool.reserve1,
                "fee_bps": pool.fee_bps,
                "lp_supply": pool.lp_supply,
                "status": _POOL_STATUS_LABEL[pool.status],
                "created_at": pool.created_at,
                "curve_tag": pool.curve_tag,
                "curve_params": pool.curve_params,
            }
            for pool in pools.values()
        ],
        "lp_balances": [
            {"pubkey": pubkey, "pool_id": pool_id, "amount": amount}
            for (pubkey, pool_id), amount in lp_balances.get_all_balances().items()
        ],
        "lp_duration_risk": [
            {
                "pubkey": pubkey,
                "pool_id": pool_id,
                "last_mint_timestamp": metadata.last_mint_timestamp,
                "last_remove_timestamp": metadata.last_remove_timestamp,
                "churn_tier": metadata.churn_tier,
                "last_churn_update_timestamp": metadata.last_churn_update_timestamp,
            }
            for (pubkey, pool_id), metadata in lp_balances.get_all_duration_risk_metadata().items()
        ],
        "nonces": [
            {"pubkey": pubkey, "last_nonce": last_nonce}
            for pubkey, last_nonce in nonces.get_all().items()
        ],
        "fee_accumulator": _fee_accumulator_json(fee_accumulator),
    }


def _compute_state_root_python(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    nonces: NonceTable | None = None,
    fee_accumulator: object | None = None,
) -> str:
    nonce_table = NonceTable() if nonces is None else nonces
    return sha256_hex(
        state_root_preimage(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonce_table,
            fee_accumulator=fee_accumulator,
        )
    )


def compute_state_root(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    nonces: NonceTable | None = None,
    fee_accumulator: object | None = None,
) -> str:
    """
    Compute a deterministic state root hash for the spot-DEX state.

    Binds balances, pools, LP balances + duration-risk metadata, nonces, and
    (since v5) the ``fee_accumulator`` dust carry. ``fee_accumulator=None`` is
    equivalent to an empty accumulator (dust == 0). Returns a 0x-prefixed
    sha256 digest.
    """
    if not isinstance(balances, BalanceTable):
        raise TypeError("balances must be a BalanceTable")
    if not isinstance(lp_balances, LPTable):
        raise TypeError("lp_balances must be an LPTable")
    nonce_table = NonceTable() if nonces is None else nonces
    if not isinstance(nonce_table, NonceTable):
        raise TypeError("nonces must be a NonceTable")

    # Validate the authority-neutral state before selecting Python or Rust. A
    # Rust-authority mode must not bypass pool identity checks in the wrapper.
    _sorted_pool_entries(pools)
    _sorted_lp_entries(lp_balances)
    _sorted_lp_duration_risk_entries(lp_balances)

    from src.runtime.authority import AuthorityMode, active_mode, decide

    mode = active_mode("state_root")
    if mode is AuthorityMode.PYTHON_AUTHORITY:
        return _compute_state_root_python(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonce_table,
            fee_accumulator=fee_accumulator,
        )

    def _python_root() -> str:
        return _compute_state_root_python(
            balances=balances,
            pools=pools,
            lp_balances=lp_balances,
            nonces=nonce_table,
            fee_accumulator=fee_accumulator,
        )

    def _rust_root() -> str:
        from src.runtime.rust_invoker import state_root_hash

        return state_root_hash(
            _state_root_json(
                balances=balances,
                pools=pools,
                lp_balances=lp_balances,
                nonces=nonce_table,
                fee_accumulator=fee_accumulator,
            )
        )

    return decide(
        "state_root",
        mode,
        python_fn=_python_root,
        rust_fn=_rust_root,
        compare=lambda python_root, rust_root: python_root == rust_root,
    ).result


# Ordered section framing for the state-root preimage. Each entry is a 3-byte
# ASCII label followed by a length-prefixed (`encode_bytes`) section body. The
# length prefix makes framing self-delimiting, so the concatenation is injective
# in the section tuple. See tools/runtime/state_root_injectivity.py and
# tests/runtime/test_state_root_injectivity_proof.py for the checked decoder
# round-trip proof.
STATE_ROOT_SECTION_LABELS: tuple[bytes, ...] = (b"BAL", b"POL", b"LPB", b"LPA", b"NNC", b"FEE")


def state_root_preimage(
    *,
    balances: BalanceTable,
    pools: Mapping[str, PoolState],
    lp_balances: LPTable,
    nonces: NonceTable | None = None,
    fee_accumulator: object | None = None,
) -> bytes:
    """Build the canonical state-root preimage bytes, the input to sha256."""
    if not isinstance(balances, BalanceTable):
        raise TypeError("balances must be a BalanceTable")
    if not isinstance(lp_balances, LPTable):
        raise TypeError("lp_balances must be an LPTable")
    nonce_table = NonceTable() if nonces is None else nonces
    if not isinstance(nonce_table, NonceTable):
        raise TypeError("nonces must be a NonceTable")

    sections = {
        b"BAL": _encode_balances_section(balances),
        b"POL": _encode_pools_section(pools),
        b"LPB": _encode_lp_section(lp_balances),
        b"LPA": _encode_lp_duration_risk_section(lp_balances),
        b"NNC": _encode_nonce_section(nonce_table),
        b"FEE": _encode_fee_section(fee_accumulator),
    }
    out = bytearray(domain_sep_bytes("state_root", version=STATE_ROOT_VERSION))
    for label in STATE_ROOT_SECTION_LABELS:
        out += label
        out += encode_bytes(sections[label])
    return bytes(out)
