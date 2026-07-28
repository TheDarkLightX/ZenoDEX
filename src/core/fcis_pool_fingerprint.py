"""Closure-clean pool fingerprinting over exact committed state."""

from __future__ import annotations

from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.state_snapshot_values import (
    POOL_STATUS_MEMBER_VALUES_V1,
    CommittedPoolStateV1,
)


def _require_exact_string(name: str, value: object) -> None:
    if type(value) is not str:
        raise TypeError(f"{name} must be an exact string")


def _require_exact_integer(name: str, value: object) -> None:
    if type(value) is not int:
        raise TypeError(f"{name} must be an exact integer")


def pool_state_fingerprint_fields_v1(
    *,
    pool_id: str,
    asset0: str,
    asset1: str,
    reserve0: int,
    reserve1: int,
    fee_bps: int,
    curve_tag: str,
    curve_params: str,
    lp_supply: int,
    status: str,
    created_at: int,
) -> str:
    """Hash one fully typed pool projection using the protocol-v1 preimage."""

    for name, value in (
        ("pool_id", pool_id),
        ("asset0", asset0),
        ("asset1", asset1),
        ("curve_tag", curve_tag),
        ("curve_params", curve_params),
        ("status", status),
    ):
        _require_exact_string(name, value)
    for name, integer_value in (
        ("reserve0", reserve0),
        ("reserve1", reserve1),
        ("fee_bps", fee_bps),
        ("lp_supply", lp_supply),
        ("created_at", created_at),
    ):
        _require_exact_integer(name, integer_value)

    preimage = {
        "pool_id": pool_id,
        "asset0": asset0,
        "asset1": asset1,
        "reserve0": reserve0,
        "reserve1": reserve1,
        "fee_bps": fee_bps,
        "curve_tag": curve_tag,
        "curve_params": curve_params,
        "lp_supply": lp_supply,
        "status": status,
        "created_at": created_at,
    }
    return sha256_hex(domain_sep_bytes("zenodex.pool_state/v1") + canonical_json_bytes(preimage))


def pool_state_fingerprint_committed_v1(pool: CommittedPoolStateV1) -> str:
    """Fingerprint one recursively revalidated exact committed pool."""

    if type(pool) is not CommittedPoolStateV1:
        raise TypeError("pool must be an exact committed pool")
    pool.__post_init__()
    return pool_state_fingerprint_fields_v1(
        pool_id=pool.pool_id,
        asset0=pool.asset0,
        asset1=pool.asset1,
        reserve0=pool.reserve0,
        reserve1=pool.reserve1,
        fee_bps=pool.fee_bps,
        curve_tag=pool.curve_tag,
        curve_params=pool.curve_params,
        lp_supply=pool.lp_supply,
        status=POOL_STATUS_MEMBER_VALUES_V1[pool.status.member_ordinal],
        created_at=pool.created_at,
    )


__all__ = (
    "pool_state_fingerprint_committed_v1",
    "pool_state_fingerprint_fields_v1",
)
