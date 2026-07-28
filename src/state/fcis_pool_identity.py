"""Closure-clean pool identity primitives shared by exact and legacy state.

The protocol pool identifier binds the canonical asset pair, fee, curve tag,
and canonical curve parameters.  This module intentionally has no dependency
on mutable pool state, JSON admission, or legacy snapshot machinery.
"""

from __future__ import annotations

import hashlib

from .canonical import canonical_hex_fixed_allow_0x

_ASSET_ID_BYTES_V1 = 32


def _require_exact_string_v1(value: object, *, name: str) -> str:
    if type(value) is not str:
        raise TypeError(f"{name} must be a string")
    return value


def _canonical_asset_id_if_hex_v1(asset: object, *, name: str) -> str:
    text = _require_exact_string_v1(asset, name=name)
    if text.strip().lower().startswith("0x"):
        return canonical_hex_fixed_allow_0x(
            text,
            nbytes=_ASSET_ID_BYTES_V1,
            name=name,
        )
    return text


def _asset_order_bytes_v1(asset: str) -> bytes | None:
    if not asset.startswith("0x") or len(asset) != 66:
        return None
    try:
        return bytes.fromhex(asset[2:])
    except ValueError:
        return None


def normalize_pool_asset_pair(asset0: object, asset1: object) -> tuple[str, str]:
    """Return one canonical strictly ordered asset pair.

    Canonical 32-byte hexadecimal identifiers are ordered by decoded bytes.
    Symbolic identifiers remain available for legacy non-authoritative tests
    and use their historical string ordering.
    """

    asset0_normalized = _canonical_asset_id_if_hex_v1(asset0, name="asset0")
    asset1_normalized = _canonical_asset_id_if_hex_v1(asset1, name="asset1")
    asset0_bytes = _asset_order_bytes_v1(asset0_normalized)
    asset1_bytes = _asset_order_bytes_v1(asset1_normalized)
    if asset0_bytes is not None and asset1_bytes is not None:
        if asset0_bytes >= asset1_bytes:
            raise ValueError(
                f"Assets must be in canonical order: {asset0_normalized} < {asset1_normalized}"
            )
        return asset0_normalized, asset1_normalized
    if asset0_normalized >= asset1_normalized:
        raise ValueError(
            f"Assets must be in canonical order: {asset0_normalized} < {asset1_normalized}"
        )
    return asset0_normalized, asset1_normalized


def compute_pool_id(
    asset0: object,
    asset1: object,
    fee_bps: object,
    *,
    curve_tag: object = "CPMM",
    curve_params: object = "",
) -> str:
    """Compute the version-one parameter-bound pool identifier."""

    asset0_normalized, asset1_normalized = normalize_pool_asset_pair(asset0, asset1)
    if type(fee_bps) is not int:
        raise TypeError("fee_bps must be an int")
    if not 0 <= fee_bps <= 10_000:
        raise ValueError(f"fee_bps must be in [0, 10000]: {fee_bps}")
    if type(curve_tag) is not str or not curve_tag:
        raise ValueError("curve_tag must be a non-empty string")
    if type(curve_params) is not str:
        raise ValueError("curve_params must be a string")

    pool_id_preimage = (
        b"TauSwapPool"
        + asset0_normalized.encode("utf-8")
        + asset1_normalized.encode("utf-8")
        + str(fee_bps).encode("utf-8")
        + curve_tag.encode("utf-8")
        + curve_params.encode("utf-8")
    )
    return "0x" + hashlib.sha256(pool_id_preimage).hexdigest()


def validate_pool_id_format(pool_id: object, *, allow_symbolic: object) -> None:
    """Require a canonical 32-byte pool ID or an allowed symbolic identifier."""

    if type(allow_symbolic) is not bool:
        raise TypeError("allow_symbolic must be a bool")
    if type(pool_id) is not str:
        raise TypeError("pool_id must be a string")
    if not pool_id or pool_id != pool_id.strip():
        raise ValueError("pool_id must be non-empty and must not contain surrounding whitespace")

    try:
        canonical_pool_id = canonical_hex_fixed_allow_0x(
            pool_id,
            nbytes=_ASSET_ID_BYTES_V1,
            name="pool_id",
        )
    except ValueError as exc:
        if pool_id.lower().startswith("0x"):
            raise ValueError(
                "pool_id must be a canonical lowercase 0x-prefixed 32-byte hex string"
            ) from exc
        if allow_symbolic:
            return
        raise ValueError(
            "pool_id must be a canonical lowercase 0x-prefixed 32-byte hex string"
        ) from exc

    if pool_id != canonical_pool_id:
        raise ValueError("pool_id must be a canonical lowercase 0x-prefixed 32-byte hex string")
