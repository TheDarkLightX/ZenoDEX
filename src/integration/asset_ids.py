"""Deterministic asset identifiers without transport or network dependencies."""

from __future__ import annotations

import hashlib

from ..state.canonical import domain_sep_bytes


def derive_zusd_asset_id(*, chain_id: str = "tau-net-alpha", symbol: str = "zUSD") -> str:
    """Derive the existing zUSD asset identifier from exact textual inputs."""

    if not isinstance(chain_id, str) or not chain_id.strip():
        raise ValueError("chain_id must be a non-empty string")
    if not isinstance(symbol, str) or not symbol.strip():
        raise ValueError("symbol must be a non-empty string")
    payload = (
        domain_sep_bytes("dex_asset_id", version=1)
        + symbol.strip().encode("utf-8")
        + chain_id.strip().encode("utf-8")
    )
    return "0x" + hashlib.sha256(payload).hexdigest()
