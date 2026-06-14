from __future__ import annotations

from typing import Mapping

from src.core.routing import RouteQuote
from src.state.pools import PoolState, PoolStatus


def parse_dex_api_pools(pools_raw: object) -> Mapping[str, PoolState]:
    """Parse the JSON pool table used by the defensive DEX API shell."""
    if not isinstance(pools_raw, list) or not pools_raw:
        raise ValueError("pools must be a non-empty list")
    pools_by_id: dict[str, PoolState] = {}
    for row in pools_raw:
        if not isinstance(row, dict):
            raise ValueError("pool must be an object")
        pid = row.get("pool_id")
        if not isinstance(pid, str) or not pid:
            raise ValueError("pool_id must be a non-empty string")
        if pid in pools_by_id:
            raise ValueError(f"duplicate pool_id: {pid}")
        st_raw = str(row.get("status", "ACTIVE")).strip().upper()
        try:
            status = PoolStatus[st_raw]
        except KeyError as exc:
            raise ValueError(f"bad pool status: {st_raw}") from exc
        pools_by_id[pid] = PoolState(
            pool_id=pid,
            asset0=str(row.get("asset0", "")),
            asset1=str(row.get("asset1", "")),
            reserve0=int(row.get("reserve0", 0)),
            reserve1=int(row.get("reserve1", 0)),
            fee_bps=int(row.get("fee_bps", 0)),
            lp_supply=int(row.get("lp_supply", 1)),
            status=status,
            created_at=int(row.get("created_at", 0)),
            curve_tag=str(row.get("curve_tag", "CPMM")),
            curve_params=row.get("curve_params", ""),
        )
    return pools_by_id


def route_quote_to_public_dict(quote: object) -> Mapping[str, object]:
    """Project a core RouteQuote into the stable JSON shape returned by the API."""
    if not isinstance(quote, RouteQuote):
        return {}
    legs_out: list[dict[str, object]] = []
    for leg in quote.legs:
        hops_out: list[dict[str, object]] = []
        for hop in leg.hops:
            hops_out.append(
                {
                    "pool_id": hop.pool_id,
                    "asset_in": hop.asset_in,
                    "asset_out": hop.asset_out,
                    "amount_in": int(hop.amount_in),
                    "amount_out": int(hop.amount_out),
                }
            )
        legs_out.append(
            {
                "amount_in": int(leg.amount_in),
                "amount_out": int(leg.amount_out),
                "hops": hops_out,
            }
        )
    return {
        "asset_in": quote.asset_in,
        "asset_out": quote.asset_out,
        "amount_in": int(quote.amount_in),
        "amount_out": int(quote.amount_out),
        "legs": legs_out,
    }


__all__ = [
    "parse_dex_api_pools",
    "route_quote_to_public_dict",
]
