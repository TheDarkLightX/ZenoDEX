"""
Deterministic quote receipts (UX + security + automation).

A *quote receipt* binds a proposed route quote to:
- the exact per-hop amounts,
- a snapshot fingerprint of the referenced pools,
- a deterministic receipt hash (canonical JSON + domain separation).

This supports:
- UI: show a quote that is replay/verifyable
- automation: deterministic agents can fail-closed if receipts don't verify
- security/audit: detect tampering or stale-state execution
"""

from __future__ import annotations

from dataclasses import replace
from typing import Any, Dict, Tuple

from ..core.amm_dispatch import swap_exact_in_for_pool, swap_exact_out_for_pool
from ..core.routing import RouteQuote
from ..state.canonical import canonical_json_bytes, domain_sep_bytes, sha256_hex
from ..state.pools import PoolState


def pool_state_fingerprint(pool: PoolState) -> str:
    """
    Deterministic pool fingerprint for receipts.

    Note: includes reserves so the receipt is only valid for a specific snapshot.
    """
    obj = {
        "pool_id": pool.pool_id,
        "asset0": pool.asset0,
        "asset1": pool.asset1,
        "reserve0": int(pool.reserve0),
        "reserve1": int(pool.reserve1),
        "fee_bps": int(pool.fee_bps),
        "curve_tag": str(pool.curve_tag),
        "curve_params": str(pool.curve_params),
        "lp_supply": int(pool.lp_supply),
        "status": str(pool.status.value),
        "created_at": int(pool.created_at),
    }
    return sha256_hex(domain_sep_bytes("zenodex.pool_state/v1") + canonical_json_bytes(obj))


def receipt_hash(receipt_body: Dict[str, Any]) -> str:
    return sha256_hex(domain_sep_bytes("zenodex.route_quote_receipt/v1") + canonical_json_bytes(receipt_body))


def make_route_quote_receipt(
    *,
    kind: str,
    quote: RouteQuote,
    pools_by_id: Dict[str, PoolState],
) -> Dict[str, Any]:
    """
    Create a deterministic receipt for a RouteQuote.

    `kind` must be "exact_in" or "exact_out". (RouteQuote itself is type-agnostic.)
    """
    k = str(kind).strip().lower()
    if k not in {"exact_in", "exact_out"}:
        raise ValueError("kind must be 'exact_in' or 'exact_out'")

    # Receipt legs/hops are stored as plain dicts (canonical JSON friendly).
    legs = []
    pool_fps: Dict[str, str] = {}
    for leg in quote.legs:
        hops = []
        for hop in leg.hops:
            pool = pools_by_id.get(hop.pool_id)
            if pool is None:
                raise ValueError(f"missing pool for hop.pool_id={hop.pool_id!r}")
            if hop.pool_id not in pool_fps:
                pool_fps[hop.pool_id] = pool_state_fingerprint(pool)
            hops.append(
                {
                    "pool_id": hop.pool_id,
                    "asset_in": hop.asset_in,
                    "asset_out": hop.asset_out,
                    "amount_in": int(hop.amount_in),
                    "amount_out": int(hop.amount_out),
                }
            )
        legs.append(
            {
                "amount_in": int(leg.amount_in),
                "amount_out": int(leg.amount_out),
                "hops": hops,
            }
        )

    body = {
        "schema": "zenodex/route_quote_receipt/v1",
        "kind": k,
        "asset_in": quote.asset_in,
        "asset_out": quote.asset_out,
        "amount_in": int(quote.amount_in),
        "amount_out": int(quote.amount_out),
        "legs": legs,
        # Deterministic map of pool_id -> snapshot fingerprint.
        "pools": {pid: pool_fps[pid] for pid in sorted(pool_fps.keys())},
    }
    return {
        "body": body,
        "receipt_hash": receipt_hash(body),
    }


def _pool_reserves_for_hop(pool: PoolState, *, asset_in: str, asset_out: str) -> Tuple[int, int] | None:
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _replay_and_apply_hop(
    *,
    pool: PoolState,
    kind: str,
    asset_in: str,
    asset_out: str,
    amount_in: int,
    amount_out: int,
) -> Tuple[bool, str, PoolState | None]:
    reserves = _pool_reserves_for_hop(pool, asset_in=asset_in, asset_out=asset_out)
    if reserves is None:
        return False, "bad_pool_direction", None
    rin, rout = reserves

    try:
        if kind == "exact_in":
            quoted_out, (next_rin, next_rout) = swap_exact_in_for_pool(
                pool,
                reserve_in=rin,
                reserve_out=rout,
                amount_in=int(amount_in),
            )
            if int(quoted_out) != int(amount_out):
                return False, "hop_quote_mismatch", None
        else:
            quoted_in, (next_rin, next_rout) = swap_exact_out_for_pool(
                pool,
                reserve_in=rin,
                reserve_out=rout,
                amount_out=int(amount_out),
            )
            if int(quoted_in) != int(amount_in):
                return False, "hop_quote_mismatch", None
    except Exception:
        return False, "hop_quote_error", None

    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return True, "ok", replace(pool, reserve0=int(next_rin), reserve1=int(next_rout))
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return True, "ok", replace(pool, reserve0=int(next_rout), reserve1=int(next_rin))
    return False, "bad_pool_direction", None


def verify_route_quote_receipt(
    receipt: object,
    *,
    pools_by_id: Dict[str, PoolState],
) -> Tuple[bool, str]:
    """
    Verify a quote receipt against pool snapshots and AMM semantics.

    Returns (ok, error_code).
    """
    if not isinstance(receipt, dict):
        return False, "bad_receipt_type"
    body = receipt.get("body")
    if not isinstance(body, dict):
        return False, "missing_body"
    if body.get("schema") != "zenodex/route_quote_receipt/v1":
        return False, "bad_schema"

    want_hash = receipt.get("receipt_hash")
    if not isinstance(want_hash, str) or not want_hash:
        return False, "missing_receipt_hash"
    got_hash = receipt_hash(body)
    if got_hash != want_hash:
        return False, "hash_mismatch"

    kind = str(body.get("kind", "")).strip().lower()
    if kind not in {"exact_in", "exact_out"}:
        return False, "bad_kind"

    body_asset_in = body.get("asset_in")
    body_asset_out = body.get("asset_out")
    if (
        not isinstance(body_asset_in, str)
        or not isinstance(body_asset_out, str)
        or not body_asset_in
        or not body_asset_out
        or body_asset_in == body_asset_out
    ):
        return False, "bad_body_assets"

    pools = body.get("pools")
    if not isinstance(pools, dict):
        return False, "bad_pools"

    # Verify pool snapshot fingerprints.
    for pid, fp in pools.items():
        if not isinstance(pid, str) or not isinstance(fp, str):
            return False, "bad_pool_fingerprint"
        pool = pools_by_id.get(pid)
        if pool is None:
            return False, "missing_pool"
        if pool_state_fingerprint(pool) != fp:
            return False, "pool_snapshot_mismatch"
    working_pools = {pid: replace(pools_by_id[pid]) for pid in pools}

    # Verify hop-by-hop quote semantics.
    legs = body.get("legs")
    if not isinstance(legs, list) or not legs:
        return False, "bad_legs"

    total_in = 0
    total_out = 0
    for leg in legs:
        if not isinstance(leg, dict):
            return False, "bad_leg"
        hops = leg.get("hops")
        if not isinstance(hops, list) or not hops:
            return False, "bad_hops"

        leg_in = int(leg.get("amount_in", 0))
        leg_out = int(leg.get("amount_out", 0))
        if leg_in <= 0 or leg_out <= 0:
            return False, "bad_leg_amounts"

        prev_out: int | None = None
        prev_asset_out: str | None = None
        for hop in hops:
            if not isinstance(hop, dict):
                return False, "bad_hop"
            pid = hop.get("pool_id")
            if not isinstance(pid, str) or not pid:
                return False, "bad_pool_id"
            if pid not in pools:
                return False, "missing_pool_fingerprint"
            pool = working_pools.get(pid)
            if pool is None:
                return False, "missing_working_pool"

            asset_in = hop.get("asset_in")
            asset_out = hop.get("asset_out")
            if not isinstance(asset_in, str) or not isinstance(asset_out, str):
                return False, "bad_assets"
            if prev_asset_out is None:
                if asset_in != body_asset_in:
                    return False, "leg_asset_in_mismatch"
            else:
                if asset_in != prev_asset_out:
                    return False, "hop_asset_chain_mismatch"

            amt_in = int(hop.get("amount_in", 0))
            amt_out = int(hop.get("amount_out", 0))
            if amt_in <= 0 or amt_out <= 0:
                return False, "bad_hop_amounts"

            if prev_out is not None and amt_in != prev_out:
                return False, "hop_chain_mismatch"

            ok, err, next_pool = _replay_and_apply_hop(
                pool=pool,
                kind=kind,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=int(amt_in),
                amount_out=int(amt_out),
            )
            if not ok or next_pool is None:
                return False, err
            working_pools[pid] = next_pool

            prev_out = int(amt_out)
            prev_asset_out = str(asset_out)

        if prev_asset_out != body_asset_out:
            return False, "leg_asset_out_mismatch"
        if int(hops[0].get("amount_in", 0)) != int(leg_in):
            return False, "leg_amount_in_mismatch"
        if int(hops[-1].get("amount_out", 0)) != int(leg_out):
            return False, "leg_amount_out_mismatch"

        total_in += int(leg_in)
        total_out += int(leg_out)

    if total_in != int(body.get("amount_in", 0)) or total_out != int(body.get("amount_out", 0)):
        return False, "totals_mismatch"

    return True, "ok"
