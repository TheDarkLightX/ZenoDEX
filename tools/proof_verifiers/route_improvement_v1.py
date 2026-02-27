#!/usr/bin/env python3
"""
Deterministic verifier: route improvement witness (v1).

Verifies `zenodex/route_improvement_witness/v1` by:
1) Recomputing the baseline = best direct CPMM pool output.
2) Replaying the proposed route (1-hop or 2-hop) exactly using integer swap semantics.
3) Checking `proposal_out > baseline_out` iff `improves=true`.

This is intended as a cheap "useful work" verifier: miners can spend GPU time
searching for better routes, but the DEX only needs deterministic replay.
"""

from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

# Allow `python3 tools/proof_verifiers/...` from repo root without needing `-m`.
_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.core.amm_dispatch import swap_exact_in_for_pool  # noqa: E402
from src.state.balances import AssetId  # noqa: E402
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus  # noqa: E402


def _fail(msg: str) -> Tuple[bool, str]:
    return False, str(msg)


def _require_mapping(value: Any, *, name: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise ValueError(f"{name} must be an object")
    return value


def _require_list(value: Any, *, name: str) -> List[Any]:
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a list")
    return list(value)


def _require_str(value: Any, *, name: str) -> str:
    if not isinstance(value, str) or not value:
        raise ValueError(f"{name} must be a non-empty string")
    return str(value)


def _require_int(value: Any, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _pool_from_json(obj: Mapping[str, Any]) -> PoolState:
    # Keep consistent with tools/gpu_jobs/route_2hop_search_cpmm.py parsing.
    pool_id = _require_str(obj.get("pool_id"), name="pool.pool_id")
    asset0 = _require_str(obj.get("asset0"), name="pool.asset0")
    asset1 = _require_str(obj.get("asset1"), name="pool.asset1")
    reserve0 = _require_int(obj.get("reserve0"), name="pool.reserve0")
    reserve1 = _require_int(obj.get("reserve1"), name="pool.reserve1")
    fee_bps = _require_int(obj.get("fee_bps"), name="pool.fee_bps")
    lp_supply = _require_int(obj.get("lp_supply", 0), name="pool.lp_supply")
    status_s = _require_str(obj.get("status", "ACTIVE"), name="pool.status")
    created_at = _require_int(obj.get("created_at", 0), name="pool.created_at")
    curve_tag = _require_str(obj.get("curve_tag", CURVE_TAG_CPMM), name="pool.curve_tag")
    curve_params = obj.get("curve_params", "")
    if curve_params is None:
        curve_params = ""
    if not isinstance(curve_params, (str, dict)):
        raise ValueError("pool.curve_params must be a string or object")
    try:
        status = PoolStatus[str(status_s).strip().upper()]
    except KeyError as exc:
        raise ValueError(f"unknown pool status: {status_s!r}") from exc
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=int(fee_bps),
        lp_supply=int(lp_supply),
        status=status,
        created_at=int(created_at),
        curve_tag=str(curve_tag),
        curve_params=curve_params if isinstance(curve_params, str) else curve_params,
    )


def _pools_by_id(pools: Sequence[PoolState]) -> Dict[str, PoolState]:
    out: Dict[str, PoolState] = {}
    for p in pools:
        if p.pool_id in out:
            raise ValueError(f"duplicate pool_id: {p.pool_id}")
        out[p.pool_id] = p
    return out


def _pool_dir_reserves(
    p: PoolState, *, asset_in: AssetId, asset_out: AssetId, reserves: Dict[str, Tuple[int, int]]
) -> Tuple[int, int, int, int]:
    if asset_in == p.asset0 and asset_out == p.asset1:
        r0, r1 = reserves[p.pool_id]
        return int(r0), int(r1), 0, 1
    if asset_in == p.asset1 and asset_out == p.asset0:
        r0, r1 = reserves[p.pool_id]
        return int(r1), int(r0), 1, 0
    raise ValueError(f"pool {p.pool_id} does not connect {asset_in}->{asset_out}")


def _quote_exact_in_route(
    *,
    pools: Dict[str, PoolState],
    route: List[Mapping[str, Any]],
    amount_in: int,
) -> Tuple[int, List[Dict[str, int]]]:
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")

    reserves: Dict[str, Tuple[int, int]] = {pid: (int(p.reserve0), int(p.reserve1)) for pid, p in pools.items()}
    hop_io: List[Dict[str, int]] = []

    amt = int(amount_in)
    for i, hop in enumerate(route):
        h = _require_mapping(hop, name=f"route[{i}]")
        pool_id = _require_str(h.get("pool_id"), name=f"route[{i}].pool_id")
        a_in = _require_str(h.get("asset_in"), name=f"route[{i}].asset_in")
        a_out = _require_str(h.get("asset_out"), name=f"route[{i}].asset_out")

        p = pools.get(pool_id)
        if p is None:
            raise ValueError(f"unknown pool_id: {pool_id}")
        if p.status != PoolStatus.ACTIVE:
            raise ValueError(f"pool not ACTIVE: {p.pool_id}")
        if p.curve_tag != CURVE_TAG_CPMM:
            raise ValueError(f"only CPMM supported in v1 verifier: {p.pool_id} has {p.curve_tag!r}")

        rin, rout, idx_in, idx_out = _pool_dir_reserves(p, asset_in=a_in, asset_out=a_out, reserves=reserves)
        out, (new_rin, new_rout) = swap_exact_in_for_pool(p, reserve_in=rin, reserve_out=rout, amount_in=amt)

        # Update canonical reserves.
        if idx_in == 0 and idx_out == 1:
            reserves[p.pool_id] = (int(new_rin), int(new_rout))
        else:
            reserves[p.pool_id] = (int(new_rout), int(new_rin))
        hop_io.append({"amount_in": int(amt), "amount_out": int(out)})
        amt = int(out)

    return int(amt), hop_io


def _best_direct_out(
    *, pools: Sequence[PoolState], asset_in: AssetId, asset_out: AssetId, amount_in: int
) -> Tuple[List[Mapping[str, Any]], int, List[Dict[str, int]]]:
    pools_map = _pools_by_id(pools)
    best_out = -1
    best_route: List[Mapping[str, Any]] = []
    best_hops: List[Dict[str, int]] = []

    for p in pools:
        if p.status != PoolStatus.ACTIVE or p.curve_tag != CURVE_TAG_CPMM:
            continue
        if not ((asset_in in (p.asset0, p.asset1)) and (asset_out in (p.asset0, p.asset1)) and asset_in != asset_out):
            continue
        # Direction must match the route hop’s declared assets.
        if not (
            (asset_in == p.asset0 and asset_out == p.asset1)
            or (asset_in == p.asset1 and asset_out == p.asset0)
        ):
            continue
        route = [{"pool_id": p.pool_id, "asset_in": asset_in, "asset_out": asset_out}]
        try:
            out, hop_io = _quote_exact_in_route(pools=pools_map, route=route, amount_in=amount_in)
        except Exception:
            continue
        # Tie-break by lex pool_id (route is 1-hop, so this is sufficient).
        if out > best_out or (out == best_out and route and best_route and str(route[0]["pool_id"]) < str(best_route[0]["pool_id"])):
            best_out = int(out)
            best_route = route
            best_hops = list(hop_io)

    if best_out < 0:
        raise ValueError("no valid direct CPMM route found")
    return best_route, int(best_out), best_hops


def verify_route_improvement_witness(payload: Mapping[str, Any]) -> Tuple[bool, Optional[str]]:
    try:
        schema = payload.get("schema")
        if schema != "zenodex/route_improvement_witness/v1":
            return _fail("unsupported schema")

        job = _require_mapping(payload.get("job"), name="job")
        asset_in = _require_str(job.get("asset_in"), name="job.asset_in")
        asset_out = _require_str(job.get("asset_out"), name="job.asset_out")
        amount_in = _require_int(job.get("amount_in"), name="job.amount_in")
        if amount_in <= 0:
            return _fail("amount_in must be positive")

        pools_raw = _require_list(payload.get("pools"), name="pools")
        pools = [_pool_from_json(_require_mapping(p, name=f"pools[{i}]")) for i, p in enumerate(pools_raw)]
        pools_map = _pools_by_id(pools)

        baseline = _require_mapping(payload.get("baseline"), name="baseline")
        proposal = _require_mapping(payload.get("proposal"), name="proposal")
        improves_flag = bool(payload.get("improves", False))

        baseline_route = _require_list(baseline.get("route"), name="baseline.route")
        baseline_amt_out_claim = _require_int(baseline.get("amount_out"), name="baseline.amount_out")
        proposal_route = _require_list(proposal.get("route"), name="proposal.route")
        proposal_amt_out_claim = _require_int(proposal.get("amount_out"), name="proposal.amount_out")

        # 1) Baseline must match deterministic "best direct route".
        base_det_route, base_det_out, _ = _best_direct_out(
            pools=pools, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in
        )
        if baseline_amt_out_claim != base_det_out:
            return _fail("baseline.amount_out does not match recomputed direct best")
        if json.dumps(baseline_route, sort_keys=True) != json.dumps(base_det_route, sort_keys=True):
            return _fail("baseline.route does not match recomputed direct best route")

        # 2) Proposal must replay to the claimed output.
        if len(proposal_route) not in (1, 2):
            return _fail("proposal.route must have 1 or 2 hops")
        # Sanity: chained assets must match job.
        p0 = _require_mapping(proposal_route[0], name="proposal.route[0]")
        if _require_str(p0.get("asset_in"), name="proposal.route[0].asset_in") != asset_in:
            return _fail("proposal first hop asset_in mismatch")
        plast = _require_mapping(proposal_route[-1], name="proposal.route[-1]")
        if _require_str(plast.get("asset_out"), name="proposal.route[-1].asset_out") != asset_out:
            return _fail("proposal last hop asset_out mismatch")
        if len(proposal_route) == 2:
            p1 = _require_mapping(proposal_route[1], name="proposal.route[1]")
            mid0 = _require_str(p0.get("asset_out"), name="proposal.route[0].asset_out")
            mid1 = _require_str(p1.get("asset_in"), name="proposal.route[1].asset_in")
            if mid0 != mid1:
                return _fail("proposal intermediate asset mismatch")

        prop_out, _ = _quote_exact_in_route(pools=pools_map, route=[_require_mapping(h, name="hop") for h in proposal_route], amount_in=amount_in)
        if proposal_amt_out_claim != prop_out:
            return _fail("proposal.amount_out does not match replay")

        # 3) Improvement check must match improves flag.
        improves_det = bool(prop_out > base_det_out)
        if improves_det != improves_flag:
            return _fail("improves flag mismatch vs deterministic comparison")
        if improves_flag and not (prop_out > base_det_out):
            return _fail("proposal does not improve baseline")

        return True, None
    except Exception as exc:
        return False, str(exc)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, help="Path to route improvement witness JSON.")
    args = ap.parse_args()
    payload = json.loads(Path(args.input).read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        sys.stdout.write(json.dumps({"ok": False, "error": "payload must be an object"}, separators=(",", ":")) + "\n")
        raise SystemExit(0)
    ok, err = verify_route_improvement_witness(payload)
    if ok:
        sys.stdout.write(json.dumps({"ok": True}, separators=(",", ":")) + "\n")
    else:
        sys.stdout.write(json.dumps({"ok": False, "error": str(err or "rejected")}, separators=(",", ":")) + "\n")


if __name__ == "__main__":
    main()

