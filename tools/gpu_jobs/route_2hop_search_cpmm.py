#!/usr/bin/env python3
"""
GPU-assisted 2-hop CPMM route search (exact-in), emitting a replayable witness.

Design goal: "expensive search, cheap verification".
- Search: optionally uses Torch (MPS/CUDA) or CuPy (CUDA) with float64
  *approximation* to rank many 2-hop candidates quickly.
- Binding: exact amounts are always computed by deterministic integer replay
  using the functional core CPMM kernel; GPU never decides the final amount.
- Verification: a verifier can deterministically replay the witness and check:
    (a) baseline direct best, (b) proposed 2-hop output, (c) improvement.

This is suitable as an experiment/UX tool and as a prototype for a "route
improvement bounty" useful-work market.
"""

from __future__ import annotations

import argparse
import heapq
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple

# Allow `python3 tools/gpu_jobs/...` from repo root without needing `-m`.
import os
import sys


_REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
if _REPO_ROOT not in sys.path:
    sys.path.insert(0, _REPO_ROOT)

from src.core.amm_dispatch import swap_exact_in_for_pool  # noqa: E402
from src.state.balances import Amount, AssetId  # noqa: E402
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus  # noqa: E402


BPS_DENOM = 10_000


def _try_import_torch() -> Any | None:
    try:
        import torch  # type: ignore

        return torch
    except Exception:
        return None


def _try_import_cupy() -> Any | None:
    try:
        import cupy  # type: ignore

        return cupy
    except Exception:
        return None


@dataclass(frozen=True)
class Hop:
    pool_id: str
    asset_in: AssetId
    asset_out: AssetId


@dataclass(frozen=True)
class Route:
    hops: Tuple[Hop, ...]

    def hop_count(self) -> int:
        return len(self.hops)

    def route_key(self) -> Tuple[int, Tuple[str, ...], str]:
        # Deterministic tie-break key (compatible with src/core/routing.py intent):
        # - fewer hops
        # - lex pool_id sequence
        # - lex intermediate asset ("" for direct)
        hop_n = self.hop_count()
        pool_ids = tuple(h.pool_id for h in self.hops)
        mid = ""
        if hop_n == 2:
            mid = str(self.hops[0].asset_out)
        return (int(hop_n), pool_ids, mid)


def _require_int(name: str, v: Any) -> int:
    if not isinstance(v, int) or isinstance(v, bool):
        raise TypeError(f"{name} must be an int, got {type(v).__name__}")
    return int(v)


def _require_str(name: str, v: Any) -> str:
    if not isinstance(v, str) or not v:
        raise TypeError(f"{name} must be a non-empty string, got {type(v).__name__}")
    return str(v)


def _pool_status_from_str(s: str) -> PoolStatus:
    raw = str(s).strip().upper()
    try:
        return PoolStatus[raw]
    except KeyError as exc:
        raise ValueError(f"unknown pool status: {s!r}") from exc


def _pool_from_json(obj: Mapping[str, Any]) -> PoolState:
    pool_id = _require_str("pool_id", obj.get("pool_id"))
    asset0 = _require_str("asset0", obj.get("asset0"))
    asset1 = _require_str("asset1", obj.get("asset1"))
    reserve0 = _require_int("reserve0", obj.get("reserve0"))
    reserve1 = _require_int("reserve1", obj.get("reserve1"))
    fee_bps = _require_int("fee_bps", obj.get("fee_bps"))
    lp_supply = _require_int("lp_supply", obj.get("lp_supply", 0))
    status = _pool_status_from_str(_require_str("status", obj.get("status", "ACTIVE")))
    created_at = _require_int("created_at", obj.get("created_at", 0))
    curve_tag = _require_str("curve_tag", obj.get("curve_tag", CURVE_TAG_CPMM))
    curve_params = obj.get("curve_params", "")
    if curve_params is None:
        curve_params = ""
    if not isinstance(curve_params, (str, dict)):
        raise TypeError("curve_params must be a string or object")
    return PoolState(
        pool_id=pool_id,
        asset0=asset0,
        asset1=asset1,
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        lp_supply=lp_supply,
        status=status,
        created_at=created_at,
        curve_tag=curve_tag,
        curve_params=curve_params if isinstance(curve_params, str) else curve_params,
    )


def _load_job(path: Path) -> Dict[str, Any]:
    obj = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(obj, dict):
        raise TypeError("input JSON must be an object")
    return obj


def _pools_by_id(pools: Sequence[PoolState]) -> Dict[str, PoolState]:
    out: Dict[str, PoolState] = {}
    for p in pools:
        if p.pool_id in out:
            raise ValueError(f"duplicate pool_id: {p.pool_id}")
        out[p.pool_id] = p
    return out


def _pool_direction_reserves(p: PoolState, *, asset_in: AssetId, asset_out: AssetId, reserves: Dict[str, Tuple[int, int]]) -> Tuple[int, int, int, int]:
    if asset_in == p.asset0 and asset_out == p.asset1:
        r0, r1 = reserves[p.pool_id]
        return int(r0), int(r1), 0, 1
    if asset_in == p.asset1 and asset_out == p.asset0:
        r0, r1 = reserves[p.pool_id]
        return int(r1), int(r0), 1, 0
    raise ValueError(f"pool {p.pool_id} does not connect {asset_in}->{asset_out}")


def _quote_exact_in_route(*, pools: Dict[str, PoolState], route: Route, amount_in: Amount) -> Tuple[int, List[Dict[str, int]]]:
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")
    # Working reserves snapshot (do not mutate PoolState).
    reserves: Dict[str, Tuple[int, int]] = {pid: (int(p.reserve0), int(p.reserve1)) for pid, p in pools.items()}
    hop_outs: List[Dict[str, int]] = []

    amt = int(amount_in)
    for h in route.hops:
        p = pools.get(h.pool_id)
        if p is None:
            raise ValueError(f"unknown pool_id in route: {h.pool_id}")
        if p.status != PoolStatus.ACTIVE:
            raise ValueError(f"pool not ACTIVE: {p.pool_id}")
        if p.curve_tag != CURVE_TAG_CPMM:
            raise ValueError(f"only CPMM supported in this prototype tool: {p.pool_id} has {p.curve_tag!r}")

        rin, rout, idx_in, idx_out = _pool_direction_reserves(p, asset_in=h.asset_in, asset_out=h.asset_out, reserves=reserves)
        out, (new_rin, new_rout) = swap_exact_in_for_pool(p, reserve_in=rin, reserve_out=rout, amount_in=amt)

        # Update reserves in canonical (reserve0,reserve1) order.
        r0, r1 = reserves[p.pool_id]
        if idx_in == 0 and idx_out == 1:
            reserves[p.pool_id] = (int(new_rin), int(new_rout))
        else:
            reserves[p.pool_id] = (int(new_rout), int(new_rin))
        hop_outs.append({"amount_in": int(amt), "amount_out": int(out)})
        amt = int(out)

    return int(amt), hop_outs


def _dir_reserves_from_pool(p: PoolState, *, asset_in: AssetId, asset_out: AssetId) -> Tuple[int, int]:
    if asset_in == p.asset0 and asset_out == p.asset1:
        return int(p.reserve0), int(p.reserve1)
    if asset_in == p.asset1 and asset_out == p.asset0:
        return int(p.reserve1), int(p.reserve0)
    raise ValueError(f"pool {p.pool_id} does not connect {asset_in}->{asset_out}")


def _quote_exact_in_2hop_candidate(
    *,
    p1: PoolState,
    p2: PoolState,
    asset_in: AssetId,
    asset_mid: AssetId,
    asset_out: AssetId,
    amount_in: int,
) -> Tuple[int, List[Dict[str, int]]]:
    # Hot path: avoid copying a full reserves snapshot for each candidate.
    rin1, rout1 = _dir_reserves_from_pool(p1, asset_in=asset_in, asset_out=asset_mid)
    out1, _ = swap_exact_in_for_pool(p1, reserve_in=rin1, reserve_out=rout1, amount_in=int(amount_in))
    rin2, rout2 = _dir_reserves_from_pool(p2, asset_in=asset_mid, asset_out=asset_out)
    out2, _ = swap_exact_in_for_pool(p2, reserve_in=rin2, reserve_out=rout2, amount_in=int(out1))
    hop_outs = [{"amount_in": int(amount_in), "amount_out": int(out1)}, {"amount_in": int(out1), "amount_out": int(out2)}]
    return int(out2), hop_outs


def _best_direct_route(*, pools: Sequence[PoolState], asset_in: AssetId, asset_out: AssetId, amount_in: int) -> Tuple[Optional[Route], int, List[Dict[str, int]]]:
    best_route: Optional[Route] = None
    best_out = -1
    best_hops: List[Dict[str, int]] = []

    pools_map = _pools_by_id(pools)
    for p in pools:
        if p.status != PoolStatus.ACTIVE or p.curve_tag != CURVE_TAG_CPMM:
            continue
        if not ((asset_in in (p.asset0, p.asset1)) and (asset_out in (p.asset0, p.asset1)) and asset_in != asset_out):
            continue
        try:
            if asset_in == p.asset0 and asset_out == p.asset1:
                route = Route(hops=(Hop(pool_id=p.pool_id, asset_in=asset_in, asset_out=asset_out),))
            elif asset_in == p.asset1 and asset_out == p.asset0:
                route = Route(hops=(Hop(pool_id=p.pool_id, asset_in=asset_in, asset_out=asset_out),))
            else:
                continue
            out, hop_outs = _quote_exact_in_route(pools=pools_map, route=route, amount_in=int(amount_in))
        except Exception:
            continue
        if out > best_out or (out == best_out and best_route is not None and route.route_key() < best_route.route_key()):
            best_out = int(out)
            best_route = route
            best_hops = list(hop_outs)

    if best_route is None:
        return None, -1, []
    return best_route, int(best_out), best_hops


def _enumerate_2hop_candidates(
    *, pools: Sequence[PoolState], asset_in: AssetId, asset_out: AssetId
) -> List[Tuple[PoolState, PoolState, AssetId]]:
    # Candidate is (p1, p2, mid_asset) where:
    # asset_in --p1--> mid --p2--> asset_out
    pools_by_asset: Dict[AssetId, List[PoolState]] = {}
    for p in pools:
        if p.status != PoolStatus.ACTIVE or p.curve_tag != CURVE_TAG_CPMM:
            continue
        pools_by_asset.setdefault(p.asset0, []).append(p)
        pools_by_asset.setdefault(p.asset1, []).append(p)

    first_hops = pools_by_asset.get(asset_in, [])
    cands: List[Tuple[PoolState, PoolState, AssetId]] = []
    for p1 in first_hops:
        if asset_in == p1.asset0:
            mid = p1.asset1
        else:
            mid = p1.asset0
        if mid == asset_out:
            continue
        for p2 in pools_by_asset.get(mid, []):
            if p2.pool_id == p1.pool_id:
                continue
            if not (asset_out == p2.asset0 or asset_out == p2.asset1):
                continue
            cands.append((p1, p2, mid))
    return cands


def _approx_2hop_outputs_torch(
    cands: Sequence[Tuple[PoolState, PoolState, AssetId]],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: int,
    prefer_gpu: bool,
) -> Tuple[List[float], str]:
    torch = _try_import_torch()
    if torch is None:
        raise RuntimeError("torch not available")

    device = torch.device("cpu")
    backend = "torch:cpu"
    if prefer_gpu and bool(getattr(torch.backends, "mps", None)) and torch.backends.mps.is_available():
        device = torch.device("mps")
        backend = "torch:mps"
    elif prefer_gpu and bool(getattr(torch, "cuda", None)) and torch.cuda.is_available():
        device = torch.device("cuda")
        backend = "torch:cuda"

    def _dir_reserves(p: PoolState, a_in: AssetId, a_out: AssetId) -> Tuple[float, float]:
        if a_in == p.asset0 and a_out == p.asset1:
            return float(p.reserve0), float(p.reserve1)
        if a_in == p.asset1 and a_out == p.asset0:
            return float(p.reserve1), float(p.reserve0)
        raise ValueError("bad direction")

    r1_in: List[float] = []
    r1_out: List[float] = []
    f1: List[float] = []
    r2_in: List[float] = []
    r2_out: List[float] = []
    f2: List[float] = []

    for p1, p2, mid in cands:
        a1_in = asset_in
        a1_out = mid
        a2_in = mid
        a2_out = asset_out
        rin1, rout1 = _dir_reserves(p1, a1_in, a1_out)
        rin2, rout2 = _dir_reserves(p2, a2_in, a2_out)
        r1_in.append(rin1)
        r1_out.append(rout1)
        f1.append(float(p1.fee_bps))
        r2_in.append(rin2)
        r2_out.append(rout2)
        f2.append(float(p2.fee_bps))

    t_r1_in = torch.tensor(r1_in, dtype=torch.float64, device=device)
    t_r1_out = torch.tensor(r1_out, dtype=torch.float64, device=device)
    t_f1 = torch.tensor(f1, dtype=torch.float64, device=device)
    t_r2_in = torch.tensor(r2_in, dtype=torch.float64, device=device)
    t_r2_out = torch.tensor(r2_out, dtype=torch.float64, device=device)
    t_f2 = torch.tensor(f2, dtype=torch.float64, device=device)

    amt = torch.full((len(cands),), float(amount_in), dtype=torch.float64, device=device)
    net1 = amt * (float(BPS_DENOM) - t_f1) / float(BPS_DENOM)
    out1 = t_r1_out * net1 / (t_r1_in + net1)
    net2 = out1 * (float(BPS_DENOM) - t_f2) / float(BPS_DENOM)
    out2 = t_r2_out * net2 / (t_r2_in + net2)
    # Move to CPU for deterministic selection/tie-break logic.
    out_list = [float(x) for x in out2.detach().to("cpu").tolist()]
    return out_list, backend


def _approx_2hop_outputs_cupy(
    cands: Sequence[Tuple[PoolState, PoolState, AssetId]],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: int,
) -> Tuple[List[float], str]:
    cp = _try_import_cupy()
    if cp is None:
        raise RuntimeError("cupy not available")

    def _dir_reserves(p: PoolState, a_in: AssetId, a_out: AssetId) -> Tuple[float, float]:
        if a_in == p.asset0 and a_out == p.asset1:
            return float(p.reserve0), float(p.reserve1)
        if a_in == p.asset1 and a_out == p.asset0:
            return float(p.reserve1), float(p.reserve0)
        raise ValueError("bad direction")

    r1_in: List[float] = []
    r1_out: List[float] = []
    f1: List[float] = []
    r2_in: List[float] = []
    r2_out: List[float] = []
    f2: List[float] = []

    for p1, p2, mid in cands:
        rin1, rout1 = _dir_reserves(p1, asset_in, mid)
        rin2, rout2 = _dir_reserves(p2, mid, asset_out)
        r1_in.append(rin1)
        r1_out.append(rout1)
        f1.append(float(p1.fee_bps))
        r2_in.append(rin2)
        r2_out.append(rout2)
        f2.append(float(p2.fee_bps))

    t_r1_in = cp.asarray(r1_in, dtype=cp.float64)
    t_r1_out = cp.asarray(r1_out, dtype=cp.float64)
    t_f1 = cp.asarray(f1, dtype=cp.float64)
    t_r2_in = cp.asarray(r2_in, dtype=cp.float64)
    t_r2_out = cp.asarray(r2_out, dtype=cp.float64)
    t_f2 = cp.asarray(f2, dtype=cp.float64)

    amt = cp.full((len(cands),), float(amount_in), dtype=cp.float64)
    net1 = amt * (float(BPS_DENOM) - t_f1) / float(BPS_DENOM)
    out1 = t_r1_out * net1 / (t_r1_in + net1)
    net2 = out1 * (float(BPS_DENOM) - t_f2) / float(BPS_DENOM)
    out2 = t_r2_out * net2 / (t_r2_in + net2)

    out_list = [float(x) for x in cp.asnumpy(out2).tolist()]
    return out_list, "cupy:cuda"


def _approx_2hop_outputs_cpu(
    cands: Sequence[Tuple[PoolState, PoolState, AssetId]],
    *,
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: int,
) -> Tuple[List[float], str]:
    try:
        import numpy as np  # type: ignore
    except Exception:
        np = None  # type: ignore

    def _dir_reserves(p: PoolState, a_in: AssetId, a_out: AssetId) -> Tuple[float, float]:
        if a_in == p.asset0 and a_out == p.asset1:
            return float(p.reserve0), float(p.reserve1)
        if a_in == p.asset1 and a_out == p.asset0:
            return float(p.reserve1), float(p.reserve0)
        raise ValueError("bad direction")

    # Vectorize formula evaluation (CPU). We still need a single pass to extract per-candidate reserves/fees.
    if np is not None:
        n = int(len(cands))
        r1_in = np.empty((n,), dtype=np.float64)
        r1_out = np.empty((n,), dtype=np.float64)
        f1 = np.empty((n,), dtype=np.float64)
        r2_in = np.empty((n,), dtype=np.float64)
        r2_out = np.empty((n,), dtype=np.float64)
        f2 = np.empty((n,), dtype=np.float64)
        for i, (p1, p2, mid) in enumerate(cands):
            rin1, rout1 = _dir_reserves(p1, asset_in, mid)
            rin2, rout2 = _dir_reserves(p2, mid, asset_out)
            r1_in[i] = rin1
            r1_out[i] = rout1
            f1[i] = float(p1.fee_bps)
            r2_in[i] = rin2
            r2_out[i] = rout2
            f2[i] = float(p2.fee_bps)

        amt = float(amount_in)
        net1 = amt * (float(BPS_DENOM) - f1) / float(BPS_DENOM)
        out1 = r1_out * net1 / (r1_in + net1)
        net2 = out1 * (float(BPS_DENOM) - f2) / float(BPS_DENOM)
        out2 = r2_out * net2 / (r2_in + net2)
        return [float(x) for x in out2.tolist()], "numpy:float64"

    # Fallback: scalar loop (slower).
    outs: List[float] = []
    for p1, p2, mid in cands:
        rin1, rout1 = _dir_reserves(p1, asset_in, mid)
        rin2, rout2 = _dir_reserves(p2, mid, asset_out)
        net1 = float(amount_in) * (float(BPS_DENOM) - float(p1.fee_bps)) / float(BPS_DENOM)
        out1 = rout1 * net1 / (rin1 + net1)
        net2 = out1 * (float(BPS_DENOM) - float(p2.fee_bps)) / float(BPS_DENOM)
        out2 = rout2 * net2 / (rin2 + net2)
        outs.append(float(out2))
    return outs, "cpu:float64"


def _best_2hop_route_topk(
    *,
    pools: Sequence[PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: int,
    topk: int,
    prefer_gpu: bool,
) -> Tuple[Optional[Route], int, List[Dict[str, int]], Dict[str, Any]]:
    cands = _enumerate_2hop_candidates(pools=pools, asset_in=asset_in, asset_out=asset_out)
    if not cands:
        return None, -1, [], {"searched_pairs": 0, "approx_backend": "none", "topk": int(topk)}

    torch = _try_import_torch()
    if torch is not None:
        approx, backend = _approx_2hop_outputs_torch(cands, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in, prefer_gpu=prefer_gpu)
    elif prefer_gpu and _try_import_cupy() is not None:
        approx, backend = _approx_2hop_outputs_cupy(cands, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
    else:
        approx, backend = _approx_2hop_outputs_cpu(cands, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)

    # Pick top-k by approximate output; tie-break deterministically by route_key.
    # Avoid full sort: keep selection is O(n log k) for small k.
    n_cands = int(len(cands))

    def _route_key_for(p1: PoolState, p2: PoolState, mid: AssetId) -> Tuple[int, Tuple[str, ...], str]:
        return (2, (str(p1.pool_id), str(p2.pool_id)), str(mid))

    def _approx_key(i: int) -> Tuple[float, Tuple[int, Tuple[str, ...], str]]:
        p1, p2, mid = cands[i]
        return (-float(approx[i]), _route_key_for(p1, p2, mid))

    k = max(1, int(topk))
    if k >= n_cands:
        keep = list(range(n_cands))
    else:
        keep = heapq.nsmallest(k, range(n_cands), key=_approx_key)

    best_route: Optional[Route] = None
    best_out = -1
    best_key: Optional[Tuple[int, Tuple[str, ...], str]] = None
    best_hops: List[Dict[str, int]] = []
    for i in keep:
        p1, p2, mid = cands[i]
        rkey = _route_key_for(p1, p2, mid)
        try:
            out, hop_outs = _quote_exact_in_2hop_candidate(
                p1=p1, p2=p2, asset_in=asset_in, asset_mid=mid, asset_out=asset_out, amount_in=int(amount_in)
            )
        except Exception:
            continue
        if out > best_out or (out == best_out and best_key is not None and rkey < best_key):
            best_out = int(out)
            best_key = rkey
            best_route = Route(
                hops=(
                    Hop(pool_id=p1.pool_id, asset_in=asset_in, asset_out=mid),
                    Hop(pool_id=p2.pool_id, asset_in=mid, asset_out=asset_out),
                )
            )
            best_hops = list(hop_outs)

    meta = {"searched_pairs": int(len(cands)), "approx_backend": str(backend), "topk": int(topk)}
    if best_route is None:
        return None, -1, [], meta
    return best_route, int(best_out), best_hops, meta


def _best_2hop_route_adaptive_prune(
    *,
    pools: Sequence[PoolState],
    asset_in: AssetId,
    asset_out: AssetId,
    amount_in: int,
    topk_max: int,
    prefer_gpu: bool,
) -> Tuple[Optional[Route], int, List[Dict[str, int]], Dict[str, Any]]:
    """
    UB-pruning variant (experimental):
      - rank candidates by continuous float64 UB (approx output)
      - exact-evaluate in that order
      - stop once floor(UB_next) <= best_exact_seen

    This is deterministic given deterministic approx values and route_key tie-break.
    It does NOT guarantee canonical tie-break across *all* exact-maximizers in tie-heavy regimes.
    """
    try:
        import numpy as np  # type: ignore

        have_np = True
    except Exception:
        np = None  # type: ignore
        have_np = False

    # Fast path: vectorized UB scoring per-mid (avoid enumerating all pairs as Python tuples).
    if have_np:
        pools_map = _pools_by_id(pools)
        # Group directional pools by intermediate asset `mid`.
        ins_by_mid: Dict[AssetId, List[str]] = {}
        outs_by_mid: Dict[AssetId, List[str]] = {}
        # Also store directional reserves/fees for each pool_id in each direction we need.
        # (We keep pool_id lists per mid and look up PoolState for exact replay.)
        dir_cache: Dict[Tuple[str, AssetId, AssetId], Tuple[int, int, int]] = {}

        def _dir(p: PoolState, a_in: AssetId, a_out: AssetId) -> Tuple[int, int]:
            return _dir_reserves_from_pool(p, asset_in=a_in, asset_out=a_out)

        # Build groups.
        for p in pools:
            if p.status != PoolStatus.ACTIVE or p.curve_tag != CURVE_TAG_CPMM:
                continue
            # First hop candidates: asset_in -> mid
            if asset_in == p.asset0:
                mid = p.asset1
            elif asset_in == p.asset1:
                mid = p.asset0
            else:
                mid = None
            if mid is not None and mid != asset_out and mid != asset_in:
                rin, rout = _dir(p, asset_in, mid)
                ins_by_mid.setdefault(mid, []).append(p.pool_id)
                dir_cache[(p.pool_id, asset_in, mid)] = (int(rin), int(rout), int(p.fee_bps))

            # Second hop candidates: mid -> asset_out
            if asset_out == p.asset0:
                mid2 = p.asset1
            elif asset_out == p.asset1:
                mid2 = p.asset0
            else:
                mid2 = None
            if mid2 is not None and mid2 != asset_in and mid2 != asset_out:
                rin2, rout2 = _dir(p, mid2, asset_out)
                outs_by_mid.setdefault(mid2, []).append(p.pool_id)
                dir_cache[(p.pool_id, mid2, asset_out)] = (int(rin2), int(rout2), int(p.fee_bps))

        mids = [m for m in ins_by_mid.keys() if m in outs_by_mid]
        if not mids:
            return None, -1, [], {"searched_pairs": 0, "approx_backend": "numpy:float64", "topk_max": int(topk_max), "evaluated": 0, "pruned": False, "vectorized": True}

        k_max = int(topk_max)
        if k_max <= 0:
            k_max = 256
        # Per-mid top-(k_max+1) union contains global top-(k_max+1) by UB.
        per_mid_t = int(k_max) + 1

        cand: List[Tuple[float, Tuple[int, Tuple[str, ...], str], str, str, AssetId]] = []
        searched_pairs = 0

        for mid in mids:
            ins = list(ins_by_mid.get(mid, []))
            outs = list(outs_by_mid.get(mid, []))
            if not ins or not outs:
                continue
            m = int(len(ins))
            n = int(len(outs))
            searched_pairs += int(m * n)

            # Directional arrays.
            r1_in = np.array([dir_cache[(pid, asset_in, mid)][0] for pid in ins], dtype=np.float64)
            r1_out = np.array([dir_cache[(pid, asset_in, mid)][1] for pid in ins], dtype=np.float64)
            f1 = np.array([dir_cache[(pid, asset_in, mid)][2] for pid in ins], dtype=np.float64)

            r2_in = np.array([dir_cache[(pid, mid, asset_out)][0] for pid in outs], dtype=np.float64)
            r2_out = np.array([dir_cache[(pid, mid, asset_out)][1] for pid in outs], dtype=np.float64)
            f2 = np.array([dir_cache[(pid, mid, asset_out)][2] for pid in outs], dtype=np.float64)

            amt = float(amount_in)
            net1 = amt * (float(BPS_DENOM) - f1) / float(BPS_DENOM)
            out1 = r1_out * net1 / (r1_in + net1)  # (m,)
            # UB out2 matrix via broadcasting (m,n)
            out1_mat = out1.reshape((m, 1))
            net2 = out1_mat * (float(BPS_DENOM) - f2.reshape((1, n))) / float(BPS_DENOM)
            ub2 = r2_out.reshape((1, n)) * net2 / (r2_in.reshape((1, n)) + net2)
            flat = ub2.reshape((m * n,))
            t = int(min(int(per_mid_t), int(m * n)))
            if t <= 0:
                continue
            if t < int(m * n):
                top = np.argpartition(-flat, kth=t - 1)[:t]
            else:
                top = np.arange(int(m * n), dtype=np.int64)

            # Deterministic order among these by (-ub, route_key).
            # route_key is (hop_count=2, (p1_id,p2_id), mid).
            for flat_k in top.tolist():
                ii = int(flat_k) // int(n)
                jj = int(flat_k) % int(n)
                ubv = float(flat[int(flat_k)])
                p1_id = str(ins[ii])
                p2_id = str(outs[jj])
                rkey = (2, (p1_id, p2_id), str(mid))
                cand.append((ubv, rkey, p1_id, p2_id, mid))

        if not cand:
            return None, -1, [], {"searched_pairs": int(searched_pairs), "approx_backend": "numpy:float64", "topk_max": int(k_max), "evaluated": 0, "pruned": False, "vectorized": True}

        # Global top-(k_max+1) by (-ub, route_key).
        cand.sort(key=lambda x: (-float(x[0]), x[1]))
        order = cand[: min(len(cand), int(k_max) + 1)]

        best_route: Optional[Route] = None
        best_out = -1
        best_key: Optional[Tuple[int, Tuple[str, ...], str]] = None
        best_hops: List[Dict[str, int]] = []

        evaluated = 0
        pruned = False
        for j in range(min(int(k_max), len(order))):
            ubv, rkey, p1_id, p2_id, mid = order[j]
            p1 = pools_map.get(p1_id)
            p2 = pools_map.get(p2_id)
            if p1 is None or p2 is None:
                evaluated += 1
                continue
            try:
                out, hop_outs = _quote_exact_in_2hop_candidate(
                    p1=p1, p2=p2, asset_in=asset_in, asset_mid=mid, asset_out=asset_out, amount_in=int(amount_in)
                )
            except Exception:
                evaluated += 1
                continue
            evaluated += 1
            if out > best_out or (out == best_out and best_key is not None and rkey < best_key):
                best_out = int(out)
                best_key = rkey
                best_route = Route(
                    hops=(
                        Hop(pool_id=p1.pool_id, asset_in=asset_in, asset_out=mid),
                        Hop(pool_id=p2.pool_id, asset_in=mid, asset_out=asset_out),
                    )
                )
                best_hops = list(hop_outs)

            nxt = j + 1
            if nxt < len(order) and best_out >= 0:
                ub_next = float(order[nxt][0])
                ub_next_int = int(ub_next) if ub_next > 0 else 0
                if ub_next_int <= int(best_out):
                    pruned = True
                    break

        meta = {
            "searched_pairs": int(searched_pairs),
            "approx_backend": "numpy:float64",
            "topk_max": int(k_max),
            "evaluated": int(evaluated),
            "pruned": bool(pruned),
            "vectorized": True,
            "union_candidates": int(len(cand)),
        }
        if best_route is None:
            return None, -1, [], meta
        return best_route, int(best_out), best_hops, meta

    # Fallback: original path (enumerate all pairs as Python tuples).
    cands = _enumerate_2hop_candidates(pools=pools, asset_in=asset_in, asset_out=asset_out)
    if not cands:
        return None, -1, [], {"searched_pairs": 0, "approx_backend": "none", "topk_max": int(topk_max), "evaluated": 0, "pruned": False}

    torch = _try_import_torch()
    if torch is not None:
        approx, backend = _approx_2hop_outputs_torch(
            cands, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in, prefer_gpu=prefer_gpu
        )
    elif prefer_gpu and _try_import_cupy() is not None:
        approx, backend = _approx_2hop_outputs_cupy(cands, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)
    else:
        approx, backend = _approx_2hop_outputs_cpu(cands, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in)

    n_cands = int(len(cands))
    k_max = int(topk_max)
    if k_max <= 0:
        k_max = n_cands
    # Need k_max+1 to compute UB_next for pruning.
    L = min(n_cands, k_max + 1)

    def _route_key_for(p1: PoolState, p2: PoolState, mid: AssetId) -> Tuple[int, Tuple[str, ...], str]:
        return (2, (str(p1.pool_id), str(p2.pool_id)), str(mid))

    def _approx_key(i: int) -> Tuple[float, Tuple[int, Tuple[str, ...], str]]:
        p1, p2, mid = cands[i]
        return (-float(approx[i]), _route_key_for(p1, p2, mid))

    # Order the top-(k_max+1) candidates by UB desc + deterministic tie-break.
    order = heapq.nsmallest(L, range(n_cands), key=_approx_key)

    best_route: Optional[Route] = None
    best_out = -1
    best_key: Optional[Tuple[int, Tuple[str, ...], str]] = None
    best_hops: List[Dict[str, int]] = []

    evaluated = 0
    pruned = False
    for j in range(min(k_max, len(order))):
        i = int(order[j])
        p1, p2, mid = cands[i]
        rkey = _route_key_for(p1, p2, mid)
        try:
            out, hop_outs = _quote_exact_in_2hop_candidate(
                p1=p1, p2=p2, asset_in=asset_in, asset_mid=mid, asset_out=asset_out, amount_in=int(amount_in)
            )
        except Exception:
            evaluated += 1
            continue
        evaluated += 1
        if out > best_out or (out == best_out and best_key is not None and rkey < best_key):
            best_out = int(out)
            best_key = rkey
            best_route = Route(
                hops=(
                    Hop(pool_id=p1.pool_id, asset_in=asset_in, asset_out=mid),
                    Hop(pool_id=p2.pool_id, asset_in=mid, asset_out=asset_out),
                )
            )
            best_hops = list(hop_outs)

        # UB pruning check against the (j+1)-th UB candidate (if available).
        nxt = j + 1
        if nxt < len(order) and nxt < (k_max + 1) and best_out >= 0:
            ub_next = float(approx[int(order[nxt])])
            if ub_next > 0:
                ub_next_int = int(ub_next)
            else:
                ub_next_int = 0
            if ub_next_int <= int(best_out):
                pruned = True
                break

    meta = {
        "searched_pairs": int(n_cands),
        "approx_backend": str(backend),
        "topk_max": int(k_max),
        "evaluated": int(evaluated),
        "pruned": bool(pruned),
    }
    if best_route is None:
        return None, -1, [], meta
    return best_route, int(best_out), best_hops, meta


def _pool_json(p: PoolState) -> Dict[str, Any]:
    return {
        "pool_id": p.pool_id,
        "asset0": p.asset0,
        "asset1": p.asset1,
        "reserve0": int(p.reserve0),
        "reserve1": int(p.reserve1),
        "fee_bps": int(p.fee_bps),
        "curve_tag": p.curve_tag,
        "curve_params": p.curve_params,
        "lp_supply": int(p.lp_supply),
        "status": p.status.value,
        "created_at": int(p.created_at),
    }


def compute_route_improvement_witness_v1(
    job: Mapping[str, Any],
    *,
    prefer_gpu: bool,
    topk: int,
    adaptive_prune: bool,
    topk_max: int,
    allow_no_improvement: bool,
) -> Dict[str, Any]:
    """
    Build a `zenodex/route_improvement_witness/v1` payload from a job mapping.

    This function is intentionally "tool-side" only (non-consensus-critical):
    - GPU use is allowed but treated as an untrusted ranking hint.
    - Exact outputs are always derived from deterministic integer replay.
    """

    asset_in = _require_str("asset_in", job.get("asset_in"))
    asset_out = _require_str("asset_out", job.get("asset_out"))
    amount_in = _require_int("amount_in", job.get("amount_in"))
    if amount_in <= 0:
        raise ValueError("amount_in must be positive")

    pools_raw = job.get("pools")
    if not isinstance(pools_raw, list):
        raise TypeError("pools must be a list")
    pools = [_pool_from_json(p) for p in pools_raw]

    baseline_route, baseline_out, baseline_hops = _best_direct_route(
        pools=pools, asset_in=asset_in, asset_out=asset_out, amount_in=amount_in
    )
    if baseline_route is None:
        raise ValueError("no valid direct CPMM pool found for asset_in->asset_out")

    if bool(adaptive_prune):
        kmax = int(topk_max) if int(topk_max) > 0 else int(topk)
        proposal_route, proposal_out, proposal_hops, meta = _best_2hop_route_adaptive_prune(
            pools=pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            topk_max=int(kmax),
            prefer_gpu=bool(prefer_gpu),
        )
    else:
        proposal_route, proposal_out, proposal_hops, meta = _best_2hop_route_topk(
            pools=pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_in=amount_in,
            topk=int(topk),
            prefer_gpu=bool(prefer_gpu),
        )

    improves = False
    if proposal_route is not None and proposal_out > baseline_out:
        improves = True
    else:
        # Degrade gracefully: produce a witness with proposal==baseline for debugging.
        proposal_route = baseline_route
        proposal_out = baseline_out
        proposal_hops = list(baseline_hops)

    if not improves and not bool(allow_no_improvement):
        raise ValueError("no 2-hop improvement found over baseline (use allow_no_improvement to emit witness anyway)")

    return {
        "schema": "zenodex/route_improvement_witness/v1",
        "job": {"asset_in": asset_in, "asset_out": asset_out, "amount_in": int(amount_in), "max_hops": 2},
        "baseline": {
            "route": [{"pool_id": h.pool_id, "asset_in": h.asset_in, "asset_out": h.asset_out} for h in baseline_route.hops],
            "amount_out": int(baseline_out),
            "hop_io": list(baseline_hops),
        },
        "proposal": {
            "route": [{"pool_id": h.pool_id, "asset_in": h.asset_in, "asset_out": h.asset_out} for h in proposal_route.hops],
            "amount_out": int(proposal_out),
            "hop_io": list(proposal_hops),
        },
        "improves": bool(improves),
        "meta": dict(meta),
        "pools": [_pool_json(p) for p in pools],
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, help="Path to job JSON: {asset_in,asset_out,amount_in,pools:[...]}.")
    ap.add_argument("--output", required=True, help="Path to write route-improvement witness JSON.")
    ap.add_argument("--prefer-gpu", action="store_true", help="Prefer GPU backend when available (Torch MPS/CUDA, or CuPy CUDA).")
    ap.add_argument("--topk", type=int, default=256, help="Exact-evaluate only the top-K approximate 2-hop candidates.")
    ap.add_argument(
        "--adaptive-prune",
        action="store_true",
        help="Experimental: use UB-pruning (top-(Kmax+1) by UB, then exact-eval until pruned).",
    )
    ap.add_argument(
        "--topk-max",
        type=int,
        default=0,
        help="Max candidates to consider under --adaptive-prune (0 => use --topk).",
    )
    ap.add_argument(
        "--allow-no-improvement",
        action="store_true",
        help="Write witness even if no 2-hop route improves baseline direct best (proposal==baseline).",
    )
    args = ap.parse_args()

    job = _load_job(Path(args.input))
    out_obj = compute_route_improvement_witness_v1(
        job,
        prefer_gpu=bool(args.prefer_gpu),
        topk=int(args.topk),
        adaptive_prune=bool(args.adaptive_prune),
        topk_max=int(args.topk_max),
        allow_no_improvement=bool(args.allow_no_improvement),
    )
    Path(args.output).write_text(json.dumps(out_obj, indent=2, sort_keys=True) + "\n", encoding="utf-8")


if __name__ == "__main__":
    main()
