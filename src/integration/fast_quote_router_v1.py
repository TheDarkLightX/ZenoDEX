"""
Fast exact-in quote routing (integration-layer, advisory).

Safety posture
  - This module is NOT used in consensus-critical execution (Dex.step).
  - It never trusts floating-point math for final amounts:
      float64 is used only to rank candidate 2-hop routes quickly.
      the returned quote amounts are computed by deterministic integer replay
      using `src/core/amm_dispatch.swap_exact_in_for_pool`.
  - If numpy is unavailable or an error occurs, callers should fall back to the
    exact deterministic router in `src/core/routing.py`.

Algorithm (fast_v1)
  - Restrict to ACTIVE CPMM pools (v1 only).
  - Compute best direct (1-hop) exact quote.
  - For 2-hop: group by intermediate `mid` and compute a CPMM float64 approximation
    matrix per-mid; keep top-(Kmax+1) per-mid and union them; exact-evaluate the
    first Kmax candidates in global (-approx, route_key) order.

Notes
  - This is a heuristic search: it is not guaranteed to find the global best route.
    Default API routing_mode remains "exact" and should be used when optimality
    is required.
"""

from __future__ import annotations

from collections import OrderedDict
from dataclasses import dataclass
import hashlib
import threading
from typing import Any, Dict, List, Mapping, Optional, Sequence, Tuple

from ..core.amm_dispatch import swap_exact_in_for_pool
from ..core.amm_dispatch import swap_exact_out_for_pool
from ..core.routing import RouteHop, RouteLeg, RouteQuote
from ..core.split_routing_dispatch import (
    best_split_many_pools_exact_in_for_pools,
    best_split_two_pools_exact_out_for_pools,
    best_split_two_pools_exact_in_for_pools,
)
from ..core.routing import should_consider_exact_out_two_hop
from ..state.balances import Amount, AssetId
from ..state.canonical import domain_sep_bytes
from ..state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


BPS_DENOM = 10_000
MAX_PAIRS_PER_MID_DEFAULT = 2_000_000
MAX_UNION_CANDIDATES_DEFAULT = 250_000
INT64_MAX = (1 << 63) - 1
# Safe gross bound for computing `ceil(gross * fee_bps / 10_000)` in int64 without overflow
# when fee_bps <= 10_000:
#   gross * 10_000 + 9_999 <= INT64_MAX
SAFE_GROSS_FOR_INT64_FEE = (INT64_MAX - (BPS_DENOM - 1)) // BPS_DENOM
# For exact-out, extremely small amount_out values are dominated by integer ceil cascades.
# In that regime, continuous float ranking can mis-rank badly; we switch to bounded exact
# enumeration over 2-hop pairs (still advisory; final amounts are exact integer replay).
EXACT_OUT_MICRO_AMOUNT_OUT_MAX = 100
EXACT_OUT_MICRO_MAX_TOTAL_PAIRS = 250_000


def _strict_int_config(value: int, *, name: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _dir_reserves_cpmm(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId) -> Optional[Tuple[int, int]]:
    if pool.curve_tag != CURVE_TAG_CPMM:
        return None
    if asset_in == pool.asset0 and asset_out == pool.asset1:
        return int(pool.reserve0), int(pool.reserve1)
    if asset_in == pool.asset1 and asset_out == pool.asset0:
        return int(pool.reserve1), int(pool.reserve0)
    return None


def _quote_exact_in_onehop(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_in: int) -> Optional[int]:
    if pool.status != PoolStatus.ACTIVE:
        return None
    r = _dir_reserves_cpmm(pool, asset_in=asset_in, asset_out=asset_out)
    if r is None:
        return None
    rin, rout = r
    try:
        out, _ = swap_exact_in_for_pool(pool, reserve_in=int(rin), reserve_out=int(rout), amount_in=int(amount_in))
    except ValueError:
        return None
    return int(out)


def _quote_exact_in_twohop(
    p1: PoolState,
    p2: PoolState,
    *,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    amount_in: int,
) -> Optional[Tuple[int, int]]:
    # Returns (out_mid, out_final)
    r1 = _dir_reserves_cpmm(p1, asset_in=asset_in, asset_out=mid)
    r2 = _dir_reserves_cpmm(p2, asset_in=mid, asset_out=asset_out)
    if r1 is None or r2 is None:
        return None
    try:
        out_mid, _ = swap_exact_in_for_pool(p1, reserve_in=int(r1[0]), reserve_out=int(r1[1]), amount_in=int(amount_in))
        out_final, _ = swap_exact_in_for_pool(p2, reserve_in=int(r2[0]), reserve_out=int(r2[1]), amount_in=int(out_mid))
    except ValueError:
        return None
    return int(out_mid), int(out_final)


def _quote_exact_out_onehop(pool: PoolState, *, asset_in: AssetId, asset_out: AssetId, amount_out: int) -> Optional[int]:
    if pool.status != PoolStatus.ACTIVE:
        return None
    r = _dir_reserves_cpmm(pool, asset_in=asset_in, asset_out=asset_out)
    if r is None:
        return None
    rin, rout = r
    try:
        inn, _ = swap_exact_out_for_pool(pool, reserve_in=int(rin), reserve_out=int(rout), amount_out=int(amount_out))
    except ValueError:
        return None
    return int(inn)


def _quote_exact_out_twohop(
    p1: PoolState,
    p2: PoolState,
    *,
    asset_in: AssetId,
    mid: AssetId,
    asset_out: AssetId,
    amount_out: int,
) -> Optional[Tuple[int, int]]:
    # Returns (amount_in_total, mid_in) where mid_in is the hop2 input / hop1 output.
    r2 = _dir_reserves_cpmm(p2, asset_in=mid, asset_out=asset_out)
    if r2 is None:
        return None
    try:
        mid_in, _ = swap_exact_out_for_pool(p2, reserve_in=int(r2[0]), reserve_out=int(r2[1]), amount_out=int(amount_out))
    except ValueError:
        return None

    r1 = _dir_reserves_cpmm(p1, asset_in=asset_in, asset_out=mid)
    if r1 is None:
        return None
    try:
        amt_in, _ = swap_exact_out_for_pool(p1, reserve_in=int(r1[0]), reserve_out=int(r1[1]), amount_out=int(mid_in))
    except ValueError:
        return None
    return int(amt_in), int(mid_in)


def _quote_key_for(
    *,
    hop_count: int,
    pool_ids: Tuple[str, ...],
    mid: str,
    asset_out: AssetId,
) -> Tuple[int, int, str, str, str]:
    # Match the spirit of src/core/routing._quote_key:
    # (hop_count, leg_count, pool_seq, mid, asset_out).
    pool_seq = ";".join([",".join(pool_ids)]) if pool_ids else ""
    return (int(hop_count), 1, pool_seq, str(mid), str(asset_out))


def _quote_key(q: RouteQuote) -> Tuple[int, int, str, str, str]:
    """
    Tie-break key consistent with src/core/routing._quote_key:
      (hop_count, leg_count, pool_seq, mid, asset_out)
    """
    hop_count = sum(len(leg.hops) for leg in q.legs)
    leg_count = len(q.legs)
    pool_seq = ";".join(",".join(h.pool_id for h in leg.hops) for leg in q.legs)
    mid = ""
    if leg_count == 1 and hop_count == 2:
        mid = q.legs[0].hops[0].asset_out
    return (int(hop_count), int(leg_count), pool_seq, mid, str(q.asset_out))


def _snapshot_digest_for_sorted_pools(pools_sorted: Sequence[PoolState]) -> str:
    # Cache key only (not a consensus hash). Keep it deterministic and cheap.
    h = hashlib.sha256()
    h.update(domain_sep_bytes("fast_quote_router_snapshot", version=1))
    for p in pools_sorted:
        # Include enough to invalidate cache on any routing-relevant change.
        h.update(str(p.pool_id).encode("utf-8"))
        h.update(b"\x00")
        h.update(str(p.asset0).encode("utf-8"))
        h.update(b"\x00")
        h.update(str(p.asset1).encode("utf-8"))
        h.update(b"\x00")
        h.update(str(int(p.reserve0)).encode("ascii"))
        h.update(b"\x00")
        h.update(str(int(p.reserve1)).encode("ascii"))
        h.update(b"\x00")
        h.update(str(int(p.fee_bps)).encode("ascii"))
        h.update(b"\x00")
        h.update(str(p.curve_tag).encode("utf-8"))
        h.update(b"\x00")
        h.update(str(p.status.value).encode("utf-8"))
        h.update(b"\x00")
    return "sha256:" + h.hexdigest()


@dataclass(frozen=True)
class _MidArrays:
    ins_ids: Tuple[str, ...]
    outs_ids: Tuple[str, ...]
    r1_in: Any  # numpy.ndarray float64
    r1_out: Any
    f1: Any
    r2_in: Any
    r2_out: Any
    f2: Any


@dataclass(frozen=True)
class _PreparedPair:
    snapshot_digest: str
    asset_in: AssetId
    asset_out: AssetId
    direct_pool_ids: Tuple[str, ...]
    mids: Tuple[AssetId, ...]
    by_mid: Mapping[AssetId, _MidArrays]


class FastQuoteRouterV1:
    """
    Thread-safe bounded cache for fast_v1 prepared pair data.

    Important: caching only helps if the same pools snapshot is reused across calls.
    If callers send pools in every request, parsing dominates anyway.
    """

    def __init__(self, *, max_cache_pairs: int = 32) -> None:
        self._max_cache_pairs = max(1, _strict_int_config(max_cache_pairs, name="max_cache_pairs"))
        self._lock = threading.Lock()
        self._pair_cache: "OrderedDict[Tuple[str, str, str], _PreparedPair]" = OrderedDict()

    def _get_or_build_prepared(
        self,
        *,
        pools_sorted: Sequence[PoolState],
        asset_in: AssetId,
        asset_out: AssetId,
    ) -> _PreparedPair:
        try:
            import numpy as np
        except ImportError as exc:  # pragma: no cover - optional dependency
            raise RuntimeError("numpy not available") from exc

        snap = _snapshot_digest_for_sorted_pools(pools_sorted)
        key = (str(snap), str(asset_in), str(asset_out))
        with self._lock:
            hit = self._pair_cache.get(key)
            if hit is not None:
                # LRU refresh
                self._pair_cache.move_to_end(key)
                return hit

        # Build outside lock (can be expensive); then insert.
        ins_by_mid: Dict[AssetId, List[str]] = {}
        outs_by_mid: Dict[AssetId, List[str]] = {}
        # Directional cache: (pool_id,a_in,a_out) -> (reserve_in,reserve_out,fee_bps)
        dir_cache: Dict[Tuple[str, AssetId, AssetId], Tuple[int, int, int]] = {}
        direct: List[str] = []

        for p in pools_sorted:
            if p.status != PoolStatus.ACTIVE or p.curve_tag != CURVE_TAG_CPMM:
                continue

            # Direct pool list
            if (asset_in == p.asset0 and asset_out == p.asset1) or (asset_in == p.asset1 and asset_out == p.asset0):
                direct.append(str(p.pool_id))
                r = _dir_reserves_cpmm(p, asset_in=asset_in, asset_out=asset_out)
                if r is not None:
                    dir_cache[(p.pool_id, asset_in, asset_out)] = (int(r[0]), int(r[1]), int(p.fee_bps))

            # First hop: asset_in -> mid
            mid: AssetId | None
            if asset_in == p.asset0:
                mid = p.asset1
            elif asset_in == p.asset1:
                mid = p.asset0
            else:
                mid = None
            if mid is not None and mid != asset_in and mid != asset_out:
                r = _dir_reserves_cpmm(p, asset_in=asset_in, asset_out=mid)
                if r is not None:
                    ins_by_mid.setdefault(mid, []).append(str(p.pool_id))
                    dir_cache[(p.pool_id, asset_in, mid)] = (int(r[0]), int(r[1]), int(p.fee_bps))

            # Second hop: mid2 -> asset_out  (pool contains asset_out and some mid2)
            mid2: AssetId | None
            if asset_out == p.asset0:
                mid2 = p.asset1
            elif asset_out == p.asset1:
                mid2 = p.asset0
            else:
                mid2 = None
            if mid2 is not None and mid2 != asset_in and mid2 != asset_out:
                r = _dir_reserves_cpmm(p, asset_in=mid2, asset_out=asset_out)
                if r is not None:
                    outs_by_mid.setdefault(mid2, []).append(str(p.pool_id))
                    dir_cache[(p.pool_id, mid2, asset_out)] = (int(r[0]), int(r[1]), int(p.fee_bps))

        # Deterministic ordering of pool-id lists.
        direct.sort()
        for ids in ins_by_mid.values():
            ids.sort()
        for ids in outs_by_mid.values():
            ids.sort()

        mids = tuple(sorted([m for m in ins_by_mid.keys() if m in outs_by_mid], key=str))

        by_mid: Dict[AssetId, _MidArrays] = {}
        for mid in mids:
            ins = tuple(ins_by_mid.get(mid, []))
            outs = tuple(outs_by_mid.get(mid, []))
            if not ins or not outs:
                continue

            r1_in = np.array([dir_cache[(pid, asset_in, mid)][0] for pid in ins], dtype=np.float64)
            r1_out = np.array([dir_cache[(pid, asset_in, mid)][1] for pid in ins], dtype=np.float64)
            # Store fee tiers as ints; ranking can upcast to float, but we sometimes need exact integer rounding.
            f1 = np.array([dir_cache[(pid, asset_in, mid)][2] for pid in ins], dtype=np.int64)

            r2_in = np.array([dir_cache[(pid, mid, asset_out)][0] for pid in outs], dtype=np.float64)
            r2_out = np.array([dir_cache[(pid, mid, asset_out)][1] for pid in outs], dtype=np.float64)
            f2 = np.array([dir_cache[(pid, mid, asset_out)][2] for pid in outs], dtype=np.int64)

            by_mid[mid] = _MidArrays(
                ins_ids=ins,
                outs_ids=outs,
                r1_in=r1_in,
                r1_out=r1_out,
                f1=f1,
                r2_in=r2_in,
                r2_out=r2_out,
                f2=f2,
            )

        prepared = _PreparedPair(
            snapshot_digest=str(snap),
            asset_in=str(asset_in),
            asset_out=str(asset_out),
            direct_pool_ids=tuple(direct),
            mids=mids,
            by_mid=by_mid,
        )

        with self._lock:
            self._pair_cache[key] = prepared
            self._pair_cache.move_to_end(key)
            while len(self._pair_cache) > self._max_cache_pairs:
                self._pair_cache.popitem(last=False)
        return prepared

    def quote_exact_in_2hop_fast_v1(
        self,
        *,
        pools_by_id: Dict[str, PoolState],
        asset_in: AssetId,
        asset_out: AssetId,
        amount_in: Amount,
        topk_max: int = 32,
        max_pairs_per_mid: int = MAX_PAIRS_PER_MID_DEFAULT,
        max_union_candidates: int = MAX_UNION_CANDIDATES_DEFAULT,
    ) -> Optional[RouteQuote]:
        """
        Fast (heuristic) best exact-in route up to 2 hops (CPMM only).

        Returns a RouteQuote with exact integer hop amounts, or None if no route exists.
        """
        D = int(amount_in)
        if D <= 0:
            return None
        if asset_in == asset_out:
            return None
        kmax = _strict_int_config(topk_max, name="topk_max")
        if kmax <= 0:
            kmax = 32
        if kmax > 4096:
            kmax = 4096
        max_pairs_mid = _strict_int_config(max_pairs_per_mid, name="max_pairs_per_mid")
        if max_pairs_mid <= 0:
            max_pairs_mid = int(MAX_PAIRS_PER_MID_DEFAULT)
        max_union = _strict_int_config(max_union_candidates, name="max_union_candidates")
        if max_union <= 0:
            max_union = int(MAX_UNION_CANDIDATES_DEFAULT)

        # Deterministic pool ordering.
        pools_sorted: Tuple[PoolState, ...] = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))

        try:
            import numpy as np
        except ImportError:
            return None

        prepared = self._get_or_build_prepared(pools_sorted=pools_sorted, asset_in=asset_in, asset_out=asset_out)

        # 1-hop direct best (CPMM only).
        best: Optional[RouteQuote] = None
        best_key: Optional[Tuple[int, int, str, str, str]] = None
        # Track feasible direct pools so we can also attempt split routing (parallel 1-hop pools).
        direct_pools: List[PoolState] = []
        direct_ranked: List[Tuple[int, PoolState]] = []

        for pid in prepared.direct_pool_ids:
            p = pools_by_id.get(pid)
            if p is None:
                continue
            out = _quote_exact_in_onehop(p, asset_in=asset_in, asset_out=asset_out, amount_in=int(D))
            if out is None:
                continue
            direct_pools.append(p)
            direct_ranked.append((int(out), p))
            hop = RouteHop(pid, asset_in, asset_out, int(D), int(out))
            q = RouteQuote(
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=int(D),
                amount_out=int(out),
                legs=(RouteLeg(hops=(hop,), amount_in=int(D), amount_out=int(out)),),
            )
            k = _quote_key(q)
            if best is None or q.amount_out > best.amount_out or (q.amount_out == best.amount_out and (best_key is None or k < best_key)):
                best = q
                best_key = k

        # 2-hop candidates via per-mid union selection.
        union: List[Tuple[float, Tuple[str, str, str], str, str, AssetId]] = []
        per_mid_t = int(kmax) + 1
        searched_pairs = 0

        for mid in prepared.mids:
            arr = prepared.by_mid.get(mid)
            if arr is None:
                continue
            ins_ids = arr.ins_ids
            outs_ids = arr.outs_ids
            m = int(len(ins_ids))
            n = int(len(outs_ids))
            if m <= 0 or n <= 0:
                continue
            pairs = int(m * n)
            if pairs > int(max_pairs_mid):
                # Fail-closed: refuse to allocate huge (m,n) matrices in fast mode.
                return None
            searched_pairs += int(pairs)

            amt = float(D)
            # Fee rounding mismatch is a real representation bug for tiny trades.
            # Kernel semantics (consensus-critical) use:
            #   fee_total = ceil(gross * fee_bps / 10_000)
            #   net_in = gross - fee_total
            #
            # For example, with amount_in=2 and any fee_bps>0, fee_total==1, net_in==1.
            # A continuous approximation would treat net_in ~= 2 and can drown fee=0 routes
            # at small topk_max. Use int64-exact rounding when it's safe, else fall back to
            # the continuous approximation (ranking-only).
            if int(D) <= int(SAFE_GROSS_FOR_INT64_FEE):
                gross_i = np.int64(int(D))
                fee_total = (gross_i * arr.f1 + np.int64(BPS_DENOM - 1)) // np.int64(BPS_DENOM)
                net1 = (gross_i - fee_total).astype(np.float64)
            else:
                net1 = amt * (float(BPS_DENOM) - arr.f1.astype(np.float64)) / float(BPS_DENOM)
            out1 = arr.r1_out * net1 / (arr.r1_in + net1)  # (m,)

            out1_mat = out1.reshape((m, 1))
            net2 = out1_mat * (float(BPS_DENOM) - arr.f2.reshape((1, n)).astype(np.float64)) / float(BPS_DENOM)
            approx2 = arr.r2_out.reshape((1, n)) * net2 / (arr.r2_in.reshape((1, n)) + net2)

            flat = approx2.reshape((m * n,))
            t = int(min(int(per_mid_t), int(m * n)))
            if t <= 0:
                continue
            if t < int(m * n):
                top = np.argpartition(-flat, kth=t - 1)[:t]
            else:
                top = np.arange(int(m * n), dtype=np.int64)

            # Deterministic order among these by (-approx, route_key).
            for flat_k in top.tolist():
                ii = int(flat_k) // int(n)
                jj = int(flat_k) % int(n)
                a = float(flat[int(flat_k)])
                p1_id = str(ins_ids[ii])
                p2_id = str(outs_ids[jj])
                rkey = (p1_id, p2_id, str(mid))
                union.append((a, rkey, p1_id, p2_id, mid))
                if len(union) > int(max_union):
                    # Fail-closed: avoid memory blowups on pathological markets.
                    return None

        # Evaluate a bounded number of 2-hop candidates exactly (no pruning in v1).
        if union:
            union.sort(key=lambda x: (-float(x[0]), x[1]))
            best2: Optional[RouteQuote] = None
            best2_key: Optional[Tuple[int, int, str, str, str]] = None
            for _a, rkey, p1_id, p2_id, mid in union[: int(kmax)]:
                p1 = pools_by_id.get(p1_id)
                p2 = pools_by_id.get(p2_id)
                if p1 is None or p2 is None:
                    continue
                quoted = _quote_exact_in_twohop(p1, p2, asset_in=asset_in, mid=mid, asset_out=asset_out, amount_in=int(D))
                if quoted is None:
                    continue
                out_mid, out_final = quoted
                hop1 = RouteHop(p1_id, asset_in, mid, int(D), int(out_mid))
                hop2 = RouteHop(p2_id, mid, asset_out, int(out_mid), int(out_final))
                q = RouteQuote(
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(D),
                    amount_out=int(out_final),
                    legs=(RouteLeg(hops=(hop1, hop2), amount_in=int(D), amount_out=int(out_final)),),
                )
                kq = _quote_key(q)
                if best2 is None or q.amount_out > best2.amount_out or (q.amount_out == best2.amount_out and (best2_key is None or kq < best2_key)):
                    best2 = q
                    best2_key = kq

            if best2 is not None:
                k2 = _quote_key(best2)
                if best is None or best2.amount_out > best.amount_out or (best2.amount_out == best.amount_out and (best_key is None or k2 < best_key)):
                    best = best2
                    best_key = k2

        # Direct split routing across parallel direct pools (1-hop legs).
        #
        # Important: split routing can be expensive for large D, so we gate it behind a
        # cheap multi-way probe. Only if the probe beats the current best (direct single / 2-hop)
        # do we attempt the heavier N-way split.
        if len(direct_ranked) >= 2 and best is not None and int(D) >= 10_000:
            direct_ranked.sort(key=lambda t: (-int(t[0]), t[1].pool_id))
            best_before_split = best
            best_before_key = best_key

            # Exact 2-pool split probe on the top-2 direct pools by single-pool output (fast, deterministic).
            split2_q: Optional[RouteQuote] = None
            if len(direct_ranked) >= 2:
                p0 = direct_ranked[0][1]
                p1 = direct_ranked[1][1]
                try:
                    split2 = best_split_two_pools_exact_in_for_pools(
                        p0,
                        p1,
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in_total=int(D),
                        search_profile="adaptive_v6",
                    )
                except ValueError:
                    split2 = None
                if split2 is not None and int(split2.amount_out_total) > 0 and int(split2.amount_in_0) > 0 and int(split2.amount_in_1) > 0:
                    leg0 = RouteLeg(
                        hops=(RouteHop(str(split2.pool0_id), asset_in, asset_out, int(split2.amount_in_0), int(split2.amount_out_0)),),
                        amount_in=int(split2.amount_in_0),
                        amount_out=int(split2.amount_out_0),
                    )
                    leg1 = RouteLeg(
                        hops=(RouteHop(str(split2.pool1_id), asset_in, asset_out, int(split2.amount_in_1), int(split2.amount_out_1)),),
                        amount_in=int(split2.amount_in_1),
                        amount_out=int(split2.amount_out_1),
                    )
                    split2_q = RouteQuote(
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in=int(D),
                        amount_out=int(split2.amount_out_total),
                        legs=(leg0, leg1),
                    )

            # Coarse N-way probe (cheap): does a multi-way split have a chance to beat the current best?
            probe_beats_best = False
            if len(direct_ranked) >= 3:
                Kprobe = min(16, len(direct_ranked))
                candidates_probe = [p for _out, p in direct_ranked[:Kprobe]]
                try:
                    split_probe = best_split_many_pools_exact_in_for_pools(
                        candidates_probe,
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in_total=int(D),
                        max_legs=4,
                        max_candidates=len(candidates_probe),
                        max_iters=256,
                    )
                except ValueError:
                    split_probe = None
                if split_probe is not None and int(split_probe.amount_out_total) > 0:
                    # Compare probe output to the pre-split best (key tie-break).
                    if int(split_probe.amount_out_total) > int(best_before_split.amount_out):
                        probe_beats_best = True

            # Update best with 2-pool exact split if it beats the pre-split best.
            if split2_q is not None:
                kq = _quote_key(split2_q)
                if split2_q.amount_out > best_before_split.amount_out or (
                    split2_q.amount_out == best_before_split.amount_out and (best_before_key is None or kq < best_before_key)
                ):
                    best = split2_q
                    best_key = kq

            # Heavier N-way split only if the coarse probe indicates multi-way splitting can beat the current best.
            if probe_beats_best:
                K = min(32, len(direct_ranked))
                candidates = [p for _out, p in direct_ranked[:K]]
                if len(candidates) >= 3:
                    try:
                        splitN = best_split_many_pools_exact_in_for_pools(
                            candidates,
                            asset_in=asset_in,
                            asset_out=asset_out,
                            amount_in_total=int(D),
                            max_legs=4,
                            max_candidates=len(candidates),
                            max_iters=4096,
                        )
                    except ValueError:
                        splitN = None
                    if splitN is not None and int(splitN.amount_out_total) > 0 and len(splitN.legs) >= 2:
                        legs: List[RouteLeg] = []
                        for leg in splitN.legs:
                            legs.append(
                                RouteLeg(
                                    hops=(RouteHop(str(leg.pool_id), asset_in, asset_out, int(leg.amount_in), int(leg.amount_out)),),
                                    amount_in=int(leg.amount_in),
                                    amount_out=int(leg.amount_out),
                                )
                            )
                        q = RouteQuote(
                            asset_in=asset_in,
                            asset_out=asset_out,
                            amount_in=int(D),
                            amount_out=int(splitN.amount_out_total),
                            legs=tuple(legs),
                        )
                        kq = _quote_key(q)
                        if q.amount_out > best.amount_out or (q.amount_out == best.amount_out and (best_key is None or kq < best_key)):
                            best = q
                            best_key = kq

        # If no direct route exists, a twohop might still exist; if none exists, return None.
        _ = searched_pairs  # kept for future debug plumbing
        return best

    def quote_exact_out_2hop_fast_v1(
        self,
        *,
        pools_by_id: Dict[str, PoolState],
        asset_in: AssetId,
        asset_out: AssetId,
        amount_out: Amount,
        topk_max: int = 32,
        apply_two_hop_gate: bool = False,
        max_pairs_per_mid: int = MAX_PAIRS_PER_MID_DEFAULT,
        max_union_candidates: int = MAX_UNION_CANDIDATES_DEFAULT,
    ) -> Optional[RouteQuote]:
        """
        Fast (heuristic) best exact-out route up to 2 hops (CPMM only).

        Returns a RouteQuote with exact integer hop amounts, or None if no route exists.
        """
        Q = int(amount_out)
        if Q <= 0:
            return None
        if asset_in == asset_out:
            return None
        kmax = _strict_int_config(topk_max, name="topk_max")
        if kmax <= 0:
            kmax = 32
        if kmax > 4096:
            kmax = 4096
        max_pairs_mid = _strict_int_config(max_pairs_per_mid, name="max_pairs_per_mid")
        if max_pairs_mid <= 0:
            max_pairs_mid = int(MAX_PAIRS_PER_MID_DEFAULT)
        max_union = _strict_int_config(max_union_candidates, name="max_union_candidates")
        if max_union <= 0:
            max_union = int(MAX_UNION_CANDIDATES_DEFAULT)

        # Deterministic pool ordering.
        pools_sorted: Tuple[PoolState, ...] = tuple(sorted(pools_by_id.values(), key=lambda p: p.pool_id))

        try:
            import numpy as np
        except ImportError:
            return None

        prepared = self._get_or_build_prepared(pools_sorted=pools_sorted, asset_in=asset_in, asset_out=asset_out)

        best: Optional[RouteQuote] = None
        best_key: Optional[Tuple[int, int, str, str, str]] = None

        # Direct pools list (for split) and best direct quote.
        direct_candidates: List[PoolState] = []
        best_direct: Optional[RouteQuote] = None
        best_direct_reserve_out: Optional[int] = None
        best_direct_fee_bps: Optional[int] = None

        for pid in prepared.direct_pool_ids:
            p = pools_by_id.get(pid)
            if p is None:
                continue
            direct_candidates.append(p)
            # Reserve_out for gate/split selection.
            r = _dir_reserves_cpmm(p, asset_in=asset_in, asset_out=asset_out)
            if r is None:
                continue
            rin, rout = r
            inn = _quote_exact_out_onehop(p, asset_in=asset_in, asset_out=asset_out, amount_out=int(Q))
            if inn is None:
                continue
            hop = RouteHop(pid, asset_in, asset_out, int(inn), int(Q))
            q = RouteQuote(
                asset_in=asset_in,
                asset_out=asset_out,
                amount_in=int(inn),
                amount_out=int(Q),
                legs=(RouteLeg(hops=(hop,), amount_in=int(inn), amount_out=int(Q)),),
            )
            k = _quote_key(q)
            if best is None or q.amount_in < best.amount_in or (q.amount_in == best.amount_in and (best_key is None or k < best_key)):
                best = q
                best_key = k
            if best_direct is None or q.amount_in < best_direct.amount_in or (
                q.amount_in == best_direct.amount_in and _quote_key(q) < _quote_key(best_direct)
            ):
                best_direct = q
                best_direct_reserve_out = int(rout)
                best_direct_fee_bps = int(p.fee_bps)

        # Direct split exact-out across parallel pools (2 legs, 1 hop each), matching core posture.
        if len(direct_candidates) >= 2:
            # Deterministic cap: keep only the top-8 by reserve_out (then pool_id) for this direction.
            if len(direct_candidates) > 8:

                def _direct_rout(p: PoolState) -> int:
                    r = _dir_reserves_cpmm(p, asset_in=asset_in, asset_out=asset_out)
                    return 0 if r is None else int(r[1])

                direct_candidates = sorted(direct_candidates, key=lambda p: (-_direct_rout(p), p.pool_id))[:8]
                direct_candidates.sort(key=lambda p: p.pool_id)

            for i in range(len(direct_candidates)):
                for j in range(i + 1, len(direct_candidates)):
                    p0 = direct_candidates[i]
                    p1 = direct_candidates[j]
                    try:
                        split = best_split_two_pools_exact_out_for_pools(
                            p0,
                            p1,
                            asset_in=asset_in,
                            asset_out=asset_out,
                            amount_out_total=int(Q),
                        )
                    except ValueError:
                        continue
                    if int(split.amount_in_total) <= 0:
                        continue
                    leg0 = RouteLeg(
                        hops=(RouteHop(str(split.pool0_id), asset_in, asset_out, int(split.amount_in_0), int(split.amount_out_0)),),
                        amount_in=int(split.amount_in_0),
                        amount_out=int(split.amount_out_0),
                    )
                    leg1 = RouteLeg(
                        hops=(RouteHop(str(split.pool1_id), asset_in, asset_out, int(split.amount_in_1), int(split.amount_out_1)),),
                        amount_in=int(split.amount_in_1),
                        amount_out=int(split.amount_out_1),
                    )
                    q = RouteQuote(
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in=int(split.amount_in_total),
                        amount_out=int(Q),
                        legs=(leg0, leg1),
                    )
                    k = _quote_key(q)
                    if best is None or q.amount_in < best.amount_in or (q.amount_in == best.amount_in and (best_key is None or k < best_key)):
                        best = q
                        best_key = k

        consider_two_hop = True
        if apply_two_hop_gate and best_direct is not None and best_direct_reserve_out is not None:
            consider_two_hop = should_consider_exact_out_two_hop(
                amount_out=int(Q),
                direct_reserve_out=int(best_direct_reserve_out),
                direct_amount_in=int(best_direct.amount_in),
                direct_fee_bps=int(best_direct_fee_bps or 0),
                config=None,
            )

        if not consider_two_hop:
            return best

        # Micro exact-out regime: if the 2-hop search space is small enough, enumerate all pairs
        # exactly (no float ranking) to avoid ceil-cascade misranking for tiny amount_out.
        if int(Q) <= int(EXACT_OUT_MICRO_AMOUNT_OUT_MAX):
            total_pairs = 0
            for mid in prepared.mids:
                arr = prepared.by_mid.get(mid)
                if arr is None:
                    continue
                m = int(len(arr.ins_ids))
                n = int(len(arr.outs_ids))
                if m <= 0 or n <= 0:
                    continue
                pairs = int(m * n)
                if pairs > int(max_pairs_mid):
                    return None
                total_pairs += int(pairs)
                if total_pairs > int(EXACT_OUT_MICRO_MAX_TOTAL_PAIRS):
                    break

            if total_pairs <= int(EXACT_OUT_MICRO_MAX_TOTAL_PAIRS):
                best2_amt_in: Optional[int] = None
                best2_mid_in: Optional[int] = None
                best2_p1_id: Optional[str] = None
                best2_p2_id: Optional[str] = None
                best2_mid: Optional[AssetId] = None
                best2_key: Optional[Tuple[int, int, str, str, str]] = None

                for mid in prepared.mids:
                    arr = prepared.by_mid.get(mid)
                    if arr is None:
                        continue
                    ins_ids = arr.ins_ids
                    outs_ids = arr.outs_ids
                    if not ins_ids or not outs_ids:
                        continue
                    for p1_id in ins_ids:
                        p1 = pools_by_id.get(str(p1_id))
                        if p1 is None:
                            continue
                        for p2_id in outs_ids:
                            p2 = pools_by_id.get(str(p2_id))
                            if p2 is None:
                                continue
                            quoted = _quote_exact_out_twohop(
                                p1,
                                p2,
                                asset_in=asset_in,
                                mid=mid,
                                asset_out=asset_out,
                                amount_out=int(Q),
                            )
                            if quoted is None:
                                continue
                            amt_in, mid_in_int = quoted
                            k = _quote_key_for(
                                hop_count=2,
                                pool_ids=(str(p1_id), str(p2_id)),
                                mid=str(mid),
                                asset_out=asset_out,
                            )
                            if best2_amt_in is None or int(amt_in) < int(best2_amt_in) or (
                                int(amt_in) == int(best2_amt_in) and (best2_key is None or k < best2_key)
                            ):
                                best2_amt_in = int(amt_in)
                                best2_mid_in = int(mid_in_int)
                                best2_p1_id = str(p1_id)
                                best2_p2_id = str(p2_id)
                                best2_mid = mid
                                best2_key = k

                if (
                    best2_amt_in is not None
                    and best2_mid_in is not None
                    and best2_p1_id is not None
                    and best2_p2_id is not None
                    and best2_mid is not None
                ):
                    mid_asset = str(best2_mid)
                    hop1 = RouteHop(best2_p1_id, asset_in, mid_asset, int(best2_amt_in), int(best2_mid_in))
                    hop2 = RouteHop(best2_p2_id, mid_asset, asset_out, int(best2_mid_in), int(Q))
                    q2 = RouteQuote(
                        asset_in=asset_in,
                        asset_out=asset_out,
                        amount_in=int(best2_amt_in),
                        amount_out=int(Q),
                        legs=(RouteLeg(hops=(hop1, hop2), amount_in=int(best2_amt_in), amount_out=int(Q)),),
                    )
                    k2 = best2_key or _quote_key(q2)
                    if best is None or q2.amount_in < best.amount_in or (
                        q2.amount_in == best.amount_in and (best_key is None or k2 < best_key)
                    ):
                        best = q2
                        best_key = k2

                return best

        # 2-hop candidates via per-mid union selection (float ranking + exact replay).
        union: List[Tuple[float, Tuple[str, str, str], str, str, AssetId]] = []
        per_mid_t = int(kmax) + 1
        searched_pairs = 0

        # Helpers: approximate CPMM exact-out input.
        bps = float(BPS_DENOM)
        qf = float(Q)

        for mid in prepared.mids:
            arr = prepared.by_mid.get(mid)
            if arr is None:
                continue
            ins_ids = arr.ins_ids
            outs_ids = arr.outs_ids
            m = int(len(ins_ids))
            n = int(len(outs_ids))
            if m <= 0 or n <= 0:
                continue
            pairs = int(m * n)
            if pairs > int(max_pairs_mid):
                return None
            searched_pairs += int(pairs)

            # Hop2: mid -> asset_out exact-out approx input (mid required).
            # net2 = rin2 * q / (rout2 - q)
            den2 = arr.r2_out - qf
            ok2 = den2 > 0.0
            fee2 = arr.f2.astype(np.float64)
            fee2_den = bps - fee2
            ok_fee2 = fee2_den > 0.0
            ok2 = ok2 & ok_fee2
            net2 = np.full_like(arr.r2_in, np.inf, dtype=np.float64)
            # Use np.divide(..., where=...) to avoid spurious divide-by-zero warnings.
            np.divide(arr.r2_in * qf, den2, out=net2, where=ok2)
            mid_in = np.full_like(net2, np.inf, dtype=np.float64)
            np.divide(net2 * bps, fee2_den, out=mid_in, where=ok2)  # (n,)

            mid_in_mat = mid_in.reshape((1, n))

            # Hop1: asset_in -> mid exact-out approx input for each needed mid_in.
            den1 = arr.r1_out.reshape((m, 1)) - mid_in_mat
            ok1 = den1 > 0.0
            fee1 = arr.f1.astype(np.float64).reshape((m, 1))
            fee1_den = bps - fee1
            ok_fee1 = fee1_den > 0.0
            ok1 = ok1 & ok_fee1 & np.isfinite(mid_in_mat)
            net1: Any = np.full((m, n), np.inf, dtype=np.float64)
            np.divide(arr.r1_in.reshape((m, 1)) * mid_in_mat, den1, out=net1, where=ok1)
            approx_in: Any = np.full((m, n), np.inf, dtype=np.float64)
            np.divide(net1 * bps, fee1_den, out=approx_in, where=ok1)  # (m,n)

            flat = approx_in.reshape((m * n,))
            finite_mask = np.isfinite(flat)
            if not bool(np.any(finite_mask)):
                continue

            t = int(min(int(per_mid_t), int(m * n)))
            if t <= 0:
                continue
            if t < int(m * n):
                top = np.argpartition(flat, kth=t - 1)[:t]  # smallest approx_in
            else:
                top = np.arange(int(m * n), dtype=np.int64)

            for flat_k in top.tolist():
                a = float(flat[int(flat_k)])
                if not (a >= 0.0) or not float(a) < float("inf"):
                    continue
                ii = int(flat_k) // int(n)
                jj = int(flat_k) % int(n)
                p1_id = str(ins_ids[ii])
                p2_id = str(outs_ids[jj])
                rkey = (p1_id, p2_id, str(mid))
                union.append((a, rkey, p1_id, p2_id, mid))
                if len(union) > int(max_union):
                    return None

        if union:
            union.sort(key=lambda x: (float(x[0]), x[1]))
            best2: Optional[RouteQuote] = None
            ranked_best2_key: Optional[Tuple[int, int, str, str, str]] = None
            for _a, _rkey, p1_id, p2_id, mid in union[: int(kmax)]:
                p1 = pools_by_id.get(p1_id)
                p2 = pools_by_id.get(p2_id)
                if p1 is None or p2 is None:
                    continue
                quoted = _quote_exact_out_twohop(p1, p2, asset_in=asset_in, mid=mid, asset_out=asset_out, amount_out=int(Q))
                if quoted is None:
                    continue
                amt_in, mid_in_int = quoted
                hop1 = RouteHop(p1_id, asset_in, mid, int(amt_in), int(mid_in_int))
                hop2 = RouteHop(p2_id, mid, asset_out, int(mid_in_int), int(Q))
                q = RouteQuote(
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_in=int(amt_in),
                    amount_out=int(Q),
                    legs=(RouteLeg(hops=(hop1, hop2), amount_in=int(amt_in), amount_out=int(Q)),),
                )
                kq = _quote_key(q)
                if best2 is None or q.amount_in < best2.amount_in or (
                    q.amount_in == best2.amount_in and (ranked_best2_key is None or kq < ranked_best2_key)
                ):
                    best2 = q
                    ranked_best2_key = kq

            if best2 is not None:
                k2 = _quote_key(best2)
                if best is None or best2.amount_in < best.amount_in or (
                    best2.amount_in == best.amount_in and (best_key is None or k2 < best_key)
                ):
                    best = best2
                    best_key = k2

        _ = searched_pairs
        return best
