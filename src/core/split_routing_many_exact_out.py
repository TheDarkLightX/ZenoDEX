"""
Many-pool exact-out split routing over a bounded canonical domain.

This module owns candidate selection, capacity checks, bounded-domain
enumeration, and canonical quote materialization. The dispatch layer supplies
the live reserve and exact-out quote functions.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Sequence

from ..kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    DEFAULT_EXACT_OUT_MANY_POOL_MAX_ENUMERATED_CANDIDATES,
)
from ..kernels.python.exact_out_many_pool_canonical_domain_v1 import (
    build_exact_out_many_pool_selected_domain as _kernel_build_exact_out_many_pool_selected_domain,
)
from ..kernels.python.exact_out_many_pool_repaired_prefilter_v1 import (
    select_many_pool_repaired_prefilter_candidates as _kernel_select_many_pool_repaired_prefilter_candidates,
)
from ..state.balances import Amount, AssetId
from ..state.pools import PoolState
from .split_routing_types import (
    ExactOutCapacityGuard,
    SplitLegExactOutQuote,
    SplitManyPoolsExactOutQuote,
)

ExactOutReservesFor = Callable[[PoolState], tuple[int, int] | None]
ExactOutQuoteFor = Callable[[PoolState, int], int]


@dataclass(frozen=True)
class ManyPoolExactOutRequest:
    pools: Sequence[PoolState]
    asset_in: AssetId
    asset_out: AssetId
    amount_out_total: int
    max_legs: int
    max_candidates: int
    max_iters: int
    window: int
    brute_force_max: int
    max_full_domain_pools: int
    reserves_for: ExactOutReservesFor
    quote_exact_out: ExactOutQuoteFor

    @property
    def max_enumerated_candidates(self) -> int:
        return max(
            int(DEFAULT_EXACT_OUT_MANY_POOL_MAX_ENUMERATED_CANDIDATES),
            int(self.max_iters) * max(1, int(self.max_legs)),
        )


def build_exact_out_capacity_guard_from_caps(
    caps_by_pool: Sequence[tuple[str, int]],
    *,
    amount_out_total: Amount,
    max_legs: int,
) -> ExactOutCapacityGuard:
    ranked_caps = sorted(
        ((str(pool_id), int(cap)) for pool_id, cap in caps_by_pool if int(cap) > 0),
        key=lambda item: (-int(item[1]), item[0]),
    )
    top_caps = tuple(ranked_caps[: min(int(max_legs), len(ranked_caps))])
    capacity_upper_bound = sum(int(cap) for _pool_id, cap in top_caps)
    return ExactOutCapacityGuard(
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        top_caps=top_caps,
        capacity_upper_bound=int(capacity_upper_bound),
    )


def _validate_request(request: ManyPoolExactOutRequest) -> None:
    if request.amount_out_total <= 0:
        raise ValueError("amount_out_total must be positive")
    if request.max_legs <= 0:
        raise ValueError("max_legs must be positive")
    if request.max_candidates <= 0:
        raise ValueError("max_candidates must be positive")
    if request.max_iters <= 0:
        raise ValueError("max_iters must be positive")
    if request.window < 0:
        raise ValueError("window must be non-negative")
    if request.brute_force_max < 0:
        raise ValueError("brute_force_max must be non-negative")
    if request.max_full_domain_pools <= 0:
        raise ValueError("max_full_domain_pools must be positive")


def _feasible_exact_out_pools(request: ManyPoolExactOutRequest) -> list[tuple[PoolState, int, int]]:
    feasible: list[tuple[PoolState, int, int]] = []
    for pool in request.pools:
        if pool.status.value != "ACTIVE":
            continue
        reserves = request.reserves_for(pool)
        if reserves is None:
            continue
        _reserve_in, reserve_out = reserves
        cap = int(reserve_out) - 1
        if cap <= 0:
            continue
        target_out = min(int(request.amount_out_total), int(cap))
        try:
            amount_in = request.quote_exact_out(pool, int(target_out))
        except ValueError:
            continue
        feasible.append((pool, int(cap), int(amount_in)))
    return feasible


def _repaired_prefilter_candidates(
    request: ManyPoolExactOutRequest,
    feasible_pools: Sequence[PoolState],
) -> list[PoolState]:
    if len(feasible_pools) > int(request.max_full_domain_pools):
        return []
    try:
        return list(
            _kernel_select_many_pool_repaired_prefilter_candidates(
                tuple(feasible_pools),
                asset_in=str(request.asset_in),
                asset_out=str(request.asset_out),
                amount_out_total=int(request.amount_out_total),
                max_legs=int(request.max_legs),
                max_candidate_pools=int(request.max_candidates),
                max_full_domain_pools=int(request.max_full_domain_pools),
                max_enumerated_candidates=int(request.max_enumerated_candidates),
            )
        )
    except ValueError:
        return []


def _fallback_ranked_candidates(
    request: ManyPoolExactOutRequest,
    feasible: Sequence[tuple[PoolState, int, int]],
) -> list[PoolState]:
    ranked: list[tuple[int, int, PoolState, int]] = []
    for pool, cap, amount_in in feasible:
        target_out = min(int(request.amount_out_total), int(cap))
        scaled_cost = (int(amount_in) * 1_000_000) // max(1, int(target_out))
        ranked.append((int(scaled_cost), int(amount_in), pool, int(cap)))
    ranked.sort(key=lambda item: (item[0], item[1], item[2].pool_id))
    return _bounded_capacity_candidate_prefix(request, ranked)


def _bounded_capacity_candidate_prefix(
    request: ManyPoolExactOutRequest,
    ranked: Sequence[tuple[int, int, PoolState, int]],
) -> list[PoolState]:
    candidates: list[PoolState] = []
    caps: dict[str, int] = {}
    for _scaled_cost, _amount_in, pool, cap in ranked:
        if pool.pool_id in caps:
            continue
        candidates.append(pool)
        caps[pool.pool_id] = int(cap)
        if len(candidates) >= int(request.max_candidates):
            break
        top_caps = sorted(caps.values(), reverse=True)
        covered = sum(top_caps[: min(int(request.max_legs), len(top_caps))])
        enough_legs_seen = len(candidates) >= min(int(request.max_legs), len(ranked))
        if covered >= int(request.amount_out_total) and enough_legs_seen:
            break
    return candidates


def _select_exact_out_candidates(
    request: ManyPoolExactOutRequest,
    feasible: Sequence[tuple[PoolState, int, int]],
) -> list[PoolState]:
    feasible_pools = tuple(pool for pool, _cap, _amount_in in feasible)
    candidates = _repaired_prefilter_candidates(request, feasible_pools)
    if not candidates:
        candidates = _fallback_ranked_candidates(request, feasible)
    candidates.sort(key=lambda pool: pool.pool_id)
    return candidates


def _selected_domain_quote(
    request: ManyPoolExactOutRequest,
    candidates: Sequence[PoolState],
) -> SplitManyPoolsExactOutQuote:
    selected_domain = _kernel_build_exact_out_many_pool_selected_domain(
        tuple(candidates),
        asset_in=request.asset_in,
        asset_out=request.asset_out,
        amount_out_total=int(request.amount_out_total),
        max_legs=int(request.max_legs),
        max_enumerated_candidates=int(request.max_enumerated_candidates),
    )
    return SplitManyPoolsExactOutQuote(
        amount_out_total=int(selected_domain.canonical_quote.amount_out_total),
        amount_in_total=int(selected_domain.canonical_quote.amount_in_total),
        legs=tuple(
            SplitLegExactOutQuote(
                pool_id=leg.pool_id,
                amount_out=int(leg.amount_out),
                amount_in=int(leg.amount_in),
            )
            for leg in selected_domain.canonical_quote.legs
        ),
    )


def best_many_pool_exact_out_split(request: ManyPoolExactOutRequest) -> SplitManyPoolsExactOutQuote:
    _validate_request(request)
    feasible = _feasible_exact_out_pools(request)
    if not feasible:
        raise ValueError("no feasible pools for exact-out split")

    capacity_guard = build_exact_out_capacity_guard_from_caps(
        tuple((pool.pool_id, int(cap)) for pool, cap, _amount_in in feasible),
        amount_out_total=int(request.amount_out_total),
        max_legs=int(request.max_legs),
    )
    if not capacity_guard.feasible:
        raise ValueError(
            "no feasible split under max_legs constraint: "
            f"requested={request.amount_out_total} "
            f"capacity_upper_bound={capacity_guard.capacity_upper_bound} "
            f"max_legs={request.max_legs}"
        )

    candidates = _select_exact_out_candidates(request, feasible)
    if not candidates:
        raise ValueError("no feasible candidates for exact-out split")
    return _selected_domain_quote(request, candidates)
