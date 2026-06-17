"""
Many-pool exact-in split routing.

The dispatch layer supplies live reserve and quote functions. This module owns
candidate filtering, bounded exact allocation for small domains, deterministic
tie-breaks, the larger-domain greedy fallback, and quote materialization.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Callable, Optional, Sequence

from ..state.balances import AssetId
from ..state.pools import PoolState
from .split_routing_many_exact_in_small import best_small_domain_many_pool_exact_in
from .split_routing_types import SplitLegQuote, SplitManyPoolsQuote

ExactInReservesFor = Callable[[PoolState], tuple[int, int] | None]
ExactInQuoteFor = Callable[[PoolState, int], int]
_ExactInStepCandidate = tuple[str, int, int, int]  # pool_id, delta, increment, current_amount
_EXACT_SMALL_DOMAIN_MAX_AMOUNT_IN = 512


@dataclass(frozen=True)
class ManyPoolExactInRequest:
    pools: Sequence[PoolState]
    asset_in: AssetId
    asset_out: AssetId
    amount_in_total: int
    max_legs: int
    max_candidates: int
    max_iters: int
    reserves_for: ExactInReservesFor
    quote_exact_in: ExactInQuoteFor


@dataclass
class _ExactInManyPoolContext:
    pools_by_id: dict[str, PoolState]
    min_valid: dict[str, int]
    quote_exact_in: ExactInQuoteFor
    quote_cache: dict[tuple[str, int], int]

    def quote(self, pool_id: str, amount_in: int) -> int | None:
        if amount_in < 0:
            return None
        if amount_in == 0:
            return 0
        min_amount = self.min_valid.get(pool_id)
        if min_amount is None or int(amount_in) < int(min_amount):
            return None
        key = (pool_id, int(amount_in))
        if key in self.quote_cache:
            return self.quote_cache[key]
        out = self.quote_exact_in(self.pools_by_id[pool_id], int(amount_in))
        self.quote_cache[key] = int(out)
        return int(out)


def _require_positive_control(value: object, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def _validate_request(request: ManyPoolExactInRequest) -> None:
    _require_positive_control(request.amount_in_total, name="amount_in_total")
    _require_positive_control(request.max_legs, name="max_legs")
    _require_positive_control(request.max_candidates, name="max_candidates")
    _require_positive_control(request.max_iters, name="max_iters")


def _quote_is_valid(request: ManyPoolExactInRequest, pool: PoolState, amount_in: int) -> bool:
    if amount_in <= 0:
        return False
    try:
        request.quote_exact_in(pool, int(amount_in))
    except ValueError:
        return False
    return True


def _feasible_exact_in_pools(request: ManyPoolExactInRequest) -> list[PoolState]:
    feasible: list[PoolState] = []
    for pool in request.pools:
        if pool.status.value != "ACTIVE":
            continue
        if request.reserves_for(pool) is None:
            continue
        if not _quote_is_valid(request, pool, int(request.amount_in_total)):
            continue
        feasible.append(pool)
    return feasible


def _rank_exact_in_candidate_pools(
    request: ManyPoolExactInRequest,
    feasible: Sequence[PoolState],
) -> list[PoolState]:
    ranked: list[tuple[int, PoolState]] = []
    for pool in feasible:
        try:
            out_full = request.quote_exact_in(pool, int(request.amount_in_total))
        except ValueError:
            continue
        ranked.append((int(out_full), pool))
    ranked.sort(key=lambda item: (-int(item[0]), item[1].pool_id))
    candidates = [pool for _out, pool in ranked[: min(int(request.max_candidates), len(ranked))]]
    candidates.sort(key=lambda pool: pool.pool_id)
    return candidates


def _min_valid_amount(request: ManyPoolExactInRequest, pool: PoolState) -> int | None:
    if not _quote_is_valid(request, pool, int(request.amount_in_total)):
        return None
    lo = 1
    hi = int(request.amount_in_total)
    while lo < hi:
        mid = (lo + hi) // 2
        if _quote_is_valid(request, pool, int(mid)):
            hi = mid
        else:
            lo = mid + 1
    return int(lo)


def _min_valid_exact_in_by_pool(
    request: ManyPoolExactInRequest,
    candidates: Sequence[PoolState],
) -> dict[str, int]:
    min_valid: dict[str, int] = {}
    for pool in candidates:
        amount = _min_valid_amount(request, pool)
        if amount is not None:
            min_valid[pool.pool_id] = int(amount)
    return min_valid


def _build_context(request: ManyPoolExactInRequest) -> _ExactInManyPoolContext:
    feasible = _feasible_exact_in_pools(request)
    if not feasible:
        raise ValueError("no feasible pools for split")

    candidates = _rank_exact_in_candidate_pools(request, feasible)
    if not candidates:
        raise ValueError("no feasible pools for split")

    min_valid = _min_valid_exact_in_by_pool(request, candidates)
    if not min_valid:
        raise ValueError("no feasible pools for split")

    return _ExactInManyPoolContext(
        pools_by_id={pool.pool_id: pool for pool in candidates if pool.pool_id in min_valid},
        min_valid=min_valid,
        quote_exact_in=request.quote_exact_in,
        quote_cache={},
    )


def _seed_allocation(
    *,
    context: _ExactInManyPoolContext,
    amount_in_total: int,
    max_legs: int,
) -> tuple[dict[str, int], set[str], int]:
    alloc: dict[str, int] = {pool_id: 0 for pool_id in context.pools_by_id.keys()}
    used: set[str] = set()
    remaining = int(amount_in_total)
    seed_order = sorted(
        context.pools_by_id.keys(),
        key=lambda pool_id: (-int(context.quote(pool_id, int(amount_in_total)) or 0), pool_id),
    )

    for pool_id in seed_order:
        if remaining <= 0:
            break
        if len(used) >= int(max_legs):
            break
        min_amount = int(context.min_valid[pool_id])
        if min_amount <= 0 or min_amount > remaining:
            continue
        alloc[pool_id] = min_amount
        remaining -= min_amount
        used.add(pool_id)

    if not used:
        pool_id = seed_order[0]
        min_amount = int(context.min_valid[pool_id])
        increment = min_amount if min_amount <= remaining else remaining
        if increment <= 0:
            raise ValueError("no feasible allocation")
        alloc[pool_id] = increment
        remaining -= increment
        used.add(pool_id)

    return alloc, used, int(remaining)


def _candidate_increment(
    pool_id: str,
    *,
    context: _ExactInManyPoolContext,
    alloc: dict[str, int],
    used: set[str],
    remaining: int,
    base_increment: int,
    max_legs: int,
) -> Optional[_ExactInStepCandidate]:
    current = int(alloc.get(pool_id, 0))
    if current == 0 and pool_id not in used and len(used) >= int(max_legs):
        return None

    increment = int(base_increment)
    if current == 0:
        min_amount = int(context.min_valid[pool_id])
        if min_amount > increment:
            increment = min_amount
    if increment <= 0 or increment > int(remaining):
        return None

    out_before = context.quote(pool_id, current) or 0
    out_after = context.quote(pool_id, current + increment)
    if out_after is None:
        return None
    delta = int(out_after - out_before)
    if delta < 0:
        return None
    return (pool_id, int(delta), int(increment), int(current))


def _is_better_increment(
    candidate: _ExactInStepCandidate,
    best: Optional[_ExactInStepCandidate],
) -> bool:
    if best is None:
        return True

    pool_id, delta, increment, current = candidate
    best_pool_id, best_delta, best_increment, best_current = best
    lhs = int(delta) * int(best_increment)
    rhs = int(best_delta) * int(increment)
    if lhs != rhs:
        return lhs > rhs
    if delta != best_delta:
        return delta > best_delta
    if current != best_current:
        return current < best_current
    return pool_id < best_pool_id


def _choose_increment(
    *,
    context: _ExactInManyPoolContext,
    alloc: dict[str, int],
    used: set[str],
    remaining: int,
    base_increment: int,
    max_legs: int,
) -> _ExactInStepCandidate:
    best: Optional[_ExactInStepCandidate] = None
    for pool_id in context.pools_by_id.keys():
        candidate = _candidate_increment(
            pool_id,
            context=context,
            alloc=alloc,
            used=used,
            remaining=int(remaining),
            base_increment=int(base_increment),
            max_legs=int(max_legs),
        )
        if candidate is not None and _is_better_increment(candidate, best):
            best = candidate
    if best is None:
        raise ValueError("no feasible allocation step (unexpected)")
    return best


def _greedy_allocate(
    step: int,
    *,
    context: _ExactInManyPoolContext,
    amount_in_total: int,
    max_legs: int,
) -> dict[str, int]:
    if step <= 0:
        raise ValueError("step must be positive")

    alloc, used, remaining = _seed_allocation(
        context=context,
        amount_in_total=int(amount_in_total),
        max_legs=int(max_legs),
    )

    while remaining > 0:
        base_increment = min(int(step), int(remaining))
        pool_id, _delta, increment, _current = _choose_increment(
            context=context,
            alloc=alloc,
            used=used,
            remaining=int(remaining),
            base_increment=int(base_increment),
            max_legs=int(max_legs),
        )
        was_zero = alloc[pool_id] == 0
        alloc[pool_id] = int(alloc[pool_id] + increment)
        remaining -= int(increment)
        if was_zero:
            used.add(pool_id)

    return alloc


def _score_allocation(alloc: dict[str, int], *, context: _ExactInManyPoolContext) -> int:
    total_out = 0
    for pool_id, amount in alloc.items():
        if amount <= 0:
            continue
        out_amount = context.quote(pool_id, int(amount))
        if out_amount is None:
            continue
        total_out += int(out_amount)
    return int(total_out)


def _positive_legs(alloc: dict[str, int]) -> list[tuple[str, int]]:
    return sorted([(pool_id, int(amount)) for pool_id, amount in alloc.items() if int(amount) > 0], key=lambda item: item[0])


def _is_better_allocation(
    *,
    total_out: int,
    alloc: dict[str, int],
    best_out: int,
    best_alloc: Optional[dict[str, int]],
) -> bool:
    if total_out > best_out:
        return True
    if total_out != best_out or best_alloc is None:
        return False
    current_legs = _positive_legs(alloc)
    best_legs = _positive_legs(best_alloc)
    return len(current_legs) < len(best_legs) or (len(current_legs) == len(best_legs) and current_legs < best_legs)


def _exact_small_domain_allocation(
    *,
    context: _ExactInManyPoolContext,
    amount_in_total: int,
    max_legs: int,
) -> dict[str, int]:
    def quote_for_pool_id(pool_id: str, amount_in: int) -> int | None:
        try:
            return context.quote(pool_id, int(amount_in))
        except ValueError:
            return None

    return best_small_domain_many_pool_exact_in(
        pool_ids=sorted(context.pools_by_id.keys()),
        amount_in_total=int(amount_in_total),
        max_legs=int(max_legs),
        quote_for_pool_id=quote_for_pool_id,
    )


def _search_best_allocation(
    *,
    context: _ExactInManyPoolContext,
    amount_in_total: int,
    max_legs: int,
    max_iters: int,
) -> dict[str, int]:
    amount_total = int(amount_in_total)
    if amount_total <= min(int(max_iters), _EXACT_SMALL_DOMAIN_MAX_AMOUNT_IN):
        return _exact_small_domain_allocation(
            context=context,
            amount_in_total=amount_total,
            max_legs=int(max_legs),
        )

    step_min = max(1, amount_total // int(max_iters))
    step = max(step_min, max(1, amount_total // 256))
    best_alloc: Optional[dict[str, int]] = None
    best_out = -1

    while True:
        alloc = _greedy_allocate(
            int(step),
            context=context,
            amount_in_total=int(amount_in_total),
            max_legs=int(max_legs),
        )
        total_out = _score_allocation(alloc, context=context)
        if _is_better_allocation(
            total_out=int(total_out),
            alloc=alloc,
            best_out=int(best_out),
            best_alloc=best_alloc,
        ):
            best_out = int(total_out)
            best_alloc = alloc

        if step <= step_min:
            break
        step = max(step_min, step // 2)

    if best_alloc is None:
        raise RuntimeError("split allocation search produced no candidate")
    return best_alloc


def _build_quote(
    *,
    best_alloc: dict[str, int],
    amount_in_total: int,
    context: _ExactInManyPoolContext,
) -> SplitManyPoolsQuote:
    legs: list[SplitLegQuote] = []
    out_total = 0
    in_total = 0
    for pool_id in sorted(best_alloc.keys()):
        amount = int(best_alloc[pool_id])
        if amount <= 0:
            continue
        out_amount = context.quote(pool_id, amount)
        if out_amount is None:
            continue
        legs.append(SplitLegQuote(pool_id=pool_id, amount_in=int(amount), amount_out=int(out_amount)))
        in_total += int(amount)
        out_total += int(out_amount)

    if in_total != int(amount_in_total):
        raise ValueError("split allocation did not consume full input (unexpected)")

    return SplitManyPoolsQuote(amount_in_total=int(amount_in_total), amount_out_total=int(out_total), legs=tuple(legs))


def best_many_pool_exact_in_split(request: ManyPoolExactInRequest) -> SplitManyPoolsQuote:
    _validate_request(request)
    context = _build_context(request)
    best_alloc = _search_best_allocation(
        context=context,
        amount_in_total=int(request.amount_in_total),
        max_legs=int(request.max_legs),
        max_iters=int(request.max_iters),
    )
    return _build_quote(best_alloc=best_alloc, amount_in_total=int(request.amount_in_total), context=context)
