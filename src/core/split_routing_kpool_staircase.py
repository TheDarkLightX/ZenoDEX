"""
k-pool staircase exact-in split routing.

Generalizes the two-pool staircase optimizer to k parallel CPMM pools. The key
theorem: in any optimal allocation, at most one pool is "interior" (strictly
inside a plateau of its own output staircase). All other positive pools sit at
a jump-point left edge of their own staircase.

This module is parameterized by the quote function to stay free of runtime
dependencies. It is an experimental prototype; promotion to the live route
selector requires parity, performance, and formal evidence.

Algorithm (single-DP with prefix/suffix combination):

  1. Enumerate jump-point left edges B_i for each pool i (O(Σ B_i * Q) quotes).
  2. Run ONE forward DP over all pools (in canonical pool_id order), folding
     each pool's jump-point candidates. This produces a prefix DP table after
     each pool. We also store the suffix DP table after each pool by running
     a backward DP.
  3. Case "no interior": check the full DP for states that spend exactly D.
  4. Case "interior pool j": combine prefix[j-1] and suffix[j+1] by spent value,
     then probe the residual r = D - spent_prefix - spent_suffix for pool j.
     This is O(S_prefix * S_suffix) per interior pool, but in practice the
     spent-indexed tables are small when breakpoints are sparse.

When breakpoints are dense (B_i ≈ D), the jump-point candidate sets are as large
as the full [1, D] range, so the DP degrades to the existing O(k * D^2) small-
domain DP cost. In that regime we fall back to the existing exact DP to avoid
the overhead of jump enumeration + prefix/suffix combination.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from typing import Callable, Protocol, Sequence

from .domain_limits import is_strict_int

BPS_DENOM = 10_000

# When the total jump-point count across all pools exceeds this fraction of
# k * D, the jump-point DP loses its sparsity advantage and we fall back to the
# existing exact small-domain DP (which folds all amounts [1..D] per pool).
# The threshold is conservative: jump points must be at least 4x sparser than
# the full range for the staircase DP to be worth running.
_DENSE_BREAKPOINT_FALLBACK_RATIO = 4


class _PoolLike(Protocol):
    x: int
    y: int
    fee_bps: int


_QuoteExactIn = Callable[[_PoolLike, int], int]
_PoolId = str
# State: (total_output, legs) where legs is a sorted tuple of (pool_id, amount).
_State = tuple[int, tuple[tuple[_PoolId, int], ...]]
# DP table keyed by (legs_used, spent) -> best state.
_DPTable = dict[tuple[int, int], _State]


@dataclass(frozen=True)
class _PoolSpec:
    pool_id: _PoolId
    pool: _PoolLike
    min_valid: int


@dataclass(frozen=True)
class _KPoolStaircaseRequest:
    pools: Sequence[_PoolSpec]
    amount_in_total: int
    max_legs: int
    quote_exact_in: _QuoteExactIn


@dataclass
class _KPoolStaircaseContext:
    request: _KPoolStaircaseRequest
    # pool_id -> sorted list of (gross_in, output) jump points reachable by D.
    jump_points: dict[_PoolId, list[tuple[int, int]]] = field(default_factory=dict)
    # pool_id -> quote cache.
    quote_cache: dict[tuple[_PoolId, int], int | None] = field(default_factory=dict)
    # pool_id -> True if the pool has a valid quote at amount_in_total.
    feasible_at_full: dict[_PoolId, bool] = field(default_factory=dict)

    def quote(self, pool_id: _PoolId, amount: int) -> int | None:
        if amount < 0:
            return None
        if amount == 0:
            return 0
        key = (pool_id, int(amount))
        if key in self.quote_cache:
            return self.quote_cache[key]
        pool = next(p for p in self.request.pools if p.pool_id == pool_id)
        try:
            out = self.request.quote_exact_in(pool.pool, int(amount))
        except ValueError:
            self.quote_cache[key] = None
            return None
        self.quote_cache[key] = int(out)
        return int(out)


def _require_positive_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) <= 0:
        raise ValueError(f"{name} must be positive")
    return int(value)


def _require_nonnegative_control(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def _ceil_div_positive(numerator: int, denominator: int) -> int:
    if denominator <= 0:
        raise ValueError("denominator must be positive")
    return (int(numerator) + int(denominator) - 1) // int(denominator)


def _is_better_state(candidate: _State, incumbent: _State | None) -> bool:
    if incumbent is None:
        return True
    candidate_out, candidate_legs = candidate
    incumbent_out, incumbent_legs = incumbent
    if candidate_out != incumbent_out:
        return candidate_out > incumbent_out
    if len(candidate_legs) != len(incumbent_legs):
        return len(candidate_legs) < len(incumbent_legs)
    return candidate_legs < incumbent_legs


def _is_better_final(
    *,
    candidate_out: int,
    candidate_legs: tuple[tuple[_PoolId, int], ...],
    best_out: int,
    best_legs: tuple[tuple[_PoolId, int], ...] | None,
) -> bool:
    if candidate_out != best_out:
        return candidate_out > best_out
    if best_legs is None:
        return True
    if len(candidate_legs) != len(best_legs):
        return len(candidate_legs) < len(best_legs)
    return candidate_legs < best_legs


def _min_gross_in_for_output_level(pool: _PoolLike, output_level: int) -> int | None:
    alpha = int(BPS_DENOM) - int(pool.fee_bps)
    target = int(output_level)
    if int(pool.x) <= 0 or int(pool.y) <= 0:
        return None
    if alpha <= 0 or target <= 0 or target >= int(pool.y):
        return None
    min_net = _ceil_div_positive(target * int(pool.x), int(pool.y) - target)
    return _ceil_div_positive(min_net * int(BPS_DENOM), alpha)


def _pool_jump_points(
    pool: _PoolLike,
    amount_in_total: int,
    *,
    quote_exact_in: _QuoteExactIn,
) -> list[tuple[int, int]]:
    """Enumerate (gross_in, output) jump-point left edges reachable by D.

    Complexity is O(B) quotes where B is the number of distinct positive input
    breakpoints. B is at most amount_in_total, and can be much smaller when
    reserves are skewed.
    """
    candidates: list[tuple[int, int]] = []
    next_output_level = 1
    while True:
        gross_in = _min_gross_in_for_output_level(pool, next_output_level)
        if gross_in is not None and gross_in <= int(amount_in_total):
            try:
                reached_output = quote_exact_in(pool, int(gross_in))
            except ValueError:
                break
            if int(reached_output) < int(next_output_level):
                break
            candidates.append((int(gross_in), int(reached_output)))
            next_output_level = int(reached_output) + 1
            continue
        return candidates


def _pool_jump_points_bounded(
    pool: _PoolLike,
    amount_in_total: int,
    *,
    quote_exact_in: _QuoteExactIn,
    max_breakpoints: int,
) -> list[tuple[int, int]] | None:
    """Enumerate jump points with an early-exit breakpoint cap.

    Returns None if the breakpoint count exceeds max_breakpoints before
    enumeration completes. This lets the adaptive entry point bail out of
    dense-breakpoint regimes without paying the full enumeration cost.
    """
    candidates: list[tuple[int, int]] = []
    next_output_level = 1
    while True:
        gross_in = _min_gross_in_for_output_level(pool, next_output_level)
        if gross_in is not None and gross_in <= int(amount_in_total):
            try:
                reached_output = quote_exact_in(pool, int(gross_in))
            except ValueError:
                break
            if int(reached_output) < int(next_output_level):
                break
            candidates.append((int(gross_in), int(reached_output)))
            if len(candidates) > int(max_breakpoints):
                return None
            next_output_level = int(reached_output) + 1
            continue
        return candidates


def _estimate_breakpoint_sparsity(
    pool: _PoolLike,
    amount_in_total: int,
) -> float:
    """Cheap analytical estimate of breakpoint density (no quotes).

    Returns the estimated fraction of [1..D] that are jump points. A value near
    1.0 means dense (every integer is a breakpoint); near 0.0 means sparse.

    For CPMM with output floor(y*net/(x+net)), the output increases by 1 each
    time net crosses roughly (x+net)^2/(y) in marginal input. The number of
    breakpoints is approximately min(y, D * y / (x + D*alpha)) where alpha is
    the fee-adjusted fraction. When x is large relative to D, breakpoints are
    sparse; when x is small, they are dense.

    This is a heuristic for the adaptive fallback decision only; the exact
    decision uses bounded enumeration.
    """
    alpha = int(BPS_DENOM) - int(pool.fee_bps)
    if alpha <= 0 or int(pool.x) <= 0 or int(pool.y) <= 0:
        return 1.0
    # Approximate number of output levels reachable: y * net_max / (x + net_max)
    # where net_max = D * alpha / BPS.
    net_max = (int(amount_in_total) * alpha) // int(BPS_DENOM)
    if net_max <= 0:
        return 0.0
    est_output_levels = (int(pool.y) * net_max) // (int(pool.x) + net_max)
    est_breakpoints = min(int(est_output_levels), int(amount_in_total))
    if int(amount_in_total) <= 0:
        return 1.0
    return float(est_breakpoints) / float(int(amount_in_total))


def _build_jump_points(request: _KPoolStaircaseRequest) -> dict[_PoolId, list[tuple[int, int]]]:
    points: dict[_PoolId, list[tuple[int, int]]] = {}
    for spec in request.pools:
        pts = _pool_jump_points(
            spec.pool,
            int(request.amount_in_total),
            quote_exact_in=request.quote_exact_in,
        )
        points[spec.pool_id] = pts
    return points


def _dp_fold_pool(
    *,
    states: _DPTable,
    pool_id: _PoolId,
    candidate_amounts: list[int],
    quote_fn: Callable[[_PoolId, int], int | None],
    amount_total: int,
    max_legs: int,
) -> _DPTable:
    """Fold one pool's candidate amounts into the DP table.

    Each candidate amount is a jump-point left edge. State key is (legs_used,
    spent); value is the best (output, legs) for that key. This is the same
    shape as best_small_domain_many_pool_exact_in but with per-pool candidate
    sets restricted to jump points instead of [1, D].
    """
    next_states: _DPTable = dict(states)
    for (used_legs, spent), (total_out, legs) in states.items():
        if used_legs >= int(max_legs):
            continue
        for amount in candidate_amounts:
            if amount <= 0:
                continue
            new_spent = int(spent) + int(amount)
            if new_spent > int(amount_total):
                continue
            out_amount = quote_fn(pool_id, int(amount))
            if out_amount is None:
                continue
            key = (int(used_legs) + 1, int(new_spent))
            candidate: _State = (
                int(total_out) + int(out_amount),
                tuple(sorted((*legs, (pool_id, int(amount))))),
            )
            if _is_better_state(candidate, next_states.get(key)):
                next_states[key] = candidate
    return next_states


def _dp_fold_pool_with_outputs(
    *,
    states: _DPTable,
    pool_id: _PoolId,
    candidates: list[tuple[int, int]],
    amount_total: int,
    max_legs: int,
) -> _DPTable:
    """Fold one pool's jump points (with pre-computed outputs) into the DP.

    This avoids re-quoting jump points whose outputs were already computed during
    enumeration. The `candidates` list contains (amount, output) pairs from
    _pool_jump_points.
    """
    next_states: _DPTable = dict(states)
    for (used_legs, spent), (total_out, legs) in states.items():
        if used_legs >= int(max_legs):
            continue
        for amount, out_amount in candidates:
            if amount <= 0:
                continue
            new_spent = int(spent) + int(amount)
            if new_spent > int(amount_total):
                continue
            key = (int(used_legs) + 1, int(new_spent))
            candidate: _State = (
                int(total_out) + int(out_amount),
                tuple(sorted((*legs, (pool_id, int(amount))))),
            )
            if _is_better_state(candidate, next_states.get(key)):
                next_states[key] = candidate
    return next_states


def _best_exact_full_from_dp(
    *,
    states: _DPTable,
    amount_total: int,
    max_legs: int,
) -> _State | None:
    """Extract the best state that spends exactly amount_total."""
    best_out = -1
    best_legs: tuple[tuple[_PoolId, int], ...] | None = None
    for used_legs in range(1, int(max_legs) + 1):
        state = states.get((used_legs, int(amount_total)))
        if state is None:
            continue
        total_out, legs = state
        if _is_better_final(
            candidate_out=int(total_out),
            candidate_legs=legs,
            best_out=int(best_out),
            best_legs=best_legs,
        ):
            best_out = int(total_out)
            best_legs = legs
    if best_legs is None:
        return None
    return (int(best_out), best_legs)


def _index_by_spent(states: _DPTable, *, max_legs: int) -> dict[int, tuple[int, _State]]:
    """Index states by spent value, keeping the best state per spent.

    Returns spent -> (legs_used, best_state). Only keeps states with
    legs_used < max_legs (so there is room for one more interior-pool leg).
    """
    by_spent: dict[int, tuple[int, _State]] = {}
    for (used_legs, spent), state in states.items():
        if int(used_legs) >= int(max_legs):
            continue
        existing = by_spent.get(int(spent))
        if existing is None or _is_better_state(state, existing[1]):
            by_spent[int(spent)] = (int(used_legs), state)
    return by_spent


def _combine_prefix_suffix_by_spent(
    *,
    prefix_index: dict[int, tuple[int, _State]],
    suffix_index: dict[int, tuple[int, _State]],
    amount_total: int,
    max_legs: int,
) -> dict[int, _State]:
    """Combine prefix and suffix DP indices by spent value.

    For each (prefix_spent, suffix_spent) pair with prefix_spent + suffix_spent
    <= amount_total, produce a combined state at combined_spent = prefix_spent +
    suffix_spent. The legs are merged (sorted). Only combinations with
    legs_used < max_legs are kept (room for the interior pool).

    Returns combined_spent -> best_state.
    """
    combined: dict[int, _State] = {}
    for p_spent, (p_legs_used, p_state) in prefix_index.items():
        for s_spent, (s_legs_used, s_state) in suffix_index.items():
            total_spent = int(p_spent) + int(s_spent)
            if int(total_spent) >= int(amount_total):
                continue
            total_legs = int(p_legs_used) + int(s_legs_used)
            if int(total_legs) >= int(max_legs):
                continue
            p_out, p_legs = p_state
            s_out, s_legs = s_state
            merged_legs = tuple(sorted((*p_legs, *s_legs)))
            # Check for duplicate pool_ids (prefix and suffix must be disjoint).
            p_ids = {pid for pid, _ in p_legs}
            s_ids = {pid for pid, _ in s_legs}
            if p_ids & s_ids:
                continue
            candidate: _State = (int(p_out) + int(s_out), merged_legs)
            existing = combined.get(int(total_spent))
            if existing is None or _is_better_state(candidate, existing):
                combined[int(total_spent)] = candidate
    return combined


def _best_with_residual_from_combined(
    *,
    combined: dict[int, _State],
    interior_pool_id: _PoolId,
    interior_min_valid: int,
    quote_fn: Callable[[_PoolId, int], int | None],
    amount_total: int,
) -> _State | None:
    """Find the best state where the interior pool absorbs the residual.

    For each combined state at spent s, the residual r = amount_total - s goes
    to the interior pool. If r > 0 and feasible, evaluate the total.
    """
    best_out = -1
    best_legs: tuple[tuple[_PoolId, int], ...] | None = None
    for spent, state in combined.items():
        residual = int(amount_total) - int(spent)
        if residual <= 0:
            continue
        if int(residual) < int(interior_min_valid):
            continue
        out_residual = quote_fn(interior_pool_id, int(residual))
        if out_residual is None:
            continue
        total_out, legs = state
        candidate_out = int(total_out) + int(out_residual)
        candidate_legs = tuple(sorted((*legs, (interior_pool_id, int(residual)))))
        if _is_better_final(
            candidate_out=int(candidate_out),
            candidate_legs=candidate_legs,
            best_out=int(best_out),
            best_legs=best_legs,
        ):
            best_out = int(candidate_out)
            best_legs = candidate_legs
    if best_legs is None:
        return None
    return (int(best_out), best_legs)


def _build_prefix_suffix_dps(
    *,
    pools: Sequence[_PoolSpec],
    jump_points: dict[_PoolId, list[tuple[int, int]]],
    amount_total: int,
    max_legs: int,
) -> tuple[list[_DPTable], list[_DPTable]]:
    """Build prefix and suffix DP tables for each pool position.

    prefix[i] = DP over pools[0..i-1] (pools before position i).
    suffix[i] = DP over pools[i+1..k-1] (pools after position i).

    Uses pre-computed jump-point outputs to avoid re-quoting during DP folding.
    This shares work: instead of running k+1 separate DPs (one per interior-pool
    exclusion), we run 2 forward/backward passes and combine in O(1) per pair.
    """
    ordered = sorted(pools, key=lambda p: p.pool_id)
    k = len(ordered)

    # Prefix DP: prefix[0] = {(0,0): (0,())}, prefix[i] folds pools[0..i-1].
    prefix: list[_DPTable] = [{} for _ in range(k + 1)]
    prefix[0] = {(0, 0): (0, ())}
    for i in range(k):
        spec = ordered[i]
        candidates = jump_points.get(spec.pool_id, [])
        prefix[i + 1] = _dp_fold_pool_with_outputs(
            states=prefix[i],
            pool_id=spec.pool_id,
            candidates=candidates,
            amount_total=int(amount_total),
            max_legs=int(max_legs),
        )

    # Suffix DP: suffix[k] = {(0,0): (0,())}, suffix[i] folds pools[i+1..k-1].
    suffix: list[_DPTable] = [{} for _ in range(k + 1)]
    suffix[k] = {(0, 0): (0, ())}
    for i in range(k - 1, -1, -1):
        spec = ordered[i]
        candidates = jump_points.get(spec.pool_id, [])
        suffix[i] = _dp_fold_pool_with_outputs(
            states=suffix[i + 1],
            pool_id=spec.pool_id,
            candidates=candidates,
            amount_total=int(amount_total),
            max_legs=int(max_legs),
        )

    return prefix, suffix


def _total_jump_point_count(jump_points: dict[_PoolId, list[tuple[int, int]]]) -> int:
    return sum(len(pts) for pts in jump_points.values())


def staircase_k_pool_best_split(
    *,
    pool_specs: Sequence[_PoolSpec],
    amount_in_total: int,
    max_legs: int,
    quote_exact_in: _QuoteExactIn,
) -> dict[_PoolId, int]:
    """Exact k-pool CPMM split by enumerating jump points + one interior pool.

    Returns the canonical-best allocation as {pool_id: amount}. Pools not in the
    result dict receive 0.

    Complexity: O(Σ B_i * Q) for jump enumeration + O(k * S * B_max) for the
    prefix/suffix DP + O(k * S^2) for combination, where S is the number of
    distinct spent values in the DP and B_max is the largest breakpoint set.
    For skewed pools B_i << D, so this is much cheaper than O(k * D^2) brute DP.

    When breakpoints are dense (Σ B_i >= k * D / 4), the sparsity advantage is
    lost and the caller should use the existing exact small-domain DP instead.
    Use `best_k_pool_exact_in_split` for the adaptive entry point that picks the
    cheaper solver automatically.
    """
    amount_total = _require_positive_control(amount_in_total, name="amount_in_total")
    max_legs_i = _require_positive_control(max_legs, name="max_legs")
    if not pool_specs:
        raise ValueError("no pools provided")

    request = _KPoolStaircaseRequest(
        pools=tuple(pool_specs),
        amount_in_total=int(amount_total),
        max_legs=int(max_legs_i),
        quote_exact_in=quote_exact_in,
    )
    context = _KPoolStaircaseContext(request=request)
    context.jump_points = _build_jump_points(request)

    def quote_fn(pool_id: _PoolId, amount: int) -> int | None:
        return context.quote(pool_id, int(amount))

    ordered = sorted(pool_specs, key=lambda p: p.pool_id)
    k = len(ordered)

    # Build prefix and suffix DP tables once (2 passes, not k+1).
    prefix, suffix = _build_prefix_suffix_dps(
        pools=tuple(pool_specs),
        jump_points=context.jump_points,
        amount_total=int(amount_total),
        max_legs=int(max_legs_i),
    )

    best: _State | None = None

    # Case 1: no interior pool. All positive pools at jump edges, sum = D.
    # This is the full prefix DP (prefix[k]) checked for exact spend = D.
    candidate_no_interior = _best_exact_full_from_dp(
        states=prefix[k],
        amount_total=int(amount_total),
        max_legs=int(max_legs_i),
    )
    if candidate_no_interior is not None and _is_better_state(candidate_no_interior, best):
        best = candidate_no_interior

    # Case 2: each pool takes a turn as the interior pool (absorbs the residual).
    # Combine prefix[i] and suffix[i+1] (excluding pool at position i), then
    # probe the residual for pool i.
    for i in range(k):
        spec = ordered[i]
        # prefix[i] covers pools[0..i-1], suffix[i+1] covers pools[i+1..k-1].
        # Together they cover all pools except pool at position i.
        prefix_index = _index_by_spent(prefix[i], max_legs=int(max_legs_i))
        suffix_index = _index_by_spent(suffix[i + 1], max_legs=int(max_legs_i))
        combined = _combine_prefix_suffix_by_spent(
            prefix_index=prefix_index,
            suffix_index=suffix_index,
            amount_total=int(amount_total),
            max_legs=int(max_legs_i),
        )
        candidate = _best_with_residual_from_combined(
            combined=combined,
            interior_pool_id=spec.pool_id,
            interior_min_valid=int(spec.min_valid),
            quote_fn=quote_fn,
            amount_total=int(amount_total),
        )
        if candidate is not None and _is_better_state(candidate, best):
            best = candidate

    if best is None:
        raise ValueError("no feasible split")

    _, legs = best
    alloc: dict[_PoolId, int] = {spec.pool_id: 0 for spec in pool_specs}
    for pool_id, amount in legs:
        alloc[pool_id] = int(amount)
    return alloc


def best_k_pool_exact_in_split(
    *,
    pool_specs: Sequence[_PoolSpec],
    amount_in_total: int,
    max_legs: int,
    quote_exact_in: _QuoteExactIn,
    small_domain_dp_fn: Callable[..., dict[_PoolId, int]] | None = None,
) -> dict[_PoolId, int]:
    """Adaptive entry point: pick the cheaper exact solver.

    Uses a cheap analytical sparsity estimate first. If the estimate suggests
    dense breakpoints, falls back to the existing exact small-domain DP without
    enumerating any jump points. If the estimate is ambiguous, enumerates jump
    points with an early-exit cap: if the breakpoint count exceeds the threshold
    before enumeration completes, falls back immediately without finishing
    enumeration.

    The `small_domain_dp_fn` parameter lets the caller inject the existing DP
    (best_small_domain_many_pool_exact_in) without creating a hard import cycle.
    If not provided, the staircase DP is always used.
    """
    amount_total = _require_positive_control(amount_in_total, name="amount_in_total")
    max_legs_i = _require_positive_control(max_legs, name="max_legs")
    if not pool_specs:
        raise ValueError("no pools provided")

    k = len(pool_specs)
    threshold = (k * int(amount_total)) // _DENSE_BREAKPOINT_FALLBACK_RATIO

    # Phase 1: cheap analytical sparsity estimate (no quotes).
    # If ALL pools are estimated dense, skip enumeration entirely.
    if small_domain_dp_fn is not None:
        max_est_density = max(
            _estimate_breakpoint_sparsity(spec.pool, int(amount_total))
            for spec in pool_specs
        )
        # If the densest pool is estimated to have > 25% breakpoints, the
        # staircase DP will almost certainly lose. Fall back without enumerating.
        if max_est_density > 0.25:
            return _fallback_to_small_dp(
                small_domain_dp_fn=small_domain_dp_fn,
                pool_specs=pool_specs,
                amount_total=int(amount_total),
                max_legs=int(max_legs_i),
                quote_exact_in=quote_exact_in,
            )

    # Phase 2: bounded enumeration with early exit.
    request = _KPoolStaircaseRequest(
        pools=tuple(pool_specs),
        amount_in_total=int(amount_total),
        max_legs=int(max_legs_i),
        quote_exact_in=quote_exact_in,
    )
    context = _KPoolStaircaseContext(request=request)

    # Enumerate with early exit per pool. If any pool exceeds the per-pool cap,
    # fall back immediately without finishing enumeration.
    per_pool_cap = int(threshold) + 1
    jump_points: dict[_PoolId, list[tuple[int, int]]] = {}
    for spec in pool_specs:
        pts = _pool_jump_points_bounded(
            spec.pool,
            int(amount_total),
            quote_exact_in=quote_exact_in,
            max_breakpoints=int(per_pool_cap),
        )
        if pts is None:
            # Dense breakpoints detected: fall back to the existing DP.
            if small_domain_dp_fn is not None:
                return _fallback_to_small_dp(
                    small_domain_dp_fn=small_domain_dp_fn,
                    pool_specs=pool_specs,
                    amount_total=int(amount_total),
                    max_legs=int(max_legs_i),
                    quote_exact_in=quote_exact_in,
                )
            # No fallback available: do full enumeration.
            pts = _pool_jump_points(
                spec.pool,
                int(amount_total),
                quote_exact_in=quote_exact_in,
            )
        jump_points[spec.pool_id] = pts
    context.jump_points = jump_points

    # Sparse breakpoints: run the staircase DP (reuses already-enumerated jumps).
    return _staircase_split_with_context(
        context=context,
        pool_specs=tuple(pool_specs),
        amount_total=int(amount_total),
        max_legs=int(max_legs_i),
    )


def _fallback_to_small_dp(
    *,
    small_domain_dp_fn: Callable[..., dict[_PoolId, int]],
    pool_specs: Sequence[_PoolSpec],
    amount_total: int,
    max_legs: int,
    quote_exact_in: _QuoteExactIn,
) -> dict[_PoolId, int]:
    """Fall back to the existing exact small-domain DP."""
    pools_by_id = {spec.pool_id: spec.pool for spec in pool_specs}

    def quote_for_pool_id(pool_id: _PoolId, amount: int) -> int | None:
        if int(amount) <= 0:
            return 0
        try:
            return int(quote_exact_in(pools_by_id[pool_id], int(amount)))
        except ValueError:
            return None

    return small_domain_dp_fn(
        pool_ids=sorted(spec.pool_id for spec in pool_specs),
        amount_in_total=int(amount_total),
        max_legs=int(max_legs),
        quote_for_pool_id=quote_for_pool_id,
    )


def _staircase_split_with_context(
    *,
    context: _KPoolStaircaseContext,
    pool_specs: tuple[_PoolSpec, ...],
    amount_total: int,
    max_legs: int,
) -> dict[_PoolId, int]:
    """Run the staircase DP using an already-built context (jump points cached)."""
    def quote_fn(pool_id: _PoolId, amount: int) -> int | None:
        return context.quote(pool_id, int(amount))

    ordered = sorted(pool_specs, key=lambda p: p.pool_id)
    k = len(ordered)

    prefix, suffix = _build_prefix_suffix_dps(
        pools=pool_specs,
        jump_points=context.jump_points,
        amount_total=int(amount_total),
        max_legs=int(max_legs),
    )

    best: _State | None = None

    candidate_no_interior = _best_exact_full_from_dp(
        states=prefix[k],
        amount_total=int(amount_total),
        max_legs=int(max_legs),
    )
    if candidate_no_interior is not None and _is_better_state(candidate_no_interior, best):
        best = candidate_no_interior

    for i in range(k):
        spec = ordered[i]
        prefix_index = _index_by_spent(prefix[i], max_legs=int(max_legs))
        suffix_index = _index_by_spent(suffix[i + 1], max_legs=int(max_legs))
        combined = _combine_prefix_suffix_by_spent(
            prefix_index=prefix_index,
            suffix_index=suffix_index,
            amount_total=int(amount_total),
            max_legs=int(max_legs),
        )
        candidate = _best_with_residual_from_combined(
            combined=combined,
            interior_pool_id=spec.pool_id,
            interior_min_valid=int(spec.min_valid),
            quote_fn=quote_fn,
            amount_total=int(amount_total),
        )
        if candidate is not None and _is_better_state(candidate, best):
            best = candidate

    if best is None:
        raise ValueError("no feasible split")

    _, legs = best
    alloc: dict[_PoolId, int] = {spec.pool_id: 0 for spec in pool_specs}
    for pool_id, amount in legs:
        alloc[pool_id] = int(amount)
    return alloc


def should_use_staircase_dp(
    *,
    pool_specs: Sequence[_PoolSpec],
    amount_in_total: int,
    jump_points: dict[_PoolId, list[tuple[int, int]]] | None = None,
) -> bool:
    """Decide whether the staircase DP is worth running vs the existing DP.

    The staircase DP wins when jump points are sparse (B_i << D). When
    breakpoints are dense (Σ B_i >= k * D / threshold), the existing exact
    small-domain DP is cheaper because it avoids the prefix/suffix combination
    overhead.
    """
    k = len(pool_specs)
    if k <= 0 or int(amount_in_total) <= 0:
        return False
    if jump_points is None:
        return True  # Caller hasn't enumerated yet; let them try.
    total_breakpoints = _total_jump_point_count(jump_points)
    # Staircase wins when breakpoints are at least _DENSE_BREAKPOINT_FALLBACK_RATIO
    # times sparser than the full k * D range.
    threshold = (k * int(amount_in_total)) // _DENSE_BREAKPOINT_FALLBACK_RATIO
    return int(total_breakpoints) < int(threshold)
