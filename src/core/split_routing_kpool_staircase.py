"""
k-pool staircase exact-in split routing.

Generalizes the two-pool staircase optimizer to k parallel CPMM pools. The key
insight: for every feasible allocation, there exists a staircase allocation
(non-interior pools at jump-point left edges, one interior pool absorbing the
residual) that weakly dominates it in total output. This is mechanized in Lean
as `exists_dominated_staircase_representative`. The optimizer searches the
finite staircase space and selects the canonical best, which is at least as
good as any feasible allocation.

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

# Hard resource bounds for fail-closed operation. When any bound is exceeded,
# the staircase DP raises ResourceLimitExceeded so the adaptive entry point can
# fall back to the existing exact small-domain DP. These bounds preserve
# exactness because the fallback is also an exact solver.
#
# Structural ceilings:
#   |table|        <= (max_legs + 1) * (D + 1)
#   combine_pairs  <= (D * max_legs)^2   (Pareto index: D spent values,
#                       each with <= max_legs Pareto-optimal states per side)
#   residual_quotes <= D                 (one quote per combined spent value)
# We set bounds at the structural ceiling times a small constant to allow
# online Pareto pruning to keep the table well below the ceiling in practice.
_MAX_TABLE_STATES_MULTIPLIER = 2    # multiplier * (max_legs+1) * (D+1)
_MAX_COMBINE_PAIRS_MULTIPLIER = 2   # multiplier * D^2 * max_legs^2
_MAX_RESIDUAL_QUOTES_MULTIPLIER = 2  # multiplier * D


class ResourceLimitExceeded(Exception):
    """Raised when the staircase DP exceeds a hard resource bound.

    The adaptive entry point catches this and falls back to the existing
    exact small-domain DP. If no fallback is available, the caller sees
    this as a fail-closed rejection (no partial result returned).
    """


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
    # min_valid is the smallest positive amount that produces a successful quote
    # for this pool. It is NOT an independent lower-bound constraint: jump-point
    # legs and fallback paths rely on the quote function rejecting amounts below
    # min_valid (returning None or raising ValueError). The residual interior
    # leg enforces min_valid explicitly at _best_with_residual_from_combined.
    # Callers must ensure min_valid is derived from the same quote function used
    # at runtime, not from an independent source.
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

    Fail-closed on drift: if the quote function rejects a requested output
    level (ValueError) or the reached output falls below the requested level
    (closed-form estimate drift), this raises ValueError. This matches the
    two-pool staircase behavior: an "exact" solver must not silently lose
    optimality by returning a partial candidate set. The caller (adaptive
    entry point) catches this and falls back to the existing DP.
    """
    candidates: list[tuple[int, int]] = []
    next_output_level = 1
    while True:
        gross_in = _min_gross_in_for_output_level(pool, next_output_level)
        if gross_in is not None and gross_in <= int(amount_in_total):
            try:
                reached_output = quote_exact_in(pool, int(gross_in))
            except ValueError as exc:
                raise ValueError("quote rejected requested output level") from exc
            if int(reached_output) < int(next_output_level):
                raise ValueError("quote did not reach requested output level")
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

    Fail-closed on drift: if the quote function rejects a requested output
    level (ValueError) or the reached output falls below the requested level
    (closed-form estimate drift), this raises ValueError. This matches
    _pool_jump_points and the two-pool staircase behavior. The caller should
    catch this and fall back to the existing DP.
    """
    candidates: list[tuple[int, int]] = []
    next_output_level = 1
    while True:
        gross_in = _min_gross_in_for_output_level(pool, next_output_level)
        if gross_in is not None and gross_in <= int(amount_in_total):
            try:
                reached_output = quote_exact_in(pool, int(gross_in))
            except ValueError as exc:
                raise ValueError("quote rejected requested output level") from exc
            if int(reached_output) < int(next_output_level):
                raise ValueError("quote did not reach requested output level")
            candidates.append((int(gross_in), int(reached_output)))
            if len(candidates) > int(max_breakpoints):
                return None
            next_output_level = int(reached_output) + 1
            continue
        return candidates


def _estimate_breakpoint_count(
    pool: _PoolLike,
    amount_in_total: int,
) -> int:
    """Cheap analytical estimate of breakpoint count (no quotes, integer-only).

    Returns the estimated number of jump points in [1..D]. A value near D
    means dense (every integer is a breakpoint); near 0 means sparse.

    For CPMM with output floor(y*net/(x+net)), the output increases by 1 each
    time net crosses roughly (x+net)^2/(y) in marginal input. The number of
    breakpoints is approximately min(y, D * y / (x + D*alpha)) where alpha is
    the fee-adjusted fraction. When x is large relative to D, breakpoints are
    sparse; when x is small, they are dense.

    This is a heuristic for the adaptive fallback decision only; the exact
    decision uses bounded enumeration. All arithmetic is integer to preserve
    the repo's no-float invariant on the deterministic core path.
    """
    alpha = int(BPS_DENOM) - int(pool.fee_bps)
    if alpha <= 0 or int(pool.x) <= 0 or int(pool.y) <= 0:
        return int(amount_in_total)
    # Approximate number of output levels reachable: y * net_max / (x + net_max)
    # where net_max = D * alpha / BPS.
    net_max = (int(amount_in_total) * alpha) // int(BPS_DENOM)
    if net_max <= 0:
        return 0
    est_output_levels = (int(pool.y) * net_max) // (int(pool.x) + net_max)
    return min(int(est_output_levels), int(amount_in_total))


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
    max_table_states: int = 0,
) -> _DPTable:
    """Fold one pool's jump points (with pre-computed outputs) into the DP.

    This avoids re-quoting jump points whose outputs were already computed during
    enumeration. The `candidates` list contains (amount, output) pairs from
    _pool_jump_points.

    Online Pareto pruning: during the fold, a candidate at (legs, spent) is
    skipped if an existing state at the same spent has <= legs and >= output
    (dominance). This is sound because any future extension of the dominated
    state would use more legs and produce less output than the same extension
    of the dominating state. This keeps the table smaller without losing
    exactness, reducing the post-fold Pareto indexing work.

    Resource bound: if max_table_states > 0 and the table exceeds it, raises
    ResourceLimitExceeded so the caller can fall back to the exact small-domain
    DP.
    """
    next_states: _DPTable = dict(states)
    # Index existing states by spent for quick Pareto checks.
    # spent -> list of (legs_used, output) for non-dominated states.
    pareto_index: dict[int, list[tuple[int, int]]] = {}
    for (used_legs, spent), (total_out, _) in next_states.items():
        _pareto_insert(pareto_index, int(spent), int(used_legs), int(total_out))

    for (used_legs, spent), (total_out, legs) in states.items():
        if used_legs >= int(max_legs):
            continue
        for amount, out_amount in candidates:
            if amount <= 0:
                continue
            new_spent = int(spent) + int(amount)
            if new_spent > int(amount_total):
                continue
            new_legs_used = int(used_legs) + 1
            new_out = int(total_out) + int(out_amount)
            # Online Pareto check: skip if dominated by an existing state at
            # the same spent with <= legs and >= output.
            if _pareto_is_dominated(pareto_index, new_spent, new_legs_used, new_out):
                continue
            key = (new_legs_used, new_spent)
            candidate: _State = (
                new_out,
                tuple(sorted((*legs, (pool_id, int(amount))))),
            )
            if _is_better_state(candidate, next_states.get(key)):
                next_states[key] = candidate
                _pareto_insert(pareto_index, new_spent, new_legs_used, new_out)
                # Remove states dominated by the new one.
                _pareto_remove_dominated(pareto_index, new_spent, new_legs_used, new_out)
                # Resource bound check.
                if max_table_states > 0 and len(next_states) > max_table_states:
                    raise ResourceLimitExceeded(
                        f"DP table exceeded {max_table_states} states "
                        f"(got {len(next_states)})"
                    )
    return next_states


def _pareto_insert(
    index: dict[int, list[tuple[int, int]]],
    spent: int,
    legs_used: int,
    output: int,
) -> None:
    """Insert a state into the Pareto index, removing strictly dominated entries.

    Uses strict dominance: an entry is removed only if the new state has
    <= legs and >= output with at least one strict. Equal (legs, output)
    entries are both kept so _is_better_state can compare lexicographic legs.
    """
    entries = index.setdefault(spent, [])
    # Check if strictly dominated by existing.
    for legs_j, out_j in entries:
        if legs_j <= legs_used and out_j >= output:
            if legs_j < legs_used or out_j > output:
                return  # Strictly dominated, don't insert.
    # Remove existing entries strictly dominated by this one.
    index[spent] = [
        (legs_j, out_j) for legs_j, out_j in entries
        if not (legs_used <= legs_j and output >= out_j
                and (legs_used < legs_j or output > out_j))
    ]
    index[spent].append((legs_used, output))


def _pareto_is_dominated(
    index: dict[int, list[tuple[int, int]]],
    spent: int,
    legs_used: int,
    output: int,
) -> bool:
    """Check if a state is strictly Pareto-dominated by an existing state.

    Uses strict dominance: an existing state dominates the candidate only if
    it has strictly fewer legs OR strictly higher output (with the other axis
    being <= or >=). This preserves canonical tie-break: when legs and output
    are both equal, the candidate is NOT dominated, so _is_better_state can
    still compare lexicographic legs and keep the canonical-best route.
    """
    entries = index.get(spent)
    if entries is None:
        return False
    for legs_j, out_j in entries:
        # Strict dominance: legs_j <= legs_used and out_j >= output,
        # with at least one strict. Equal (legs, output) is NOT dominated.
        if legs_j <= legs_used and out_j >= output:
            if legs_j < legs_used or out_j > output:
                return True
    return False


def _pareto_remove_dominated(
    index: dict[int, list[tuple[int, int]]],
    spent: int,
    legs_used: int,
    output: int,
) -> None:
    """Remove entries strictly dominated by the new state.

    Uses strict dominance: an entry is removed only if the new state has
    <= legs and >= output with at least one strict. Equal (legs, output)
    entries are kept so canonical tie-break can compare lexicographic legs.
    """
    entries = index.get(spent)
    if entries is None:
        return
    index[spent] = [
        (legs_j, out_j) for legs_j, out_j in entries
        if not (legs_used <= legs_j and output >= out_j
                and (legs_used < legs_j or output > out_j))
    ]


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


def _index_by_spent_pareto(states: _DPTable, *, max_legs: int) -> dict[int, list[tuple[int, _State]]]:
    """Index states by spent value, keeping Pareto-optimal states per spent.

    A state (legs_a, out_a) dominates (legs_b, out_b) at the same spent if
    legs_a <= legs_b and out_a >= out_b (with at least one strict). We keep
    only non-dominated states because a state with fewer legs but lower output
    can enable a prefix/suffix combination that a higher-output state with more
    legs cannot (the legs budget constraint may exclude the latter).

    Returns spent -> list of (legs_used, state) for non-dominated states.
    Only keeps states with legs_used < max_legs (room for interior-pool leg).
    """
    by_spent: dict[int, list[tuple[int, _State]]] = {}
    for (used_legs, spent), state in states.items():
        if int(used_legs) >= int(max_legs):
            continue
        spent_i = int(spent)
        legs_i = int(used_legs)
        out_i = int(state[0])
        candidates = by_spent.setdefault(spent_i, [])
        # Check if this state is dominated by an existing one, or dominates some.
        is_dominated = False
        for legs_j, state_j in candidates:
            out_j = int(state_j[0])
            # state_j dominates state_i if legs_j <= legs_i and out_j >= out_i
            if legs_j <= legs_i and out_j >= out_i:
                is_dominated = True
                break
        if is_dominated:
            continue
        # Remove existing states dominated by this one.
        candidates = [
            (legs_j, state_j) for legs_j, state_j in candidates
            if not (legs_i <= legs_j and out_i >= int(state_j[0]))
        ]
        candidates.append((legs_i, state))
        by_spent[spent_i] = candidates
    return by_spent


def _combine_prefix_suffix_by_spent(
    *,
    prefix_index: dict[int, list[tuple[int, _State]]],
    suffix_index: dict[int, list[tuple[int, _State]]],
    amount_total: int,
    max_legs: int,
    max_combine_pairs: int = 0,
) -> dict[int, _State]:
    """Combine prefix and suffix DP indices by spent value.

    For each (prefix_spent, suffix_spent) pair with prefix_spent + suffix_spent
    < amount_total, produce a combined state at combined_spent. The legs are
    merged (sorted). Only combinations with legs_used < max_legs are kept
    (room for the interior pool).

    Returns combined_spent -> best_state (highest output, then fewest legs,
    then lex legs).

    Resource bound: if max_combine_pairs > 0 and the number of candidate pair
    iterations exceeds it, raises ResourceLimitExceeded.
    """
    combined: dict[int, _State] = {}
    pair_count = 0
    for p_spent, p_candidates in prefix_index.items():
        for s_spent, s_candidates in suffix_index.items():
            total_spent = int(p_spent) + int(s_spent)
            if int(total_spent) >= int(amount_total):
                continue
            for p_legs_used, p_state in p_candidates:
                for s_legs_used, s_state in s_candidates:
                    pair_count += 1
                    if max_combine_pairs > 0 and pair_count > max_combine_pairs:
                        raise ResourceLimitExceeded(
                            f"combine pairs exceeded {max_combine_pairs} "
                            f"(at {pair_count})"
                        )
                    total_legs = int(p_legs_used) + int(s_legs_used)
                    if int(total_legs) >= int(max_legs):
                        continue
                    p_out, p_legs = p_state
                    s_out, s_legs = s_state
                    # Check for duplicate pool_ids (prefix and suffix must be disjoint).
                    p_ids = {pid for pid, _ in p_legs}
                    s_ids = {pid for pid, _ in s_legs}
                    if p_ids & s_ids:
                        continue
                    merged_legs = tuple(sorted((*p_legs, *s_legs)))
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
    max_residual_quotes: int = 0,
) -> _State | None:
    """Find the best state where the interior pool absorbs the residual.

    For each combined state at spent s, the residual r = amount_total - s goes
    to the interior pool. If r > 0 and feasible, evaluate the total.

    Resource bound: if max_residual_quotes > 0 and the number of quote calls
    exceeds it, raises ResourceLimitExceeded.
    """
    best_out = -1
    best_legs: tuple[tuple[_PoolId, int], ...] | None = None
    quote_count = 0
    for spent, state in combined.items():
        residual = int(amount_total) - int(spent)
        if residual <= 0:
            continue
        if int(residual) < int(interior_min_valid):
            continue
        quote_count += 1
        if max_residual_quotes > 0 and quote_count > max_residual_quotes:
            raise ResourceLimitExceeded(
                f"residual quotes exceeded {max_residual_quotes} "
                f"(at {quote_count})"
            )
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
    max_table_states: int = 0,
) -> tuple[list[_DPTable], list[_DPTable]]:
    """Build prefix and suffix DP tables for each pool position.

    prefix[i] = DP over pools[0..i-1] (pools before position i).
    suffix[i] = DP over pools[i..k-1] (pools from position i onward).

    To exclude pool i as the interior pool, combine prefix[i] (pools before i)
    with suffix[i+1] (pools after i). This is what the main staircase loop does.

    Uses pre-computed jump-point outputs to avoid re-quoting during DP folding.
    This shares work: instead of running k+1 separate DPs (one per interior-pool
    exclusion), we run 2 forward/backward passes and combine in O(1) per pair.

    Resource bound: if max_table_states > 0 and any DP table exceeds it, raises
    ResourceLimitExceeded.
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
            max_table_states=max_table_states,
        )

    # Suffix DP: suffix[k] = {(0,0): (0,())}, suffix[i] folds pools[i..k-1].
    # To exclude pool i as interior, use suffix[i+1] (pools after i).
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
            max_table_states=max_table_states,
        )

    return prefix, suffix


def _total_jump_point_count(jump_points: dict[_PoolId, list[tuple[int, int]]]) -> int:
    return sum(len(pts) for pts in jump_points.values())


def _validate_pool_ids(pool_specs: Sequence[_PoolSpec]) -> None:
    """Fail-closed validation: reject duplicate pool_ids.

    The optimizer keys quote caches, jump points, and allocations by pool_id.
    Duplicate IDs would silently corrupt these maps, causing incorrect results.
    The existing small-domain DP rejects repeated IDs; this matches that contract.
    """
    seen: set[_PoolId] = set()
    for spec in pool_specs:
        if spec.pool_id in seen:
            raise ValueError(f"duplicate pool_id: {spec.pool_id}")
        seen.add(spec.pool_id)


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

    Rejects duplicate pool_ids (fail-closed, matching the existing DP contract).

    Hard resource bounds: enforces max_table_states, max_combine_pairs, and
    max_residual_quotes. If any bound is exceeded, raises ResourceLimitExceeded
    so the adaptive entry point can fall back to the exact small-domain DP.
    The structural ceiling for table states is (max_legs+1)*(D+1); we allow
    up to _MAX_TABLE_STATES_MULTIPLIER times that before triggering fallback.
    """
    amount_total = _require_positive_control(amount_in_total, name="amount_in_total")
    max_legs_i = _require_positive_control(max_legs, name="max_legs")
    if not pool_specs:
        raise ValueError("no pools provided")
    _validate_pool_ids(pool_specs)

    # Compute hard resource bounds from structural ceilings.
    D_i = int(amount_total)
    max_table_states = _MAX_TABLE_STATES_MULTIPLIER * (int(max_legs_i) + 1) * (D_i + 1)
    max_combine_pairs = _MAX_COMBINE_PAIRS_MULTIPLIER * D_i * D_i * int(max_legs_i) * int(max_legs_i)
    max_residual_quotes = _MAX_RESIDUAL_QUOTES_MULTIPLIER * D_i

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
        max_table_states=max_table_states,
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
        prefix_index = _index_by_spent_pareto(prefix[i], max_legs=int(max_legs_i))
        suffix_index = _index_by_spent_pareto(suffix[i + 1], max_legs=int(max_legs_i))
        combined = _combine_prefix_suffix_by_spent(
            prefix_index=prefix_index,
            suffix_index=suffix_index,
            amount_total=int(amount_total),
            max_legs=int(max_legs_i),
            max_combine_pairs=max_combine_pairs,
        )
        candidate = _best_with_residual_from_combined(
            combined=combined,
            interior_pool_id=spec.pool_id,
            interior_min_valid=int(spec.min_valid),
            quote_fn=quote_fn,
            amount_total=int(amount_total),
            max_residual_quotes=max_residual_quotes,
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
    _validate_pool_ids(pool_specs)

    k = len(pool_specs)
    threshold = (k * int(amount_total)) // _DENSE_BREAKPOINT_FALLBACK_RATIO

    # Phase 1: cheap analytical sparsity estimate (no quotes).
    # Use the sum of per-pool estimated breakpoint counts, not the max, so that
    # a single dense pool among many sparse ones does not trigger fallback when
    # the cumulative total is still below threshold.
    if small_domain_dp_fn is not None:
        est_total = sum(
            _estimate_breakpoint_count(spec.pool, int(amount_total))
            for spec in pool_specs
        )
        # If estimated total breakpoints already exceed the threshold, the
        # staircase DP will almost certainly lose. Fall back without enumerating.
        if est_total >= int(threshold):
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
    # fall back immediately without finishing enumeration. If any pool raises
    # ValueError (quote/formula drift), fall back to the existing DP rather than
    # silently returning a partial candidate set.
    per_pool_cap = int(threshold) + 1
    jump_points: dict[_PoolId, list[tuple[int, int]]] = {}
    try:
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
    except ValueError:
        # Quote/formula drift detected: fall back to the existing DP if
        # available, otherwise re-raise (fail-closed, no silent partial result).
        if small_domain_dp_fn is not None:
            return _fallback_to_small_dp(
                small_domain_dp_fn=small_domain_dp_fn,
                pool_specs=pool_specs,
                amount_total=int(amount_total),
                max_legs=int(max_legs_i),
                quote_exact_in=quote_exact_in,
            )
        raise
    context.jump_points = jump_points

    # Cumulative post-enumeration budget guard.
    # Even if each pool passes the per-pool cap, the total breakpoint count
    # could still make the O(k * S^2) combination path expensive. If the
    # cumulative count exceeds the threshold, fall back to the existing DP.
    if small_domain_dp_fn is not None:
        total_breakpoints = _total_jump_point_count(jump_points)
        if int(total_breakpoints) >= int(threshold):
            return _fallback_to_small_dp(
                small_domain_dp_fn=small_domain_dp_fn,
                pool_specs=pool_specs,
                amount_total=int(amount_total),
                max_legs=int(max_legs_i),
                quote_exact_in=quote_exact_in,
            )

    # Sparse breakpoints: run the staircase DP (reuses already-enumerated jumps).
    # ResourceLimitExceeded from hard resource bounds is caught here and falls
    # back to the exact small-domain DP, preserving exactness.
    try:
        return _staircase_split_with_context(
            context=context,
            pool_specs=tuple(pool_specs),
            amount_total=int(amount_total),
            max_legs=int(max_legs_i),
        )
    except ResourceLimitExceeded:
        if small_domain_dp_fn is not None:
            return _fallback_to_small_dp(
                small_domain_dp_fn=small_domain_dp_fn,
                pool_specs=pool_specs,
                amount_total=int(amount_total),
                max_legs=int(max_legs_i),
                quote_exact_in=quote_exact_in,
            )
        raise


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
    """Run the staircase DP using an already-built context (jump points cached).

    Raises ResourceLimitExceeded if any hard resource bound is exceeded.
    """
    D_i = int(amount_total)
    max_table_states = _MAX_TABLE_STATES_MULTIPLIER * (int(max_legs) + 1) * (D_i + 1)
    max_combine_pairs = _MAX_COMBINE_PAIRS_MULTIPLIER * D_i * D_i * int(max_legs) * int(max_legs)
    max_residual_quotes = _MAX_RESIDUAL_QUOTES_MULTIPLIER * D_i

    def quote_fn(pool_id: _PoolId, amount: int) -> int | None:
        return context.quote(pool_id, int(amount))

    ordered = sorted(pool_specs, key=lambda p: p.pool_id)
    k = len(ordered)

    prefix, suffix = _build_prefix_suffix_dps(
        pools=pool_specs,
        jump_points=context.jump_points,
        amount_total=int(amount_total),
        max_legs=int(max_legs),
        max_table_states=max_table_states,
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
        prefix_index = _index_by_spent_pareto(prefix[i], max_legs=int(max_legs))
        suffix_index = _index_by_spent_pareto(suffix[i + 1], max_legs=int(max_legs))
        combined = _combine_prefix_suffix_by_spent(
            prefix_index=prefix_index,
            suffix_index=suffix_index,
            amount_total=int(amount_total),
            max_legs=int(max_legs),
            max_combine_pairs=max_combine_pairs,
        )
        candidate = _best_with_residual_from_combined(
            combined=combined,
            interior_pool_id=spec.pool_id,
            interior_min_valid=int(spec.min_valid),
            quote_fn=quote_fn,
            amount_total=int(amount_total),
            max_residual_quotes=max_residual_quotes,
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
