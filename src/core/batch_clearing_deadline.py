"""
Batch clearing A-optimization via deadline scheduling (experimental).

Reformulates CPMM batch clearing as weighted deadline scheduling under the
constant-k approximation. The DP finds the maximum-weight feasible subset in
EDF order in O(n * S) pseudo-polynomial time (S = total amount_in). A local
search pass (insert + 1-out-1-in with real CPMM simulation) heuristically
reduces the approximation gap for small batches.

Scope: this is an experimental prototype. The DP is exact for the
constant-k deadline model (A-optimal subset selection under EDF). The local
search heuristically reduces the approximation gap for the actual CPMM
ordering; it is not a completeness proof. Property tests verify A-matching
against a brute-force oracle for n <= 6 (200 random cases). Promotion to
the live batch clearing path requires exhaustive small-domain verification,
B-refinement integration, Intent/PoolState integration, and production-scale
resource profiling.

Key insight: under the constant-k approximation (k = R_in * R_out >= k_0,
since fees only increase k), each SWAP_EXACT_IN intent has a closed-form
deadline: the maximum cumulative gross_in of preceding swaps before the
intent's output drops below its effective minimum (max(min_amount_out, 1),
since the CPMM kernel rejects amount_out <= 0).

This module is parameterized by the quote function to stay free of runtime
dependencies.
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Callable, Dict, List, Optional, Sequence, Tuple

BPS_DENOM = 10_000


@dataclass(frozen=True)
class DeadlineSwap:
    """A swap with its computed deadline and processing time.

    Attributes:
        intent_id: Stable identifier for tie-breaking.
        amount_in: Gross input (also the weight for A-maximization).
        min_amount_out: Slippage limit; swap fails if output < this.
        net_in: amount_in - fee (the effective input that moves the price).
        deadline: Maximum cumulative gross_in of preceding swaps before this
            swap's output drops below effective_min under constant-k. The
            effective minimum is max(min_amount_out, 1) because the CPMM
            kernel rejects amount_out <= 0. A deadline of -1 means the swap
            can never execute.
        index: Original position in the intent list (for stable tie-breaking).
    """
    intent_id: str
    amount_in: int
    min_amount_out: int
    net_in: int
    deadline: Optional[int]
    index: int


@dataclass(frozen=True)
class DeadlineScheduleResult:
    """Result of deadline-scheduling batch clearing.

    Attributes:
        ordered_intents: Intent IDs in execution order (EDF + local search).
        total_a: Total executed input volume.
        total_b: Total surplus (amount_out - min_amount_out).
        selected_count: Number of swaps in the schedule from DP selection.
        excluded_count: Number of swaps excluded from the final schedule.
        greedy_added_count: Number of swaps added by local search completion.
    """
    ordered_intents: Tuple[str, ...]
    total_a: int
    total_b: int
    selected_count: int
    excluded_count: int
    greedy_added_count: int


class ResourceLimitExceeded(Exception):
    """Raised when the DP exceeds its resource bounds (fail-closed)."""


def _compute_fee(gross_in: int, fee_bps: int) -> int:
    """Compute ceil(gross_in * fee_bps / 10000)."""
    if gross_in <= 0 or fee_bps <= 0:
        return 0
    return (gross_in * fee_bps + BPS_DENOM - 1) // BPS_DENOM


def _compute_net_in(amount_in: int, fee_bps: int) -> int:
    """Compute net_in = amount_in - fee_total."""
    fee = _compute_fee(amount_in, fee_bps)
    return amount_in - fee


def compute_deadline(
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    amount_in: int,
    min_amount_out: int,
    fee_bps: int,
) -> Optional[int]:
    """Compute the deadline for a SWAP_EXACT_IN intent under constant-k.

    The deadline is the maximum value of R_in' (the pool's input reserve after
    preceding swaps) such that the swap still produces amount_out >= min_amount_out.

    Under constant-k (k = R_in * R_out = k_0), R_out' = k_0 / R_in'. The swap
    output is:

        amount_out = floor(R_out' * net_in / (R_in' + net_in))

    For the swap to execute, amount_out >= min_amount_out, which gives:

        net_in * (R_out' - m) >= m * R_in'    (ignoring floor for the bound)

    Substituting R_out' = k_0 / R_in':

        net_in * k_0 / R_in' - net_in * m >= m * R_in'
        net_in * k_0 >= m * R_in'^2 + net_in * m * R_in'
        m * x^2 + net_in * m * x - net_in * k_0 <= 0

    The positive root is:

        x = (-net_in * m + sqrt((net_in * m)^2 + 4 * m * net_in * k_0)) / (2 * m)

    The deadline is floor(x) - reserve_in_0 (relative to the starting reserve).

    Returns None if the deadline is infinity (swap always produces output >= 1).
    Returns -1 if the swap can never execute (net_in <= 0 or deadline < 0).

    Note: The CPMM kernel rejects amount_out <= 0 with ValueError, so the
    effective minimum output is max(min_amount_out, 1). A swap with
    min_amount_out=0 still has a finite deadline: the point where amount_out
    drops to 0 and the kernel rejects it.
    """
    # The CPMM kernel rejects amount_out <= 0, so effective min is at least 1.
    effective_min = max(min_amount_out, 1)

    net_in = _compute_net_in(amount_in, fee_bps)
    if net_in <= 0:
        return -1  # Fee consumes entire input; can never execute

    k_0 = reserve_in_0 * reserve_out_0

    # Quadratic: m * x^2 + net_in * m * x - net_in * k_0 <= 0
    # Positive root: x = (-b + sqrt(b^2 + 4ac)) / (2a)
    # where a = m, b = net_in * m, c = net_in * k_0
    a_coeff = effective_min
    b_coeff = net_in * effective_min
    c_coeff = net_in * k_0

    discriminant = b_coeff * b_coeff + 4 * a_coeff * c_coeff
    sqrt_disc = math.isqrt(discriminant)

    # x = (-b_coeff + sqrt_disc) / (2 * a_coeff)
    # Use floor division (conservative: deadline is the largest x where the
    # quadratic is still <= 0, and floor gives us the largest integer x).
    numerator = -b_coeff + sqrt_disc
    denominator = 2 * a_coeff

    if numerator <= 0:
        return -1  # Even at R_in' = 0, the swap doesn't produce enough output

    x = numerator // denominator  # floor division (conservative)
    deadline_relative = x - reserve_in_0

    if deadline_relative < 0:
        return -1  # Swap cannot execute even with no preceding swaps

    return deadline_relative


def _build_deadline_swaps(
    intents: List[Tuple[str, int, int]],  # (intent_id, amount_in, min_amount_out)
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
) -> List[DeadlineSwap]:
    """Compute deadlines for all swaps.

    Returns a list of DeadlineSwap sorted by deadline (EDF order).
    Swaps with deadline = -1 (never executable) are excluded.
    """
    deadline_swaps: List[DeadlineSwap] = []
    for idx, (intent_id, amount_in, min_amount_out) in enumerate(intents):
        net_in = _compute_net_in(amount_in, fee_bps)
        deadline = compute_deadline(
            reserve_in_0=reserve_in_0,
            reserve_out_0=reserve_out_0,
            amount_in=amount_in,
            min_amount_out=min_amount_out,
            fee_bps=fee_bps,
        )
        if deadline is not None and deadline < 0:
            continue  # Never executable; exclude
        deadline_swaps.append(DeadlineSwap(
            intent_id=intent_id,
            amount_in=amount_in,
            min_amount_out=min_amount_out,
            net_in=net_in,
            deadline=deadline,
            index=idx,
        ))

    # Sort by deadline (EDF order). None deadlines (infinity) go last.
    # Tie-break by index for determinism.
    deadline_swaps.sort(key=lambda s: (s.deadline if s.deadline is not None else math.inf, s.index))
    return deadline_swaps


def _dp_select_subset(
    swaps: List[DeadlineSwap],
    *,
    max_dp_states: int,
) -> Tuple[List[int], int]:
    """Select the maximum-weight feasible subset via DP.

    Uses a sparse DP where dp[s] = max total A with cumulative gross_in = s.
    Iterates swaps in EDF order. For each swap, if cumulative gross_in s <= d_i,
    the swap can execute, and we transition to s + amount_in_i.

    Returns (selected_indices, total_a) where selected_indices are indices into
    the swaps list (in EDF order).

    Raises ResourceLimitExceeded if the DP table exceeds max_dp_states.
    """
    if not swaps:
        return [], 0

    # dp[s] = (total_a, backtrack_index)
    # We use a dict for sparse representation.
    # dp[0] = (0, -1)  # base case: no swaps selected, total_a = 0
    dp: Dict[int, Tuple[int, int]] = {0: (0, -1)}
    # For backtracking, we need to store which swap was added at each state.
    # dp_history[i] = dict mapping s -> (prev_s, swap_index, total_a)
    dp_history: List[Dict[int, Tuple[int, int, int]]] = []

    for i, swap in enumerate(swaps):
        if len(dp) > max_dp_states:
            raise ResourceLimitExceeded(
                f"DP table exceeded max_dp_states={max_dp_states}: {len(dp)} states"
            )

        new_dp: Dict[int, Tuple[int, int]] = dict(dp)
        history_step: Dict[int, Tuple[int, int, int]] = {}

        deadline = swap.deadline if swap.deadline is not None else math.inf

        for s, (a, _) in dp.items():
            if s > deadline:
                continue  # Swap cannot execute at cumulative gross_in s
            new_s = s + swap.amount_in
            new_a = a + swap.amount_in
            if new_s not in new_dp or new_dp[new_s][0] < new_a:
                new_dp[new_s] = (new_a, i)
                history_step[new_s] = (s, i, new_a)

        # Check resource limit after state insertion (fail-closed)
        if len(new_dp) > max_dp_states:
            raise ResourceLimitExceeded(
                f"DP table exceeded max_dp_states={max_dp_states}: {len(new_dp)} states"
            )

        dp = new_dp
        dp_history.append(history_step)

    # Find the best total_a
    best_s = max(dp, key=lambda s: dp[s][0])
    best_a = dp[best_s][0]

    # Backtrack to find selected swaps
    selected: List[int] = []
    s = best_s
    for i in range(len(swaps) - 1, -1, -1):
        if s in dp_history[i]:
            prev_s, swap_idx, _ = dp_history[i][s]
            selected.append(swap_idx)
            s = prev_s

    selected.reverse()
    return selected, best_a


def _greedy_completion(
    selected_swaps: List[DeadlineSwap],
    excluded_swaps: List[DeadlineSwap],
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
    quote_exact_in_fn: Callable,
) -> Tuple[List[DeadlineSwap], int]:
    """Local search completion: insert and replace to heuristically reduce the constant-k gap.

    The deadline-based DP is conservative (underestimates R_out), so some swaps
    excluded by the DP may actually execute with the real CPMM formula. This
    function applies two types of local search moves:

    1. INSERT: Try inserting each excluded swap at every position. If all swaps
       in the resulting schedule execute, keep it.
    2. (1-out, 1-in): Remove a selected swap, insert an excluded swap at every
       position. If the replacement is feasible and has higher total A, keep it.

    Iterate until no improvement is found.

    Returns (final_schedule, greedy_added_count).

    Complexity: O(n^2 * k) per round where k = rounds (typically 1-3).
    """
    schedule = list(selected_swaps)
    remaining = list(excluded_swaps)
    greedy_added = 0

    changed = True
    while changed and remaining:
        changed = False

        # Phase 1: Try INSERT moves (add excluded swaps without removing any)
        for rem_idx, candidate in enumerate(remaining):
            for pos in range(len(schedule) + 1):
                trial = schedule[:pos] + [candidate] + schedule[pos:]
                if _schedule_all_execute(
                    trial,
                    reserve_in_0=reserve_in_0,
                    reserve_out_0=reserve_out_0,
                    fee_bps=fee_bps,
                    quote_exact_in_fn=quote_exact_in_fn,
                ):
                    schedule.insert(pos, candidate)
                    greedy_added += 1
                    remaining.pop(rem_idx)
                    changed = True
                    break
            if changed:
                break

        if changed:
            continue

        # Phase 2: Try (1-out, 1-in) moves: remove a selected swap, insert
        # an excluded swap at every position. This handles cases where the
        # constant-k deadline excluded a swap that could execute in a different
        # ordering than the DP's EDF sequence.
        best_a = _total_a(schedule)
        best_trial: Optional[List[DeadlineSwap]] = None
        best_rem_idx = -1

        for rem_idx, candidate in enumerate(remaining):
            for sel_idx in range(len(schedule)):
                without = schedule[:sel_idx] + schedule[sel_idx + 1:]
                for pos in range(len(without) + 1):
                    trial = without[:pos] + [candidate] + without[pos:]
                    if _schedule_all_execute(
                        trial,
                        reserve_in_0=reserve_in_0,
                        reserve_out_0=reserve_out_0,
                        fee_bps=fee_bps,
                        quote_exact_in_fn=quote_exact_in_fn,
                    ):
                        trial_a = _total_a(trial)
                        if trial_a > best_a:
                            best_a = trial_a
                            best_trial = list(trial)
                            best_rem_idx = rem_idx

        if best_trial is not None:
            # Identify the removed swap (the one in schedule but not in best_trial)
            old_set = set(id(s) for s in schedule)
            new_set = set(id(s) for s in best_trial)
            removed = [s for s in schedule if id(s) not in new_set]
            schedule = best_trial
            remaining.pop(best_rem_idx)
            # Return the removed swap to remaining (it might be re-insertable
            # in a later round at a different position)
            remaining.extend(removed)
            changed = True

    return schedule, greedy_added


def _total_a(swaps: List[DeadlineSwap]) -> int:
    """Sum of amount_in for all swaps in the list."""
    return sum(s.amount_in for s in swaps)


def _schedule_all_execute(
    schedule: List[DeadlineSwap],
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
    quote_exact_in_fn: Callable,
) -> bool:
    """Check that all swaps in the schedule execute with the real CPMM formula.

    Returns True iff every swap produces amount_out >= effective_min when
    executed in order against the actual (non-constant-k) CPMM reserves.
    The effective minimum is max(min_amount_out, 1) because the CPMM kernel
    rejects amount_out <= 0 with ValueError.
    """
    r_in = reserve_in_0
    r_out = reserve_out_0
    for swap in schedule:
        try:
            quote = quote_exact_in_fn(
                reserve_in=r_in,
                reserve_out=r_out,
                amount_in=swap.amount_in,
                fee_bps=fee_bps,
            )
            if quote.amount_out < max(swap.min_amount_out, 1):
                return False
            r_in = quote.reserve_in_after
            r_out = quote.reserve_out_after
        except ValueError:
            return False
    return True


def _simulate_schedule(
    ordered_swaps: List[DeadlineSwap],
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
    quote_exact_in_fn: Callable,
) -> Tuple[int, int]:
    """Simulate a schedule and return (total_a, total_b).

    total_a = sum of amount_in for executed swaps.
    total_b = sum of (amount_out - min_amount_out) for executed swaps.

    Fail-closed: if any swap in the schedule does not execute (amount_out <
    effective_min or ValueError), raises ResourceLimitExceeded. This catches
    deadline formula bugs or quote semantics drift that would otherwise
    silently produce an invalid schedule.
    """
    r_in = reserve_in_0
    r_out = reserve_out_0
    total_a = 0
    total_b = 0

    for swap in ordered_swaps:
        try:
            quote = quote_exact_in_fn(
                reserve_in=r_in,
                reserve_out=r_out,
                amount_in=swap.amount_in,
                fee_bps=fee_bps,
            )
        except ValueError as e:
            raise ResourceLimitExceeded(
                f"Swap {swap.intent_id} failed during final simulation: {e}"
            ) from e
        effective_min = max(swap.min_amount_out, 1)
        if quote.amount_out < effective_min:
            raise ResourceLimitExceeded(
                f"Swap {swap.intent_id} produced amount_out={quote.amount_out} "
                f"< effective_min={effective_min} (min_amount_out={swap.min_amount_out})"
            )
        total_a += swap.amount_in
        total_b += quote.amount_out - swap.min_amount_out
        r_in = quote.reserve_in_after
        r_out = quote.reserve_out_after

    return total_a, total_b


def deadline_schedule_batch(
    intents: List[Tuple[str, int, int]],  # (intent_id, amount_in, min_amount_out)
    *,
    reserve_in_0: int,
    reserve_out_0: int,
    fee_bps: int,
    quote_exact_in_fn: Callable,
    max_dp_states: int = 100_000,
) -> DeadlineScheduleResult:
    """Compute a batch clearing schedule via deadline scheduling (experimental).

    Finds the maximum-weight feasible subset under the constant-k approximation
    via DP (exact for the constant-k deadline model), then applies local search
    (insert + 1-out-1-in with real CPMM simulation) to heuristically reduce the
    approximation gap for the actual CPMM ordering. The local search is not a
    completeness proof. Property tests verify A-matching against a brute-force
    oracle for n <= 6.

    Args:
        intents: List of (intent_id, amount_in, min_amount_out) tuples.
        reserve_in_0: Initial input reserve of the pool.
        reserve_out_0: Initial output reserve of the pool.
        fee_bps: Fee in basis points (0-10000).
        quote_exact_in_fn: Function to quote a CPMM exact-in swap.
        max_dp_states: Maximum number of DP states before ResourceLimitExceeded.

    Returns:
        DeadlineScheduleResult with the ordered intent IDs and (A, B) totals.

    Raises:
        ResourceLimitExceeded: If the DP table exceeds max_dp_states, or if
            the final schedule fails validation (fail-closed).
    """
    if not intents:
        return DeadlineScheduleResult(
            ordered_intents=(),
            total_a=0,
            total_b=0,
            selected_count=0,
            excluded_count=0,
            greedy_added_count=0,
        )

    # 1. Compute deadlines and sort by EDF
    deadline_swaps = _build_deadline_swaps(
        intents,
        reserve_in_0=reserve_in_0,
        reserve_out_0=reserve_out_0,
        fee_bps=fee_bps,
    )

    if not deadline_swaps:
        return DeadlineScheduleResult(
            ordered_intents=(),
            total_a=0,
            total_b=0,
            selected_count=0,
            excluded_count=len(intents),
            greedy_added_count=0,
        )

    # 2. DP to select maximum-weight feasible subset
    selected_indices, dp_total_a = _dp_select_subset(
        deadline_swaps,
        max_dp_states=max_dp_states,
    )

    selected_swaps = [deadline_swaps[i] for i in selected_indices]
    excluded_swaps = [s for i, s in enumerate(deadline_swaps) if i not in set(selected_indices)]

    # 3. Local search completion: insert and replace to heuristically reduce the constant-k gap
    final_ordered, greedy_added = _greedy_completion(
        selected_swaps,
        excluded_swaps,
        reserve_in_0=reserve_in_0,
        reserve_out_0=reserve_out_0,
        fee_bps=fee_bps,
        quote_exact_in_fn=quote_exact_in_fn,
    )

    # 4. Simulate to get actual (A, B)
    total_a, total_b = _simulate_schedule(
        final_ordered,
        reserve_in_0=reserve_in_0,
        reserve_out_0=reserve_out_0,
        fee_bps=fee_bps,
        quote_exact_in_fn=quote_exact_in_fn,
    )

    # Count how many originally excluded swaps ended up in the final schedule
    selected_set = set(id(s) for s in selected_swaps)
    greedy_added_count = sum(1 for s in final_ordered if id(s) not in selected_set)

    return DeadlineScheduleResult(
        ordered_intents=tuple(s.intent_id for s in final_ordered),
        total_a=total_a,
        total_b=total_b,
        selected_count=len(final_ordered) - greedy_added_count,
        excluded_count=len(intents) - len(final_ordered),
        greedy_added_count=greedy_added_count,
    )
