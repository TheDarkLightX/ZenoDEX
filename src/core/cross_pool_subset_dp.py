"""Exact subset-DP oracles for cross-pool batch clearing.

This module is a pure, deterministic research oracle. It does not wire into
settlement and does not authorize state transitions. The modeled domain is a
same-direction batch of exact-in intents routed across CPMM pools with v8
fee-ceil/output-floor arithmetic and fees retained in pool reserves.

Contract:
- Inputs are integer reserves, fee_bps, and exact-in intent amounts.
- Output is an exact optimum for the modeled cross-pool problem within the
  configured search limits.
- Ties are deterministic: the DP keeps the first path reached by subset,
  intent-index, then split/allocation order.
- The solver is exponential in intent count and pseudo-polynomial in the split
  domain D. It removes the n! ordering factor by exploring the subset lattice.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations
from math import factorial
from typing import Iterable

from .domain_limits import is_strict_int

BPS_DENOM = 10_000


@dataclass(frozen=True)
class TwoPoolCPMM:
    """CPMM pool state in the swap direction: input reserve x, output reserve y."""

    x: int
    y: int
    fee_bps: int = 0


@dataclass(frozen=True)
class CrossPoolExecution:
    """One routed intent execution in the selected order."""

    intent_index: int
    amount_in_total: int
    amount_in_0: int
    amount_out_0: int
    amount_in_1: int
    amount_out_1: int


@dataclass(frozen=True)
class KPoolExecution:
    """One routed intent execution across k CPMM pools."""

    intent_index: int
    amount_in_total: int
    amount_in_by_pool: tuple[int, ...]
    amount_out_by_pool: tuple[int, ...]


@dataclass(frozen=True)
class SubsetDPLimits:
    """Fail-closed bounds for the advisory exact oracle."""

    max_intents: int = 20
    max_total_input: int = 100_000
    max_states_per_subset: int = 250_000
    max_pools: int = 5


@dataclass(frozen=True)
class CrossPoolBatchResult:
    amount_out_total: int
    executions: tuple[CrossPoolExecution, ...]
    max_states_per_subset: int
    final_state_count: int
    states_visited: int
    transitions_evaluated: int
    ordering_count_upper_bound: int
    max_compressed_collision: int = 0


@dataclass(frozen=True)
class KPoolBatchResult:
    amount_out_total: int
    executions: tuple[KPoolExecution, ...]
    pool_count: int
    max_states_per_subset: int
    final_state_count: int
    states_visited: int
    transitions_evaluated: int
    ordering_count_upper_bound: int


@dataclass(frozen=True)
class _CompressedRecord:
    total_out: int
    executions: tuple[CrossPoolExecution, ...]


@dataclass(frozen=True)
class _FullRecord:
    total_out: int


@dataclass(frozen=True)
class _KCompressedRecord:
    total_out: int
    executions: tuple[KPoolExecution, ...]


def _require_int(value: object, *, name: str) -> int:
    if not is_strict_int(value):
        raise ValueError(f"{name} must be an int")
    return int(value)


def _require_positive_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out <= 0:
        raise ValueError(f"{name} must be positive")
    return out


def _require_nonnegative_int(value: object, *, name: str) -> int:
    out = _require_int(value, name=name)
    if out < 0:
        raise ValueError(f"{name} must be non-negative")
    return out


def _validate_pool(pool: TwoPoolCPMM, *, name: str) -> TwoPoolCPMM:
    x = _require_positive_int(pool.x, name=f"{name}.x")
    y = _require_positive_int(pool.y, name=f"{name}.y")
    fee_bps = _require_int(pool.fee_bps, name=f"{name}.fee_bps")
    if not 0 <= fee_bps <= 10_000:
        raise ValueError(f"{name}.fee_bps out of range")
    return TwoPoolCPMM(x=x, y=y, fee_bps=fee_bps)


def _normalize_intents(intents: Iterable[int], *, limits: SubsetDPLimits) -> tuple[int, ...]:
    out = tuple(_require_positive_int(v, name="intent amount") for v in intents)
    if len(out) > int(limits.max_intents):
        raise ValueError("intent count exceeds SubsetDPLimits.max_intents")
    if sum(out) > int(limits.max_total_input):
        raise ValueError("total input exceeds SubsetDPLimits.max_total_input")
    return out


def _normalize_pools(pools: Iterable[TwoPoolCPMM], *, limits: SubsetDPLimits) -> tuple[TwoPoolCPMM, ...]:
    out = tuple(_validate_pool(pool, name=f"pools[{idx}]") for idx, pool in enumerate(pools))
    if len(out) < 2:
        raise ValueError("at least two pools are required")
    if len(out) > int(limits.max_pools):
        raise ValueError("pool count exceeds SubsetDPLimits.max_pools")
    return out


def _kway_splits(total: int, parts: int) -> Iterable[tuple[int, ...]]:
    if parts <= 0:
        raise ValueError("parts must be positive")
    if parts == 1:
        yield (int(total),)
        return
    for head in range(0, int(total) + 1):
        for tail in _kway_splits(int(total) - int(head), int(parts) - 1):
            yield (int(head),) + tail


def cpmm_exact_in_output_allow_zero(pool: TwoPoolCPMM, amount_in: int) -> int:
    """Return CPMM v8 exact-in output, allowing zero-output advisory legs."""

    p = _validate_pool(pool, name="pool")
    amount = _require_nonnegative_int(amount_in, name="amount_in")
    return _cpmm_exact_in_output_raw(int(p.x), int(p.y), int(p.fee_bps), int(amount))


def _cpmm_exact_in_output_raw(x: int, y: int, fee_bps: int, amount_in: int) -> int:
    if x <= 0 or y <= 0:
        raise ValueError("pool reserves must be positive")
    if not 0 <= fee_bps <= BPS_DENOM:
        raise ValueError("fee_bps out of range")
    amount = int(amount_in)
    if amount <= 0:
        return 0
    fee = (amount * int(fee_bps) + BPS_DENOM - 1) // BPS_DENOM
    net = int(amount) - int(fee)
    if net <= 0:
        return 0
    return int((int(y) * int(net)) // (int(x) + int(net)))


def _outputs_for_split(
    *,
    amount_in_total: int,
    x0: int,
    y0: int,
    fee0_bps: int,
    x1: int,
    y1: int,
    fee1_bps: int,
    split_to_pool0: int,
) -> tuple[int, int]:
    amount0 = int(split_to_pool0)
    amount1 = int(amount_in_total) - amount0
    out0 = _cpmm_exact_in_output_raw(int(x0), int(y0), int(fee0_bps), amount0)
    out1 = _cpmm_exact_in_output_raw(int(x1), int(y1), int(fee1_bps), amount1)
    return int(out0), int(out1)


def _execution_for_split(
    *,
    intent_index: int,
    amount_in_total: int,
    x0: int,
    y0: int,
    fee0_bps: int,
    x1: int,
    y1: int,
    fee1_bps: int,
    split_to_pool0: int,
) -> CrossPoolExecution:
    amount0 = int(split_to_pool0)
    amount1 = int(amount_in_total) - amount0
    out0, out1 = _outputs_for_split(
        amount_in_total=int(amount_in_total),
        x0=int(x0),
        y0=int(y0),
        fee0_bps=int(fee0_bps),
        x1=int(x1),
        y1=int(y1),
        fee1_bps=int(fee1_bps),
        split_to_pool0=int(split_to_pool0),
    )
    return CrossPoolExecution(
        intent_index=int(intent_index),
        amount_in_total=int(amount_in_total),
        amount_in_0=int(amount0),
        amount_out_0=int(out0),
        amount_in_1=int(amount1),
        amount_out_1=int(out1),
    )


def _check_subset_state_limit(dp_size: int, limits: SubsetDPLimits) -> None:
    if int(dp_size) > int(limits.max_states_per_subset):
        raise ValueError("subset state count exceeds SubsetDPLimits.max_states_per_subset")


def solve_two_pool_cpmm_subset_dp(
    pool0: TwoPoolCPMM,
    pool1: TwoPoolCPMM,
    intents: Iterable[int],
    *,
    limits: SubsetDPLimits = SubsetDPLimits(),
    trace_mode: str = "path",
) -> CrossPoolBatchResult:
    """Solve the modeled two-pool batch exactly by compressed subset DP."""

    mode = str(trace_mode).strip().lower()
    if mode not in {"path", "none"}:
        raise ValueError("trace_mode must be 'path' or 'none'")
    p0 = _validate_pool(pool0, name="pool0")
    p1 = _validate_pool(pool1, name="pool1")
    intent_amounts = _normalize_intents(intents, limits=limits)
    n = len(intent_amounts)
    if n == 0:
        return CrossPoolBatchResult(0, tuple(), 1, 1, 1, 0, 1)

    dp: list[dict[tuple[int, int], _CompressedRecord]] = [dict() for _ in range(1 << n)]
    dp[0][(0, int(p0.y))] = _CompressedRecord(total_out=0, executions=tuple())
    max_states = 1
    states_visited = 1
    transitions_evaluated = 0

    for subset in range(1 << n):
        states = dp[subset]
        if not states:
            continue
        max_states = max(max_states, len(states))
        _check_subset_state_limit(len(states), limits)
        processed_input = sum(intent_amounts[i] for i in range(n) if subset & (1 << i))
        for intent_index, amount_in_total in enumerate(intent_amounts):
            if subset & (1 << intent_index):
                continue
            next_subset = subset | (1 << intent_index)
            for (amount_to_pool0_so_far, y0r), record in tuple(states.items()):
                x0r = int(p0.x) + int(amount_to_pool0_so_far)
                x1r = int(p1.x) + int(processed_input) - int(amount_to_pool0_so_far)
                y1r = int(p1.y) - int(record.total_out) + (int(p0.y) - int(y0r))
                for split_to_pool0 in range(0, int(amount_in_total) + 1):
                    transitions_evaluated += 1
                    out0, out1 = _outputs_for_split(
                        amount_in_total=int(amount_in_total),
                        x0=x0r,
                        y0=int(y0r),
                        fee0_bps=int(p0.fee_bps),
                        x1=x1r,
                        y1=y1r,
                        fee1_bps=int(p1.fee_bps),
                        split_to_pool0=int(split_to_pool0),
                    )
                    next_key = (
                        int(amount_to_pool0_so_far) + int(split_to_pool0),
                        int(y0r) - int(out0),
                    )
                    next_total = int(record.total_out) + int(out0) + int(out1)
                    current = dp[next_subset].get(next_key)
                    if current is None or next_total > int(current.total_out):
                        if mode == "path":
                            amount0 = int(split_to_pool0)
                            execution = CrossPoolExecution(
                                intent_index=int(intent_index),
                                amount_in_total=int(amount_in_total),
                                amount_in_0=amount0,
                                amount_out_0=int(out0),
                                amount_in_1=int(amount_in_total) - amount0,
                                amount_out_1=int(out1),
                            )
                            executions = record.executions + (execution,)
                        else:
                            executions = tuple()
                        dp[next_subset][next_key] = _CompressedRecord(
                            total_out=next_total,
                            executions=executions,
                        )
            _check_subset_state_limit(len(dp[next_subset]), limits)

    final = dp[(1 << n) - 1]
    states_visited = sum(len(states) for states in dp)
    max_states = max(max_states, len(final))
    if not final:
        raise ValueError("no reachable final state")
    best = max(final.values(), key=lambda rec: int(rec.total_out))
    return CrossPoolBatchResult(
        amount_out_total=int(best.total_out),
        executions=best.executions,
        max_states_per_subset=int(max_states),
        final_state_count=int(len(final)),
        states_visited=int(states_visited),
        transitions_evaluated=int(transitions_evaluated),
        ordering_count_upper_bound=int(factorial(n)),
    )


def solve_two_pool_cpmm_multiset_dp(
    pool0: TwoPoolCPMM,
    pool1: TwoPoolCPMM,
    intents: Iterable[int],
    *,
    limits: SubsetDPLimits = SubsetDPLimits(),
    trace_mode: str = "path",
) -> CrossPoolBatchResult:
    """Solve exactly after quotienting interchangeable equal-amount intents.

    Intents with the same exact-in amount are interchangeable in this model:
    the CPMM output function depends on the amount and current reserves, not on
    the identity of the intent that supplied that amount. The DP state replaces
    the subset bitmask with per-amount usage counts.
    """

    mode = str(trace_mode).strip().lower()
    if mode not in {"path", "none"}:
        raise ValueError("trace_mode must be 'path' or 'none'")
    p0 = _validate_pool(pool0, name="pool0")
    p1 = _validate_pool(pool1, name="pool1")
    intent_amounts = _normalize_intents(intents, limits=limits)
    n = len(intent_amounts)
    if n == 0:
        return CrossPoolBatchResult(0, tuple(), 1, 1, 1, 0, 1)

    grouped_indices: dict[int, list[int]] = {}
    for intent_index, amount in enumerate(intent_amounts):
        grouped_indices.setdefault(int(amount), []).append(int(intent_index))
    amount_classes = tuple(sorted(grouped_indices))
    group_sizes = tuple(len(grouped_indices[amount]) for amount in amount_classes)
    zero_counts = tuple(0 for _ in amount_classes)
    final_counts = tuple(int(v) for v in group_sizes)

    dp: dict[tuple[int, ...], dict[tuple[int, int], _CompressedRecord]] = {
        zero_counts: {(0, int(p0.y)): _CompressedRecord(total_out=0, executions=tuple())}
    }
    max_states = 1
    transitions_evaluated = 0

    for depth in range(n):
        count_states = [counts for counts in dp if sum(counts) == depth]
        for counts in count_states:
            states = dp[counts]
            if not states:
                continue
            max_states = max(max_states, len(states))
            _check_subset_state_limit(len(states), limits)
            processed_input = sum(int(amount_classes[i]) * int(counts[i]) for i in range(len(amount_classes)))
            for class_index, amount_in_total in enumerate(amount_classes):
                used_count = int(counts[class_index])
                if used_count >= int(group_sizes[class_index]):
                    continue
                next_counts_list = list(counts)
                next_counts_list[class_index] = used_count + 1
                next_counts = tuple(next_counts_list)
                next_states = dp.setdefault(next_counts, {})
                intent_index = int(grouped_indices[int(amount_in_total)][used_count])

                for (amount_to_pool0_so_far, y0r), record in tuple(states.items()):
                    x0r = int(p0.x) + int(amount_to_pool0_so_far)
                    x1r = int(p1.x) + int(processed_input) - int(amount_to_pool0_so_far)
                    y1r = int(p1.y) - int(record.total_out) + (int(p0.y) - int(y0r))
                    for split_to_pool0 in range(0, int(amount_in_total) + 1):
                        transitions_evaluated += 1
                        out0, out1 = _outputs_for_split(
                            amount_in_total=int(amount_in_total),
                            x0=x0r,
                            y0=int(y0r),
                            fee0_bps=int(p0.fee_bps),
                            x1=x1r,
                            y1=y1r,
                            fee1_bps=int(p1.fee_bps),
                            split_to_pool0=int(split_to_pool0),
                        )
                        next_key = (
                            int(amount_to_pool0_so_far) + int(split_to_pool0),
                            int(y0r) - int(out0),
                        )
                        next_total = int(record.total_out) + int(out0) + int(out1)
                        current = next_states.get(next_key)
                        if current is None or next_total > int(current.total_out):
                            if mode == "path":
                                amount0 = int(split_to_pool0)
                                execution = CrossPoolExecution(
                                    intent_index=int(intent_index),
                                    amount_in_total=int(amount_in_total),
                                    amount_in_0=amount0,
                                    amount_out_0=int(out0),
                                    amount_in_1=int(amount_in_total) - amount0,
                                    amount_out_1=int(out1),
                                )
                                executions = record.executions + (execution,)
                            else:
                                executions = tuple()
                            next_states[next_key] = _CompressedRecord(
                                total_out=next_total,
                                executions=executions,
                            )
                _check_subset_state_limit(len(next_states), limits)

    final = dp[final_counts]
    states_visited = sum(len(states) for states in dp.values())
    max_states = max(max_states, len(final))
    if not final:
        raise ValueError("no reachable final state")
    best = max(final.values(), key=lambda rec: int(rec.total_out))
    distinct_ordering_count = factorial(n)
    for count in group_sizes:
        distinct_ordering_count //= factorial(int(count))
    return CrossPoolBatchResult(
        amount_out_total=int(best.total_out),
        executions=best.executions,
        max_states_per_subset=int(max_states),
        final_state_count=int(len(final)),
        states_visited=int(states_visited),
        transitions_evaluated=int(transitions_evaluated),
        ordering_count_upper_bound=int(distinct_ordering_count),
    )


def solve_k_pool_cpmm_subset_dp(
    pools: Iterable[TwoPoolCPMM],
    intents: Iterable[int],
    *,
    limits: SubsetDPLimits = SubsetDPLimits(),
    trace_mode: str = "path",
) -> KPoolBatchResult:
    """Solve same-direction exact-in routing across k CPMM pools exactly.

    The compressed state stores each non-hidden pool's cumulative input and
    output reserve. The final pool is derived by conservation from total
    processed input, known-pool drained output, and banked total output.
    """

    mode = str(trace_mode).strip().lower()
    if mode not in {"path", "none"}:
        raise ValueError("trace_mode must be 'path' or 'none'")
    pool_tuple = _normalize_pools(pools, limits=limits)
    intent_amounts = _normalize_intents(intents, limits=limits)
    k = len(pool_tuple)
    n = len(intent_amounts)
    if n == 0:
        return KPoolBatchResult(0, tuple(), k, 1, 1, 1, 0, 1)

    initial_state = tuple([0] * (k - 1) + [int(pool_tuple[i].y) for i in range(k - 1)])
    dp: list[dict[tuple[int, ...], _KCompressedRecord]] = [dict() for _ in range(1 << n)]
    dp[0][initial_state] = _KCompressedRecord(total_out=0, executions=tuple())
    max_states = 1
    transitions_evaluated = 0

    for subset in range(1 << n):
        states = dp[subset]
        if not states:
            continue
        max_states = max(max_states, len(states))
        _check_subset_state_limit(len(states), limits)
        processed_input = sum(intent_amounts[i] for i in range(n) if subset & (1 << i))
        for intent_index, amount_in_total in enumerate(intent_amounts):
            if subset & (1 << intent_index):
                continue
            next_subset = subset | (1 << intent_index)
            for state, record in tuple(states.items()):
                known_inputs = tuple(int(v) for v in state[: k - 1])
                known_y_reserves = tuple(int(v) for v in state[k - 1 :])
                hidden_input = int(processed_input) - sum(known_inputs)
                known_drained_output = sum(
                    int(pool_tuple[i].y) - int(known_y_reserves[i]) for i in range(k - 1)
                )
                hidden_y_reserve = (
                    int(pool_tuple[k - 1].y) - int(record.total_out) + int(known_drained_output)
                )
                x_reserves = tuple(
                    int(pool_tuple[i].x) + int(known_inputs[i]) for i in range(k - 1)
                ) + (int(pool_tuple[k - 1].x) + int(hidden_input),)
                y_reserves = known_y_reserves + (int(hidden_y_reserve),)

                for allocation in _kway_splits(int(amount_in_total), k):
                    transitions_evaluated += 1
                    outputs = tuple(
                        _cpmm_exact_in_output_raw(
                            int(x_reserves[i]),
                            int(y_reserves[i]),
                            int(pool_tuple[i].fee_bps),
                            int(allocation[i]),
                        )
                        for i in range(k)
                    )
                    next_known_inputs = tuple(
                        int(known_inputs[i]) + int(allocation[i]) for i in range(k - 1)
                    )
                    next_known_y_reserves = tuple(
                        int(known_y_reserves[i]) - int(outputs[i]) for i in range(k - 1)
                    )
                    next_key = next_known_inputs + next_known_y_reserves
                    next_total = int(record.total_out) + sum(int(v) for v in outputs)
                    current = dp[next_subset].get(next_key)
                    if current is None or next_total > int(current.total_out):
                        if mode == "path":
                            execution = KPoolExecution(
                                intent_index=int(intent_index),
                                amount_in_total=int(amount_in_total),
                                amount_in_by_pool=tuple(int(v) for v in allocation),
                                amount_out_by_pool=tuple(int(v) for v in outputs),
                            )
                            executions = record.executions + (execution,)
                        else:
                            executions = tuple()
                        dp[next_subset][next_key] = _KCompressedRecord(
                            total_out=int(next_total),
                            executions=executions,
                        )
            _check_subset_state_limit(len(dp[next_subset]), limits)

    final = dp[(1 << n) - 1]
    states_visited = sum(len(states) for states in dp)
    max_states = max(max_states, len(final))
    if not final:
        raise ValueError("no reachable final state")
    best = max(final.values(), key=lambda rec: int(rec.total_out))
    return KPoolBatchResult(
        amount_out_total=int(best.total_out),
        executions=best.executions,
        pool_count=int(k),
        max_states_per_subset=int(max_states),
        final_state_count=int(len(final)),
        states_visited=int(states_visited),
        transitions_evaluated=int(transitions_evaluated),
        ordering_count_upper_bound=int(factorial(n)),
    )


def solve_k_pool_cpmm_multiset_dp(
    pools: Iterable[TwoPoolCPMM],
    intents: Iterable[int],
    *,
    limits: SubsetDPLimits = SubsetDPLimits(),
    trace_mode: str = "path",
) -> KPoolBatchResult:
    """Solve k-pool exact-in routing after quotienting equal-amount intents.

    Equal exact-in amounts are interchangeable in this modeled oracle: the
    transition relation depends on the amount, current reserves, and pool fees,
    not on intent identity. The state therefore tracks how many intents of each
    distinct amount have been processed instead of tracking a full subset
    bitmask. This is still exponential in the number of distinct amount classes
    and pseudo-polynomial in the split domain.
    """

    mode = str(trace_mode).strip().lower()
    if mode not in {"path", "none"}:
        raise ValueError("trace_mode must be 'path' or 'none'")
    pool_tuple = _normalize_pools(pools, limits=limits)
    intent_amounts = _normalize_intents(intents, limits=limits)
    k = len(pool_tuple)
    n = len(intent_amounts)
    if n == 0:
        return KPoolBatchResult(0, tuple(), k, 1, 1, 1, 0, 1)

    grouped_indices: dict[int, list[int]] = {}
    for intent_index, amount in enumerate(intent_amounts):
        grouped_indices.setdefault(int(amount), []).append(int(intent_index))
    amount_classes = tuple(sorted(grouped_indices))
    group_sizes = tuple(len(grouped_indices[amount]) for amount in amount_classes)
    zero_counts = tuple(0 for _ in amount_classes)
    final_counts = tuple(int(v) for v in group_sizes)

    initial_state = tuple([0] * (k - 1) + [int(pool_tuple[i].y) for i in range(k - 1)])
    dp: dict[tuple[int, ...], dict[tuple[int, ...], _KCompressedRecord]] = {
        zero_counts: {initial_state: _KCompressedRecord(total_out=0, executions=tuple())}
    }
    max_states = 1
    transitions_evaluated = 0

    for depth in range(n):
        count_states = [counts for counts in tuple(dp) if sum(counts) == depth]
        for counts in count_states:
            states = dp[counts]
            if not states:
                continue
            max_states = max(max_states, len(states))
            _check_subset_state_limit(len(states), limits)
            processed_input = sum(int(amount_classes[i]) * int(counts[i]) for i in range(len(amount_classes)))
            for class_index, amount_in_total in enumerate(amount_classes):
                used_count = int(counts[class_index])
                if used_count >= int(group_sizes[class_index]):
                    continue
                next_counts_list = list(counts)
                next_counts_list[class_index] = used_count + 1
                next_counts = tuple(next_counts_list)
                next_states = dp.setdefault(next_counts, {})
                intent_index = int(grouped_indices[int(amount_in_total)][used_count])

                for state, record in tuple(states.items()):
                    known_inputs = tuple(int(v) for v in state[: k - 1])
                    known_y_reserves = tuple(int(v) for v in state[k - 1 :])
                    hidden_input = int(processed_input) - sum(known_inputs)
                    known_drained_output = sum(
                        int(pool_tuple[i].y) - int(known_y_reserves[i]) for i in range(k - 1)
                    )
                    hidden_y_reserve = (
                        int(pool_tuple[k - 1].y) - int(record.total_out) + int(known_drained_output)
                    )
                    x_reserves = tuple(
                        int(pool_tuple[i].x) + int(known_inputs[i]) for i in range(k - 1)
                    ) + (int(pool_tuple[k - 1].x) + int(hidden_input),)
                    y_reserves = known_y_reserves + (int(hidden_y_reserve),)

                    for allocation in _kway_splits(int(amount_in_total), k):
                        transitions_evaluated += 1
                        outputs = tuple(
                            _cpmm_exact_in_output_raw(
                                int(x_reserves[i]),
                                int(y_reserves[i]),
                                int(pool_tuple[i].fee_bps),
                                int(allocation[i]),
                            )
                            for i in range(k)
                        )
                        next_known_inputs = tuple(
                            int(known_inputs[i]) + int(allocation[i]) for i in range(k - 1)
                        )
                        next_known_y_reserves = tuple(
                            int(known_y_reserves[i]) - int(outputs[i]) for i in range(k - 1)
                        )
                        next_key = next_known_inputs + next_known_y_reserves
                        next_total = int(record.total_out) + sum(int(v) for v in outputs)
                        current = next_states.get(next_key)
                        if current is None or next_total > int(current.total_out):
                            if mode == "path":
                                execution = KPoolExecution(
                                    intent_index=int(intent_index),
                                    amount_in_total=int(amount_in_total),
                                    amount_in_by_pool=tuple(int(v) for v in allocation),
                                    amount_out_by_pool=tuple(int(v) for v in outputs),
                                )
                                executions = record.executions + (execution,)
                            else:
                                executions = tuple()
                            next_states[next_key] = _KCompressedRecord(
                                total_out=int(next_total),
                                executions=executions,
                            )
                _check_subset_state_limit(len(next_states), limits)

    final = dp[final_counts]
    states_visited = sum(len(states) for states in dp.values())
    max_states = max(max_states, len(final))
    if not final:
        raise ValueError("no reachable final state")
    best = max(final.values(), key=lambda rec: int(rec.total_out))
    distinct_ordering_count = factorial(n)
    for count in group_sizes:
        distinct_ordering_count //= factorial(int(count))
    return KPoolBatchResult(
        amount_out_total=int(best.total_out),
        executions=best.executions,
        pool_count=int(k),
        max_states_per_subset=int(max_states),
        final_state_count=int(len(final)),
        states_visited=int(states_visited),
        transitions_evaluated=int(transitions_evaluated),
        ordering_count_upper_bound=int(distinct_ordering_count),
    )


def solve_two_pool_cpmm_full_state_dp(
    pool0: TwoPoolCPMM,
    pool1: TwoPoolCPMM,
    intents: Iterable[int],
    *,
    limits: SubsetDPLimits = SubsetDPLimits(max_intents=12, max_total_input=20_000, max_states_per_subset=500_000),
) -> CrossPoolBatchResult:
    """Reference subset DP that keeps y1 reserve in the state."""

    p0 = _validate_pool(pool0, name="pool0")
    p1 = _validate_pool(pool1, name="pool1")
    intent_amounts = _normalize_intents(intents, limits=limits)
    n = len(intent_amounts)
    if n == 0:
        return CrossPoolBatchResult(0, tuple(), 1, 1, 1, 0, 1, 0)

    dp: list[dict[tuple[int, int, int], _FullRecord]] = [dict() for _ in range(1 << n)]
    dp[0][(0, int(p0.y), int(p1.y))] = _FullRecord(total_out=0)
    max_states = 1
    max_compressed_collision = 1
    transitions_evaluated = 0

    for subset in range(1 << n):
        states = dp[subset]
        if not states:
            continue
        max_states = max(max_states, len(states))
        _check_subset_state_limit(len(states), limits)
        by_compressed: dict[tuple[int, int], int] = {}
        for amount_to_pool0_so_far, y0r, _y1r in states:
            key = (int(amount_to_pool0_so_far), int(y0r))
            by_compressed[key] = int(by_compressed.get(key, 0)) + 1
        max_compressed_collision = max(max_compressed_collision, max(by_compressed.values(), default=1))
        processed_input = sum(intent_amounts[i] for i in range(n) if subset & (1 << i))
        for intent_index, amount_in_total in enumerate(intent_amounts):
            if subset & (1 << intent_index):
                continue
            next_subset = subset | (1 << intent_index)
            for (amount_to_pool0_so_far, y0r, y1r), record in tuple(states.items()):
                x0r = int(p0.x) + int(amount_to_pool0_so_far)
                x1r = int(p1.x) + int(processed_input) - int(amount_to_pool0_so_far)
                for split_to_pool0 in range(0, int(amount_in_total) + 1):
                    transitions_evaluated += 1
                    out0, out1 = _outputs_for_split(
                        amount_in_total=int(amount_in_total),
                        x0=x0r,
                        y0=int(y0r),
                        fee0_bps=int(p0.fee_bps),
                        x1=x1r,
                        y1=int(y1r),
                        fee1_bps=int(p1.fee_bps),
                        split_to_pool0=int(split_to_pool0),
                    )
                    next_key = (
                        int(amount_to_pool0_so_far) + int(split_to_pool0),
                        int(y0r) - int(out0),
                        int(y1r) - int(out1),
                    )
                    next_total = int(record.total_out) + int(out0) + int(out1)
                    current = dp[next_subset].get(next_key)
                    if current is None or next_total > int(current.total_out):
                        dp[next_subset][next_key] = _FullRecord(total_out=next_total)
            _check_subset_state_limit(len(dp[next_subset]), limits)

    final = dp[(1 << n) - 1]
    states_visited = sum(len(states) for states in dp)
    max_states = max(max_states, len(final))
    if not final:
        raise ValueError("no reachable final state")
    best = max(final.values(), key=lambda rec: int(rec.total_out))
    return CrossPoolBatchResult(
        amount_out_total=int(best.total_out),
        executions=tuple(),
        max_states_per_subset=int(max_states),
        final_state_count=int(len(final)),
        states_visited=int(states_visited),
        transitions_evaluated=int(transitions_evaluated),
        ordering_count_upper_bound=int(factorial(n)),
        max_compressed_collision=int(max_compressed_collision),
    )


def brute_force_two_pool_cpmm_batch(
    pool0: TwoPoolCPMM,
    pool1: TwoPoolCPMM,
    intents: Iterable[int],
) -> CrossPoolBatchResult:
    """Factorial reference oracle for small cases: all orderings and splits."""

    p0 = _validate_pool(pool0, name="pool0")
    p1 = _validate_pool(pool1, name="pool1")
    intent_amounts = _normalize_intents(intents, limits=SubsetDPLimits(max_intents=8, max_total_input=256))
    n = len(intent_amounts)
    best_total = -1
    best_path: tuple[CrossPoolExecution, ...] = tuple()
    transitions_evaluated = 0

    def search(
        ordered_indices: tuple[int, ...],
        k: int,
        x0r: int,
        y0r: int,
        x1r: int,
        y1r: int,
        total_out: int,
        path: tuple[CrossPoolExecution, ...],
    ) -> None:
        nonlocal best_total, best_path, transitions_evaluated
        if k == len(ordered_indices):
            if int(total_out) > int(best_total):
                best_total = int(total_out)
                best_path = path
            return
        intent_index = ordered_indices[k]
        amount_in_total = intent_amounts[intent_index]
        for split_to_pool0 in range(0, int(amount_in_total) + 1):
            transitions_evaluated += 1
            execution = _execution_for_split(
                intent_index=intent_index,
                amount_in_total=int(amount_in_total),
                x0=x0r,
                y0=y0r,
                fee0_bps=int(p0.fee_bps),
                x1=x1r,
                y1=y1r,
                fee1_bps=int(p1.fee_bps),
                split_to_pool0=int(split_to_pool0),
            )
            search(
                ordered_indices,
                k + 1,
                x0r + int(execution.amount_in_0),
                y0r - int(execution.amount_out_0),
                x1r + int(execution.amount_in_1),
                y1r - int(execution.amount_out_1),
                total_out + int(execution.amount_out_0) + int(execution.amount_out_1),
                path + (execution,),
            )

    for perm in permutations(range(n)):
        search(perm, 0, int(p0.x), int(p0.y), int(p1.x), int(p1.y), 0, tuple())

    if best_total < 0:
        best_total = 0
    return CrossPoolBatchResult(
        amount_out_total=int(best_total),
        executions=best_path,
        max_states_per_subset=0,
        final_state_count=0,
        states_visited=0,
        transitions_evaluated=int(transitions_evaluated),
        ordering_count_upper_bound=int(factorial(n)),
    )


def brute_force_k_pool_cpmm_batch(
    pools: Iterable[TwoPoolCPMM],
    intents: Iterable[int],
    *,
    limits: SubsetDPLimits = SubsetDPLimits(max_intents=7, max_total_input=256, max_pools=5),
) -> KPoolBatchResult:
    """Factorial reference oracle for small k-pool cases."""

    pool_tuple = _normalize_pools(pools, limits=limits)
    intent_amounts = _normalize_intents(intents, limits=limits)
    k = len(pool_tuple)
    n = len(intent_amounts)
    best_total = -1
    best_path: tuple[KPoolExecution, ...] = tuple()
    transitions_evaluated = 0

    def search(
        ordered_indices: tuple[int, ...],
        step: int,
        x_reserves: tuple[int, ...],
        y_reserves: tuple[int, ...],
        total_out: int,
        path: tuple[KPoolExecution, ...],
    ) -> None:
        nonlocal best_total, best_path, transitions_evaluated
        if step == len(ordered_indices):
            if int(total_out) > int(best_total):
                best_total = int(total_out)
                best_path = path
            return
        intent_index = int(ordered_indices[step])
        amount_in_total = int(intent_amounts[intent_index])
        for allocation in _kway_splits(amount_in_total, k):
            transitions_evaluated += 1
            outputs = tuple(
                _cpmm_exact_in_output_raw(
                    int(x_reserves[i]),
                    int(y_reserves[i]),
                    int(pool_tuple[i].fee_bps),
                    int(allocation[i]),
                )
                for i in range(k)
            )
            execution = KPoolExecution(
                intent_index=int(intent_index),
                amount_in_total=int(amount_in_total),
                amount_in_by_pool=tuple(int(v) for v in allocation),
                amount_out_by_pool=tuple(int(v) for v in outputs),
            )
            search(
                ordered_indices,
                step + 1,
                tuple(int(x_reserves[i]) + int(allocation[i]) for i in range(k)),
                tuple(int(y_reserves[i]) - int(outputs[i]) for i in range(k)),
                int(total_out) + sum(int(v) for v in outputs),
                path + (execution,),
            )

    for perm in permutations(range(n)):
        search(
            perm,
            0,
            tuple(int(pool.x) for pool in pool_tuple),
            tuple(int(pool.y) for pool in pool_tuple),
            0,
            tuple(),
        )

    if best_total < 0:
        best_total = 0
    return KPoolBatchResult(
        amount_out_total=int(best_total),
        executions=best_path,
        pool_count=int(k),
        max_states_per_subset=0,
        final_state_count=0,
        states_visited=0,
        transitions_evaluated=int(transitions_evaluated),
        ordering_count_upper_bound=int(factorial(n)),
    )


def replay_two_pool_cpmm_executions(
    pool0: TwoPoolCPMM,
    pool1: TwoPoolCPMM,
    executions: Iterable[CrossPoolExecution],
) -> int:
    """Replay a proposed execution sequence and return total output."""

    p0 = _validate_pool(pool0, name="pool0")
    p1 = _validate_pool(pool1, name="pool1")
    x0r, y0r = int(p0.x), int(p0.y)
    x1r, y1r = int(p1.x), int(p1.y)
    total_out = 0
    for execution in executions:
        if int(execution.amount_in_0) + int(execution.amount_in_1) != int(execution.amount_in_total):
            raise ValueError("execution split does not sum to amount_in_total")
        out0 = cpmm_exact_in_output_allow_zero(
            TwoPoolCPMM(x=x0r, y=y0r, fee_bps=int(p0.fee_bps)),
            int(execution.amount_in_0),
        )
        out1 = cpmm_exact_in_output_allow_zero(
            TwoPoolCPMM(x=x1r, y=y1r, fee_bps=int(p1.fee_bps)),
            int(execution.amount_in_1),
        )
        if int(out0) != int(execution.amount_out_0) or int(out1) != int(execution.amount_out_1):
            raise ValueError("execution outputs do not match CPMM replay")
        x0r += int(execution.amount_in_0)
        y0r -= int(out0)
        x1r += int(execution.amount_in_1)
        y1r -= int(out1)
        total_out += int(out0) + int(out1)
    return int(total_out)


def replay_k_pool_cpmm_executions(
    pools: Iterable[TwoPoolCPMM],
    executions: Iterable[KPoolExecution],
    *,
    limits: SubsetDPLimits = SubsetDPLimits(),
) -> int:
    """Replay a proposed k-pool execution sequence and return total output."""

    pool_tuple = _normalize_pools(pools, limits=limits)
    k = len(pool_tuple)
    x_reserves = [int(pool.x) for pool in pool_tuple]
    y_reserves = [int(pool.y) for pool in pool_tuple]
    total_out = 0
    for execution in executions:
        if len(execution.amount_in_by_pool) != k or len(execution.amount_out_by_pool) != k:
            raise ValueError("execution pool count does not match pools")
        if sum(int(v) for v in execution.amount_in_by_pool) != int(execution.amount_in_total):
            raise ValueError("execution allocation does not sum to amount_in_total")
        outputs: list[int] = []
        for pool_index, amount_in in enumerate(execution.amount_in_by_pool):
            out = cpmm_exact_in_output_allow_zero(
                TwoPoolCPMM(
                    x=int(x_reserves[pool_index]),
                    y=int(y_reserves[pool_index]),
                    fee_bps=int(pool_tuple[pool_index].fee_bps),
                ),
                int(amount_in),
            )
            expected = int(execution.amount_out_by_pool[pool_index])
            if int(out) != expected:
                raise ValueError("execution outputs do not match CPMM replay")
            outputs.append(int(out))
        for pool_index, amount_in in enumerate(execution.amount_in_by_pool):
            x_reserves[pool_index] += int(amount_in)
            y_reserves[pool_index] -= int(outputs[pool_index])
            total_out += int(outputs[pool_index])
    return int(total_out)


def compressed_state_pruning_margin(
    *,
    banked_output_delta: int,
    y_reserve_delta: int,
) -> int:
    """Return the remaining dominance margin for a compressed-state collision.

    If two paths collide on `(subset, a, y0r)`, the retained path has higher
    banked output and lower pool1 y reserve by the same amount. Future pool1
    output advantage for the discarded path cannot exceed its extra y reserve,
    so a non-negative margin is the proof obligation for safe pruning.
    """

    banked = _require_nonnegative_int(banked_output_delta, name="banked_output_delta")
    y_delta = _require_nonnegative_int(y_reserve_delta, name="y_reserve_delta")
    return int(banked) - int(y_delta)
