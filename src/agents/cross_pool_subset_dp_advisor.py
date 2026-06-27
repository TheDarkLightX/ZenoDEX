"""Advisory wrapper for the exact cross-pool subset-DP oracle.

This module is intentionally outside the settlement path. It turns the exact
research oracle into a bounded UX and research comparison packet: a route can
be compared against the modeled optimum, but this packet never authorizes a
state transition.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Iterable, Literal

from ..core.cross_pool_subset_dp import (
    CrossPoolBatchResult,
    CrossPoolExecution,
    SubsetDPLimits,
    TwoPoolCPMM,
    solve_two_pool_cpmm_multiset_dp,
    solve_two_pool_cpmm_subset_dp,
)
from ..core.domain_limits import is_strict_int

CROSS_POOL_SUBSET_DP_ADVISOR_SCHEMA = "zenodex/agents/cross_pool_subset_dp_advisor/v1"
DEFAULT_ADVISOR_LIMITS = SubsetDPLimits()

AdvisorStatus = Literal["exact_available", "exact_unavailable"]


@dataclass(frozen=True)
class CrossPoolSubsetDPAdvisory:
    """One bounded advisory comparison for a two-pool CPMM batch."""

    status: AdvisorStatus
    reason: str
    exact_available: bool
    solver_kind: str
    pool_count: int
    intent_count: int
    total_input: int
    exact_amount_out_total: int | None
    candidate_amount_out_total: int | None
    missed_output: int | None
    candidate_gap_bps: int | None
    max_states_per_subset: int | None
    final_state_count: int | None
    states_visited: int | None
    transitions_evaluated: int | None
    ordering_count_upper_bound: int | None
    execution_preview: tuple[dict[str, int], ...] = tuple()
    schema: str = CROSS_POOL_SUBSET_DP_ADVISOR_SCHEMA
    production_security_claim: bool = False
    settlement_authority: bool = False
    solver_authorizes_settlement: bool = False

    def to_dict(self) -> dict[str, Any]:
        return {
            "schema": self.schema,
            "status": self.status,
            "reason": self.reason,
            "exact_available": self.exact_available,
            "solver_kind": self.solver_kind,
            "production_security_claim": self.production_security_claim,
            "settlement_authority": self.settlement_authority,
            "solver_authorizes_settlement": self.solver_authorizes_settlement,
            "pool_count": self.pool_count,
            "intent_count": self.intent_count,
            "total_input": self.total_input,
            "exact_amount_out_total": self.exact_amount_out_total,
            "candidate_amount_out_total": self.candidate_amount_out_total,
            "missed_output": self.missed_output,
            "candidate_gap_bps": self.candidate_gap_bps,
            "max_states_per_subset": self.max_states_per_subset,
            "final_state_count": self.final_state_count,
            "states_visited": self.states_visited,
            "transitions_evaluated": self.transitions_evaluated,
            "ordering_count_upper_bound": self.ordering_count_upper_bound,
            "execution_preview": [dict(step) for step in self.execution_preview],
        }


def advise_two_pool_cpmm_batch(
    pool0: TwoPoolCPMM,
    pool1: TwoPoolCPMM,
    intents: Iterable[int],
    *,
    candidate_amount_out_total: int | None = None,
    limits: SubsetDPLimits = DEFAULT_ADVISOR_LIMITS,
    include_execution_preview: bool = False,
) -> CrossPoolSubsetDPAdvisory:
    """Return an exact advisory comparison packet when the bounded solver fits."""

    intent_amounts = tuple(int(v) if is_strict_int(v) else v for v in intents)
    intent_count = len(intent_amounts)
    total_input = sum(int(v) for v in intent_amounts if is_strict_int(v) and int(v) > 0)
    candidate = _normalize_optional_candidate(candidate_amount_out_total)
    trace_mode = "path" if include_execution_preview else "none"
    use_multiset = _has_duplicate_intents(intent_amounts)
    solver_kind = "multiset_dp" if use_multiset else "subset_dp"

    try:
        solver = solve_two_pool_cpmm_multiset_dp if use_multiset else solve_two_pool_cpmm_subset_dp
        result = solver(
            pool0,
            pool1,
            intent_amounts,
            limits=limits,
            trace_mode=trace_mode,
        )
    except (TypeError, ValueError) as exc:
        return CrossPoolSubsetDPAdvisory(
            status="exact_unavailable",
            reason=str(exc),
            exact_available=False,
            solver_kind="unavailable",
            pool_count=2,
            intent_count=int(intent_count),
            total_input=int(total_input),
            exact_amount_out_total=None,
            candidate_amount_out_total=candidate,
            missed_output=None,
            candidate_gap_bps=None,
            max_states_per_subset=None,
            final_state_count=None,
            states_visited=None,
            transitions_evaluated=None,
            ordering_count_upper_bound=None,
        )

    return _available_advisory(
        result=result,
        intent_count=int(intent_count),
        total_input=int(total_input),
        solver_kind=solver_kind,
        candidate_amount_out_total=candidate,
        include_execution_preview=include_execution_preview,
    )


def _available_advisory(
    *,
    result: CrossPoolBatchResult,
    intent_count: int,
    total_input: int,
    solver_kind: str,
    candidate_amount_out_total: int | None,
    include_execution_preview: bool,
) -> CrossPoolSubsetDPAdvisory:
    exact = int(result.amount_out_total)
    if candidate_amount_out_total is None:
        missed_output = None
        gap_bps = None
    else:
        missed_output = max(exact - int(candidate_amount_out_total), 0)
        gap_bps = None if exact == 0 else int((int(missed_output) * 10_000) // exact)

    return CrossPoolSubsetDPAdvisory(
        status="exact_available",
        reason="exact subset-DP advisory comparison computed",
        exact_available=True,
        solver_kind=str(solver_kind),
        pool_count=2,
        intent_count=int(intent_count),
        total_input=int(total_input),
        exact_amount_out_total=exact,
        candidate_amount_out_total=candidate_amount_out_total,
        missed_output=missed_output,
        candidate_gap_bps=gap_bps,
        max_states_per_subset=int(result.max_states_per_subset),
        final_state_count=int(result.final_state_count),
        states_visited=int(result.states_visited),
        transitions_evaluated=int(result.transitions_evaluated),
        ordering_count_upper_bound=int(result.ordering_count_upper_bound),
        execution_preview=_execution_preview(result.executions) if include_execution_preview else tuple(),
    )


def _normalize_optional_candidate(value: int | None) -> int | None:
    if value is None:
        return None
    if not is_strict_int(value):
        raise ValueError("candidate_amount_out_total must be an int")
    candidate = int(value)
    if candidate < 0:
        raise ValueError("candidate_amount_out_total must be non-negative")
    return candidate


def _has_duplicate_intents(intent_amounts: tuple[object, ...]) -> bool:
    seen: set[int] = set()
    for amount in intent_amounts:
        if not is_strict_int(amount):
            return False
        normalized = int(amount)
        if normalized in seen:
            return True
        seen.add(normalized)
    return False


def _execution_preview(executions: tuple[CrossPoolExecution, ...]) -> tuple[dict[str, int], ...]:
    return tuple(
        {
            "intent_index": int(execution.intent_index),
            "amount_in_total": int(execution.amount_in_total),
            "amount_in_0": int(execution.amount_in_0),
            "amount_out_0": int(execution.amount_out_0),
            "amount_in_1": int(execution.amount_in_1),
            "amount_out_1": int(execution.amount_out_1),
        }
        for execution in executions
    )
