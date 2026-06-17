from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ...core.domain_limits import is_strict_int
from ...core.split_routing_dispatch import (
    SplitLegExactOutQuote,
    SplitManyPoolsExactOutQuote,
    best_split_many_pools_exact_out_for_pools,
)
from ...state.pools import PoolState
from .exact_out_many_pool_canonical_domain_v1 import (
    ExactOutManyPoolCandidateQuote,
    _require_positive_int,
    build_exact_out_many_pool_selected_domain,
    feasible_exact_out_pools,
    pool_reserves_for_exact_out,
    select_many_pool_audit_candidates,
)
from .exact_out_many_pool_repaired_prefilter_v1 import (
    select_many_pool_repaired_prefilter_candidates,
)

__all__ = (
    "ExactOutManyPoolBoundedRuntimeDomain",
    "bounded_exact_out_many_pool_runtime_domain",
    "enumerate_exact_out_many_pool_candidates",
    "feasible_exact_out_pools",
    "pool_reserves_for_exact_out",
    "select_many_pool_audit_candidates",
)


@dataclass(frozen=True)
class ExactOutManyPoolBoundedRuntimeDomain:
    audit_pool_ids: tuple[str, ...]
    candidates: tuple[SplitManyPoolsExactOutQuote, ...]
    canonical_quote: SplitManyPoolsExactOutQuote
    runtime_quote: SplitManyPoolsExactOutQuote


def _to_core_quote(quote: ExactOutManyPoolCandidateQuote) -> SplitManyPoolsExactOutQuote:
    return SplitManyPoolsExactOutQuote(
        amount_out_total=int(quote.amount_out_total),
        amount_in_total=int(quote.amount_in_total),
        legs=tuple(
            SplitLegExactOutQuote(
                pool_id=leg.pool_id,
                amount_out=int(leg.amount_out),
                amount_in=int(leg.amount_in),
            )
            for leg in quote.legs
        ),
    )


def _require_nonnegative_int(value: object, *, name: str) -> int:
    if not is_strict_int(value) or int(value) < 0:
        raise ValueError(f"{name} must be non-negative")
    return int(value)


def enumerate_exact_out_many_pool_candidates(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[SplitManyPoolsExactOutQuote, ...]:
    amount_out_total_i = _require_positive_int(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_positive_int(max_candidate_pools, name="max_candidate_pools")
    max_full_domain_pools_i = _require_positive_int(max_full_domain_pools, name="max_full_domain_pools")
    max_enumerated_candidates_i = _require_positive_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    try:
        candidate_pools = select_many_pool_repaired_prefilter_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=amount_out_total_i,
            max_legs=max_legs_i,
            max_candidate_pools=max_candidate_pools_i,
            max_full_domain_pools=max_full_domain_pools_i,
            max_enumerated_candidates=max_enumerated_candidates_i,
        )
    except ValueError:
        candidate_pools = select_many_pool_audit_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=amount_out_total_i,
            max_legs=max_legs_i,
            max_candidate_pools=max_candidate_pools_i,
        )
    selected_domain = build_exact_out_many_pool_selected_domain(
        candidate_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    return tuple(_to_core_quote(candidate) for candidate in selected_domain.candidates)


def bounded_exact_out_many_pool_runtime_domain(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_candidates: int = 12,
    max_iters: int = 4096,
    window: int = 64,
    brute_force_max: int = 512,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolBoundedRuntimeDomain:
    amount_out_total_i = _require_positive_int(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_positive_int(max_candidate_pools, name="max_candidate_pools")
    max_candidates_i = _require_positive_int(max_candidates, name="max_candidates")
    max_iters_i = _require_positive_int(max_iters, name="max_iters")
    window_i = _require_nonnegative_int(window, name="window")
    brute_force_max_i = _require_nonnegative_int(brute_force_max, name="brute_force_max")
    max_full_domain_pools_i = _require_positive_int(max_full_domain_pools, name="max_full_domain_pools")
    max_enumerated_candidates_i = _require_positive_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    try:
        audit_pools = select_many_pool_repaired_prefilter_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=amount_out_total_i,
            max_legs=max_legs_i,
            max_candidate_pools=max_candidate_pools_i,
            max_full_domain_pools=max_full_domain_pools_i,
            max_enumerated_candidates=max_enumerated_candidates_i,
        )
    except ValueError:
        audit_pools = select_many_pool_audit_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=amount_out_total_i,
            max_legs=max_legs_i,
            max_candidate_pools=max_candidate_pools_i,
        )
    selected_domain = build_exact_out_many_pool_selected_domain(
        audit_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    runtime_quote = best_split_many_pools_exact_out_for_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidates=max_candidates_i,
        max_iters=max_iters_i,
        window=window_i,
        brute_force_max=brute_force_max_i,
        max_full_domain_pools=max_full_domain_pools_i,
    )
    return ExactOutManyPoolBoundedRuntimeDomain(
        audit_pool_ids=tuple(pool.pool_id for pool in audit_pools),
        candidates=tuple(_to_core_quote(candidate) for candidate in selected_domain.candidates),
        canonical_quote=_to_core_quote(selected_domain.canonical_quote),
        runtime_quote=runtime_quote,
    )
