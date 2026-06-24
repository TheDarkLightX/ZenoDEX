from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ...core.split_routing_dispatch import (
    SplitLegExactOutQuote,
    SplitManyPoolsExactOutQuote,
    best_split_many_pools_exact_out_for_pools,
)
from .exact_out_many_pool_canonical_domain_v1 import (
    ExactOutManyPoolCandidateQuote,
    build_exact_out_many_pool_selected_domain,
    feasible_exact_out_pools,
    pool_reserves_for_exact_out,
    select_many_pool_audit_candidates,
)
from .exact_out_many_pool_repaired_prefilter_v1 import (
    select_many_pool_repaired_prefilter_candidates,
)
from ...state.pools import PoolState


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
    try:
        candidate_pools = select_many_pool_repaired_prefilter_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_candidate_pools=int(max_candidate_pools),
            max_full_domain_pools=int(max_full_domain_pools),
            max_enumerated_candidates=int(max_enumerated_candidates),
        )
    except (TypeError, ValueError):
        candidate_pools = select_many_pool_audit_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_candidate_pools=int(max_candidate_pools),
        )
    selected_domain = build_exact_out_many_pool_selected_domain(
        candidate_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_enumerated_candidates=int(max_enumerated_candidates),
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
    try:
        audit_pools = select_many_pool_repaired_prefilter_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_candidate_pools=int(max_candidate_pools),
            max_full_domain_pools=int(max_full_domain_pools),
            max_enumerated_candidates=int(max_enumerated_candidates),
        )
    except (TypeError, ValueError):
        audit_pools = select_many_pool_audit_candidates(
            pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_candidate_pools=int(max_candidate_pools),
        )
    selected_domain = build_exact_out_many_pool_selected_domain(
        audit_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    runtime_quote = best_split_many_pools_exact_out_for_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidates=int(max_candidates),
        max_iters=int(max_iters),
        window=int(window),
        brute_force_max=int(brute_force_max),
        max_full_domain_pools=int(max_full_domain_pools),
    )
    return ExactOutManyPoolBoundedRuntimeDomain(
        audit_pool_ids=tuple(pool.pool_id for pool in audit_pools),
        candidates=tuple(_to_core_quote(candidate) for candidate in selected_domain.candidates),
        canonical_quote=_to_core_quote(selected_domain.canonical_quote),
        runtime_quote=runtime_quote,
    )
