from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ...state.pools import PoolState
from .exact_out_many_pool_canonical_domain_v1 import (
    ExactOutManyPoolCandidateQuote,
    build_exact_out_many_pool_selected_domain,
    exact_out_many_pool_canonical_key,
    feasible_exact_out_pools,
    select_exact_out_many_pool_canonical_quote,
    select_many_pool_audit_candidates,
)


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterContractionAudit:
    feasible_pool_ids: tuple[str, ...]
    selected_pool_ids: tuple[str, ...]
    full_domain_candidate_count: int
    selected_domain_candidate_count: int
    full_domain_canonical_quote: ExactOutManyPoolCandidateQuote
    selected_domain_canonical_quote: ExactOutManyPoolCandidateQuote
    contraction_holds: bool
    counterexample_quote: ExactOutManyPoolCandidateQuote | None


def audit_exact_out_many_pool_selected_subset_contraction(
    pools: Sequence[PoolState],
    selected_pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolPrefilterContractionAudit:
    if int(max_legs) <= 0:
        raise ValueError("max_legs must be positive")
    if int(max_full_domain_pools) <= 0:
        raise ValueError("max_full_domain_pools must be positive")
    if int(max_enumerated_candidates) <= 0:
        raise ValueError("max_enumerated_candidates must be positive")

    feasible_rows = feasible_exact_out_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
    )
    if not feasible_rows:
        raise ValueError("no feasible pools for exact-out contraction audit")

    feasible_pools = tuple(pool for pool, _cap, _in_i in feasible_rows)
    if len(feasible_pools) > int(max_full_domain_pools):
        raise ValueError("prefilter contraction audit exceeded max_full_domain_pools")

    full_domain = build_exact_out_many_pool_selected_domain(
        feasible_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    selected_domain = build_exact_out_many_pool_selected_domain(
        selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )

    selected_keys = tuple(
        exact_out_many_pool_canonical_key(candidate) for candidate in selected_domain.candidates
    )
    bad_candidates = tuple(
        candidate
        for candidate in full_domain.candidates
        if not any(selected_key <= exact_out_many_pool_canonical_key(candidate) for selected_key in selected_keys)
    )
    counterexample_quote = (
        select_exact_out_many_pool_canonical_quote(bad_candidates)
        if bad_candidates
        else None
    )
    return ExactOutManyPoolPrefilterContractionAudit(
        feasible_pool_ids=tuple(sorted(pool.pool_id for pool in feasible_pools)),
        selected_pool_ids=tuple(sorted(pool.pool_id for pool in selected_pools)),
        full_domain_candidate_count=len(full_domain.candidates),
        selected_domain_candidate_count=len(selected_domain.candidates),
        full_domain_canonical_quote=full_domain.canonical_quote,
        selected_domain_canonical_quote=selected_domain.canonical_quote,
        contraction_holds=(counterexample_quote is None),
        counterexample_quote=counterexample_quote,
    )


def audit_exact_out_many_pool_prefilter_contraction(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolPrefilterContractionAudit:
    if int(max_legs) <= 0:
        raise ValueError("max_legs must be positive")
    if int(max_candidate_pools) <= 0:
        raise ValueError("max_candidate_pools must be positive")
    if int(max_full_domain_pools) <= 0:
        raise ValueError("max_full_domain_pools must be positive")
    if int(max_enumerated_candidates) <= 0:
        raise ValueError("max_enumerated_candidates must be positive")

    selected_pools = select_many_pool_audit_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
    )
    return audit_exact_out_many_pool_selected_subset_contraction(
        pools,
        selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_full_domain_pools=int(max_full_domain_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
