from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Sequence

from ...state.pools import PoolState
from .exact_out_many_pool_canonical_domain_v1 import (
    ExactOutManyPoolCandidateQuote,
    _require_positive_int,
    build_exact_out_many_pool_selected_domain,
    feasible_exact_out_pools,
    select_many_pool_audit_candidates,
)


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterSubsetSearchResult:
    feasible_pool_ids: tuple[str, ...]
    full_domain_canonical_quote: ExactOutManyPoolCandidateQuote
    current_selected_pool_ids: tuple[str, ...]
    current_selected_canonical_quote: ExactOutManyPoolCandidateQuote
    current_selected_matches_full_canonical: bool
    best_cover_subset_ids: tuple[str, ...] | None
    best_cover_canonical_quote: ExactOutManyPoolCandidateQuote | None
    searched_subset_count: int


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterCoverSelection:
    strategy: str
    selected_pool_ids: tuple[str, ...]
    current_selected_pool_ids: tuple[str, ...]
    full_domain_canonical_quote: ExactOutManyPoolCandidateQuote
    selected_domain_canonical_quote: ExactOutManyPoolCandidateQuote
    current_selected_matches_full_canonical: bool
    searched_subset_count: int


def search_exact_out_many_pool_prefilter_subset(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolPrefilterSubsetSearchResult:
    amount_out_total_i = _require_positive_int(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_positive_int(max_candidate_pools, name="max_candidate_pools")
    max_full_domain_pools_i = _require_positive_int(max_full_domain_pools, name="max_full_domain_pools")
    max_enumerated_candidates_i = _require_positive_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )

    feasible_rows = feasible_exact_out_pools(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
    )
    if not feasible_rows:
        raise ValueError("no feasible pools for exact-out subset search")

    feasible_pools = tuple(pool for pool, _cap, _in_i in feasible_rows)
    if len(feasible_pools) > max_full_domain_pools_i:
        raise ValueError("prefilter subset search exceeded max_full_domain_pools")

    full_domain = build_exact_out_many_pool_selected_domain(
        feasible_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )

    current_selected_pools = select_many_pool_audit_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
    )
    current_selected_domain = build_exact_out_many_pool_selected_domain(
        current_selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )

    best_subset_ids: tuple[str, ...] | None = None
    best_subset_canonical_quote: ExactOutManyPoolCandidateQuote | None = None
    searched_subset_count = 0

    full_canonical_quote = full_domain.canonical_quote
    current_matches = current_selected_domain.canonical_quote == full_canonical_quote
    # A subset that omits a leg used by the full-domain winner cannot reproduce
    # that winner. Prune it before rebuilding the selected-domain oracle.
    required_pool_ids = frozenset(leg.pool_id for leg in full_canonical_quote.legs)

    for subset_size in range(1, min(max_candidate_pools_i, len(feasible_pools)) + 1):
        for subset in combinations(feasible_pools, subset_size):
            searched_subset_count += 1
            if int(subset_size) < len(required_pool_ids):
                continue
            subset_pool_ids = {pool.pool_id for pool in subset}
            if not required_pool_ids.issubset(subset_pool_ids):
                continue
            try:
                subset_domain = build_exact_out_many_pool_selected_domain(
                    subset,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=amount_out_total_i,
                    max_legs=max_legs_i,
                    max_enumerated_candidates=max_enumerated_candidates_i,
                )
            except ValueError:
                continue
            if subset_domain.canonical_quote != full_canonical_quote:
                continue
            subset_ids = tuple(subset_domain.selected_pool_ids)
            if best_subset_ids is None or (len(subset_ids), subset_ids) < (len(best_subset_ids), best_subset_ids):
                best_subset_ids = subset_ids
                best_subset_canonical_quote = subset_domain.canonical_quote

    return ExactOutManyPoolPrefilterSubsetSearchResult(
        feasible_pool_ids=tuple(sorted(pool.pool_id for pool in feasible_pools)),
        full_domain_canonical_quote=full_canonical_quote,
        current_selected_pool_ids=tuple(pool.pool_id for pool in current_selected_pools),
        current_selected_canonical_quote=current_selected_domain.canonical_quote,
        current_selected_matches_full_canonical=current_matches,
        best_cover_subset_ids=best_subset_ids,
        best_cover_canonical_quote=best_subset_canonical_quote,
        searched_subset_count=searched_subset_count,
    )


def select_many_pool_cover_search_candidates(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolPrefilterCoverSelection:
    amount_out_total_i = _require_positive_int(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_positive_int(max_candidate_pools, name="max_candidate_pools")
    max_full_domain_pools_i = _require_positive_int(max_full_domain_pools, name="max_full_domain_pools")
    max_enumerated_candidates_i = _require_positive_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    result = search_exact_out_many_pool_prefilter_subset(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )

    if result.best_cover_subset_ids is not None:
        return ExactOutManyPoolPrefilterCoverSelection(
            strategy="bounded_cover_search",
            selected_pool_ids=result.best_cover_subset_ids,
            current_selected_pool_ids=result.current_selected_pool_ids,
            full_domain_canonical_quote=result.full_domain_canonical_quote,
            selected_domain_canonical_quote=result.best_cover_canonical_quote
            or result.full_domain_canonical_quote,
            current_selected_matches_full_canonical=result.current_selected_matches_full_canonical,
            searched_subset_count=result.searched_subset_count,
        )

    return ExactOutManyPoolPrefilterCoverSelection(
        strategy="fallback_current_prefilter",
        selected_pool_ids=result.current_selected_pool_ids,
        current_selected_pool_ids=result.current_selected_pool_ids,
        full_domain_canonical_quote=result.full_domain_canonical_quote,
        selected_domain_canonical_quote=result.current_selected_canonical_quote,
        current_selected_matches_full_canonical=result.current_selected_matches_full_canonical,
        searched_subset_count=result.searched_subset_count,
    )
