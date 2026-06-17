from __future__ import annotations

from dataclasses import dataclass
from typing import Sequence

from ...state.pools import PoolState
from .exact_out_many_pool_canonical_domain_v1 import _require_positive_int
from .exact_out_many_pool_prefilter_subset_search_v1 import (
    select_many_pool_cover_search_candidates,
)


@dataclass(frozen=True)
class ExactOutManyPoolRepairedPrefilterSelection:
    strategy: str
    selected_pool_ids: tuple[str, ...]
    current_selected_pool_ids: tuple[str, ...]
    current_selected_matches_full_canonical: bool
    searched_subset_count: int


def select_many_pool_repaired_prefilter_candidates(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> tuple[PoolState, ...]:
    amount_out_total_i = _require_positive_int(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_positive_int(max_candidate_pools, name="max_candidate_pools")
    max_full_domain_pools_i = _require_positive_int(max_full_domain_pools, name="max_full_domain_pools")
    max_enumerated_candidates_i = _require_positive_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    selection = select_many_pool_cover_search_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    pools_by_id = {pool.pool_id: pool for pool in pools}
    return tuple(
        sorted(
            (pools_by_id[pool_id] for pool_id in selection.selected_pool_ids),
            key=lambda pool: pool.pool_id,
        )
    )


def build_many_pool_repaired_prefilter_selection(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolRepairedPrefilterSelection:
    amount_out_total_i = _require_positive_int(amount_out_total, name="amount_out_total")
    max_legs_i = _require_positive_int(max_legs, name="max_legs")
    max_candidate_pools_i = _require_positive_int(max_candidate_pools, name="max_candidate_pools")
    max_full_domain_pools_i = _require_positive_int(max_full_domain_pools, name="max_full_domain_pools")
    max_enumerated_candidates_i = _require_positive_int(
        max_enumerated_candidates,
        name="max_enumerated_candidates",
    )
    selection = select_many_pool_cover_search_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=amount_out_total_i,
        max_legs=max_legs_i,
        max_candidate_pools=max_candidate_pools_i,
        max_full_domain_pools=max_full_domain_pools_i,
        max_enumerated_candidates=max_enumerated_candidates_i,
    )
    return ExactOutManyPoolRepairedPrefilterSelection(
        strategy=str(selection.strategy),
        selected_pool_ids=tuple(selection.selected_pool_ids),
        current_selected_pool_ids=tuple(selection.current_selected_pool_ids),
        current_selected_matches_full_canonical=bool(selection.current_selected_matches_full_canonical),
        searched_subset_count=int(selection.searched_subset_count),
    )
