from __future__ import annotations

from dataclasses import dataclass
from itertools import combinations
from typing import Callable, Sequence

from ...core.amm_dispatch import swap_exact_out_for_pool
from ...state.pools import PoolState
from .exact_out_many_pool_canonical_domain_v1 import (
    ExactOutManyPoolCandidateQuote,
    build_exact_out_many_pool_selected_domain,
    pool_reserves_for_exact_out,
    select_many_pool_audit_candidates,
)

ProjectedQuotedLeg = tuple[str, int, int]
ProjectedQuotedPath = tuple[ProjectedQuotedLeg, ...]


@dataclass(frozen=True)
class ExactOutManyPoolProjectionCoverAudit:
    selected_pool_ids: tuple[str, ...]
    emitted_candidate_count: int
    emitted_projected_path_count: int
    reachable_projected_path_count: int
    canonical_quote: ExactOutManyPoolCandidateQuote
    canonical_quote_projected_path: ProjectedQuotedPath
    canonical_quote_covered: bool
    sound_holds: bool
    complete_holds: bool
    projection_cover_holds: bool
    extra_emitted_path: ProjectedQuotedPath | None
    missing_reachable_path: ProjectedQuotedPath | None


ExactOutManyPoolCpmmProjectionCoverAudit = ExactOutManyPoolProjectionCoverAudit


def _candidate_to_projected_path(candidate: ExactOutManyPoolCandidateQuote) -> ProjectedQuotedPath:
    return tuple(
        (leg.pool_id, int(leg.amount_out), int(leg.amount_in))
        for leg in candidate.legs
    )


def _sorted_unique_projected_paths(
    paths: set[ProjectedQuotedPath],
) -> tuple[ProjectedQuotedPath, ...]:
    return tuple(sorted(paths))


def _selected_domain_quote_env(
    selected_pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
) -> tuple[tuple[str, ...], dict[str, int], Callable[[str, int], int | None]]:
    pools_by_id = {pool.pool_id: pool for pool in selected_pools}
    pool_ids = tuple(sorted(pools_by_id.keys()))
    if len(pool_ids) != len(selected_pools):
        raise ValueError("selected_pools must not repeat pool_id")

    reserves_by_id: dict[str, tuple[int, int]] = {}
    max_out_by_id: dict[str, int] = {}
    for pool_id in pool_ids:
        reserves = pool_reserves_for_exact_out(
            pools_by_id[pool_id],
            asset_in=asset_in,
            asset_out=asset_out,
        )
        if reserves is None:
            continue
        reserves_by_id[pool_id] = (int(reserves[0]), int(reserves[1]))
        max_out_by_id[pool_id] = max(0, int(reserves[1]) - 1)

    quote_cache: dict[tuple[str, int], int | None] = {}

    def quote_in(pool_id: str, amount_out: int) -> int | None:
        amount_out_i = int(amount_out)
        if amount_out_i <= 0:
            return None
        if amount_out_i > int(max_out_by_id.get(pool_id, 0)):
            return None
        key = (str(pool_id), amount_out_i)
        if key in quote_cache:
            return quote_cache[key]
        reserves = reserves_by_id.get(str(pool_id))
        if reserves is None:
            quote_cache[key] = None
            return None
        try:
            amount_in, _ = swap_exact_out_for_pool(
                pools_by_id[str(pool_id)],
                reserve_in=int(reserves[0]),
                reserve_out=int(reserves[1]),
                amount_out=amount_out_i,
            )
        except Exception:
            quote_cache[key] = None
            return None
        amount_in_i = int(amount_in)
        quote_cache[key] = amount_in_i if amount_in_i > 0 else None
        return quote_cache[key]

    return pool_ids, max_out_by_id, quote_in


def _enumerate_positive_bounded_outputs(
    total_out: int,
    upper_bounds: Sequence[int],
) -> tuple[tuple[int, ...], ...]:
    if int(total_out) <= 0:
        raise ValueError("total_out must be positive")
    if not upper_bounds:
        return ()

    results: list[tuple[int, ...]] = []

    def recurse(remaining: int, idx: int, partial: list[int]) -> None:
        if idx == len(upper_bounds):
            if remaining == 0:
                results.append(tuple(partial))
            return
        slots_left = len(upper_bounds) - idx
        upper = int(upper_bounds[idx])
        min_here = max(1, int(remaining) - sum(int(x) for x in upper_bounds[idx + 1 :]))
        max_here = min(int(upper), int(remaining) - (slots_left - 1))
        if min_here > max_here:
            return
        for amount_out in range(int(min_here), int(max_here) + 1):
            partial.append(int(amount_out))
            recurse(int(remaining) - int(amount_out), idx + 1, partial)
            partial.pop()

    recurse(int(total_out), 0, [])
    return tuple(results)


def enumerate_exact_out_many_pool_reachable_projected_paths(
    selected_pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_selected_pools: int = 8,
) -> tuple[ProjectedQuotedPath, ...]:
    if int(amount_out_total) <= 0:
        raise ValueError("amount_out_total must be positive")
    if int(max_legs) <= 0:
        raise ValueError("max_legs must be positive")
    if int(max_selected_pools) <= 0:
        raise ValueError("max_selected_pools must be positive")

    if len(selected_pools) > int(max_selected_pools):
        raise ValueError("projection cover audit exceeded max_selected_pools")

    pool_ids, max_out_by_id, quote_in = _selected_domain_quote_env(
        selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
    )
    if not pool_ids:
        raise ValueError("no feasible selected pools for projection cover audit")

    reachable_paths: set[ProjectedQuotedPath] = set()
    max_support = min(int(max_legs), len(pool_ids))
    for support_size in range(1, int(max_support) + 1):
        for support_ids in combinations(pool_ids, support_size):
            upper_bounds = tuple(int(max_out_by_id.get(pool_id, 0)) for pool_id in support_ids)
            if any(bound <= 0 for bound in upper_bounds):
                continue
            if sum(upper_bounds) < int(amount_out_total):
                continue
            for outputs in _enumerate_positive_bounded_outputs(int(amount_out_total), upper_bounds):
                path: list[ProjectedQuotedLeg] = []
                ok = True
                for pool_id, amount_out in zip(support_ids, outputs):
                    amount_in = quote_in(pool_id, int(amount_out))
                    if amount_in is None or int(amount_in) <= 0:
                        ok = False
                        break
                    path.append((str(pool_id), int(amount_out), int(amount_in)))
                if ok:
                    reachable_paths.add(tuple(path))
    return _sorted_unique_projected_paths(reachable_paths)


def enumerate_exact_out_many_pool_cpmm_reachable_projected_paths(
    selected_pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_selected_pools: int = 8,
) -> tuple[ProjectedQuotedPath, ...]:
    return enumerate_exact_out_many_pool_reachable_projected_paths(
        selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_selected_pools=int(max_selected_pools),
    )


def audit_exact_out_many_pool_selected_domain_projection_cover(
    selected_pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_selected_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolProjectionCoverAudit:
    if int(max_enumerated_candidates) <= 0:
        raise ValueError("max_enumerated_candidates must be positive")

    if len(selected_pools) > int(max_selected_pools):
        raise ValueError("projection cover audit exceeded max_selected_pools")

    selected_domain = build_exact_out_many_pool_selected_domain(
        selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
    emitted_paths = {
        _candidate_to_projected_path(candidate)
        for candidate in selected_domain.candidates
    }
    reachable_paths = set(
        enumerate_exact_out_many_pool_reachable_projected_paths(
            selected_pools,
            asset_in=asset_in,
            asset_out=asset_out,
            amount_out_total=int(amount_out_total),
            max_legs=int(max_legs),
            max_selected_pools=int(max_selected_pools),
        )
    )

    extra_paths = emitted_paths - reachable_paths
    missing_paths = reachable_paths - emitted_paths
    canonical_projected_path = _candidate_to_projected_path(selected_domain.canonical_quote)
    return ExactOutManyPoolProjectionCoverAudit(
        selected_pool_ids=tuple(selected_domain.selected_pool_ids),
        emitted_candidate_count=len(selected_domain.candidates),
        emitted_projected_path_count=len(emitted_paths),
        reachable_projected_path_count=len(reachable_paths),
        canonical_quote=selected_domain.canonical_quote,
        canonical_quote_projected_path=canonical_projected_path,
        canonical_quote_covered=(canonical_projected_path in emitted_paths and canonical_projected_path in reachable_paths),
        sound_holds=not extra_paths,
        complete_holds=not missing_paths,
        projection_cover_holds=(not extra_paths and not missing_paths),
        extra_emitted_path=min(extra_paths) if extra_paths else None,
        missing_reachable_path=min(missing_paths) if missing_paths else None,
    )


def audit_exact_out_many_pool_selected_domain_cpmm_projection_cover(
    selected_pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_selected_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolCpmmProjectionCoverAudit:
    return audit_exact_out_many_pool_selected_domain_projection_cover(
        selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_selected_pools=int(max_selected_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )


def audit_exact_out_many_pool_projection_cover(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_selected_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolProjectionCoverAudit:
    if int(max_candidate_pools) <= 0:
        raise ValueError("max_candidate_pools must be positive")

    selected_pools = select_many_pool_audit_candidates(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
    )
    return audit_exact_out_many_pool_selected_domain_projection_cover(
        selected_pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_selected_pools=int(max_selected_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )


def audit_exact_out_many_pool_cpmm_projection_cover(
    pools: Sequence[PoolState],
    *,
    asset_in: str,
    asset_out: str,
    amount_out_total: int,
    max_legs: int = 3,
    max_candidate_pools: int = 5,
    max_selected_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
) -> ExactOutManyPoolCpmmProjectionCoverAudit:
    return audit_exact_out_many_pool_projection_cover(
        pools,
        asset_in=asset_in,
        asset_out=asset_out,
        amount_out_total=int(amount_out_total),
        max_legs=int(max_legs),
        max_candidate_pools=int(max_candidate_pools),
        max_selected_pools=int(max_selected_pools),
        max_enumerated_candidates=int(max_enumerated_candidates),
    )
