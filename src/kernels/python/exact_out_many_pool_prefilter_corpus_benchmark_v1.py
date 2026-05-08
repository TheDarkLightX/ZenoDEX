from __future__ import annotations

from dataclasses import dataclass
from itertools import product
from typing import Optional, Sequence

from ...state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus, normalize_curve_config
from .exact_out_many_pool_prefilter_contraction_audit_v1 import (
    audit_exact_out_many_pool_prefilter_contraction,
    audit_exact_out_many_pool_selected_subset_contraction,
)
from .exact_out_many_pool_prefilter_subset_search_v1 import (
    search_exact_out_many_pool_prefilter_subset,
)
from .exact_out_many_pool_repaired_prefilter_v1 import (
    build_many_pool_repaired_prefilter_selection,
)

ReservePair = tuple[int, int]
CurveTemplate = tuple[ReservePair, str, Optional[object]]


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterCorpusCase:
    case_id: str
    reserve_pairs: tuple[ReservePair, ...]
    amount_out_total: int
    current_selected_pool_ids: tuple[str, ...]
    cover_selected_pool_ids: tuple[str, ...]
    current_matches_full_canonical: bool
    cover_matches_full_canonical: bool
    current_contraction_holds: bool
    cover_contraction_holds: bool
    strict_improvement: bool
    cover_never_worse: bool
    cover_strategy: str
    searched_subset_count: int


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterCorpusBenchmarkResult:
    reserve_templates: tuple[ReservePair, ...]
    num_pools: int
    amount_out_values: tuple[int, ...]
    total_cases: int
    infeasible_cases: int
    evaluated_cases: int
    current_matches_full_canonical_cases: int
    cover_matches_full_canonical_cases: int
    current_contraction_holds_cases: int
    cover_contraction_holds_cases: int
    strict_improvement_cases: int
    cover_never_worse_cases: int
    bounded_cover_search_cases: int
    max_searched_subset_count: int
    strict_improvement_case_ids: tuple[str, ...]
    current_mismatch_case_ids: tuple[str, ...]
    cases: tuple[ExactOutManyPoolPrefilterCorpusCase, ...]


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterCurveTemplateCorpusCase:
    case_id: str
    pool_templates: tuple[str, ...]
    amount_out_total: int
    current_selected_pool_ids: tuple[str, ...]
    cover_selected_pool_ids: tuple[str, ...]
    current_matches_full_canonical: bool
    cover_matches_full_canonical: bool
    current_contraction_holds: bool
    cover_contraction_holds: bool
    strict_improvement: bool
    cover_never_worse: bool
    cover_strategy: str
    searched_subset_count: int


@dataclass(frozen=True)
class ExactOutManyPoolPrefilterCurveTemplateBenchmarkResult:
    curve_templates: tuple[str, ...]
    num_pools: int
    amount_out_values: tuple[int, ...]
    require_non_cpmm_pool: bool
    total_cases: int
    infeasible_cases: int
    evaluated_cases: int
    current_matches_full_canonical_cases: int
    cover_matches_full_canonical_cases: int
    current_contraction_holds_cases: int
    cover_contraction_holds_cases: int
    strict_improvement_cases: int
    cover_never_worse_cases: int
    bounded_cover_search_cases: int
    max_searched_subset_count: int
    strict_improvement_case_ids: tuple[str, ...]
    current_mismatch_case_ids: tuple[str, ...]
    cover_mismatch_case_ids: tuple[str, ...]
    cases: tuple[ExactOutManyPoolPrefilterCurveTemplateCorpusCase, ...]


def _pool(pid: str, reserve_pair: ReservePair) -> PoolState:
    reserve0, reserve1 = reserve_pair
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=0,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=CURVE_TAG_CPMM,
        curve_params=None,
    )


def _case_id(reserve_pairs: Sequence[ReservePair], amount_out_total: int) -> str:
    reserve_text = ",".join(f"({int(r0)},{int(r1)})" for r0, r1 in reserve_pairs)
    return f"q={int(amount_out_total)};pools=[{reserve_text}]"


def _curve_template_text(curve_template: CurveTemplate) -> str:
    reserve_pair, curve_tag, curve_params = curve_template
    reserve0, reserve1 = reserve_pair
    tag, params = normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)
    if params:
        return f"({int(reserve0)},{int(reserve1)})/{tag}:{params}"
    return f"({int(reserve0)},{int(reserve1)})/{tag}"


def _pool_from_curve_template(pid: str, curve_template: CurveTemplate) -> PoolState:
    reserve_pair, curve_tag, curve_params = curve_template
    reserve0, reserve1 = reserve_pair
    return PoolState(
        pool_id=pid,
        asset0="A",
        asset1="B",
        reserve0=int(reserve0),
        reserve1=int(reserve1),
        fee_bps=0,
        lp_supply=1_000,
        status=PoolStatus.ACTIVE,
        created_at=0,
        curve_tag=curve_tag,
        curve_params=curve_params,
    )


def _curve_case_id(curve_templates: Sequence[CurveTemplate], amount_out_total: int) -> str:
    template_text = ",".join(_curve_template_text(curve_template) for curve_template in curve_templates)
    return f"q={int(amount_out_total)};pools=[{template_text}]"


def benchmark_exact_out_many_pool_prefilter_cover_search(
    *,
    reserve_templates: Sequence[ReservePair],
    num_pools: int,
    amount_out_values: Sequence[int],
    asset_in: str = "A",
    asset_out: str = "B",
    max_legs: int = 3,
    max_candidate_pools: int = 3,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
    capture_case_limit: int = 128,
) -> ExactOutManyPoolPrefilterCorpusBenchmarkResult:
    if not reserve_templates:
        raise ValueError("reserve_templates must be non-empty")
    if int(num_pools) <= 0:
        raise ValueError("num_pools must be positive")
    if not amount_out_values:
        raise ValueError("amount_out_values must be non-empty")
    if int(capture_case_limit) <= 0:
        raise ValueError("capture_case_limit must be positive")

    total_cases = 0
    infeasible_cases = 0
    current_matches_cases = 0
    cover_matches_cases = 0
    current_contraction_cases = 0
    cover_contraction_cases = 0
    strict_improvement_cases = 0
    cover_never_worse_cases = 0
    bounded_cover_search_cases = 0
    max_searched_subset_count = 0
    captured_cases: list[ExactOutManyPoolPrefilterCorpusCase] = []
    strict_improvement_case_ids: list[str] = []
    current_mismatch_case_ids: list[str] = []

    for reserve_pairs in product(tuple(reserve_templates), repeat=int(num_pools)):
        pools = tuple(_pool(f"p{idx}", reserve_pair) for idx, reserve_pair in enumerate(reserve_pairs))
        pool_by_id = {pool.pool_id: pool for pool in pools}
        for amount_out_total in amount_out_values:
            total_cases += 1
            case_id = _case_id(reserve_pairs, int(amount_out_total))
            try:
                search_result = search_exact_out_many_pool_prefilter_subset(
                    pools,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
            except ValueError:
                infeasible_cases += 1
                continue

            cover_selection = build_many_pool_repaired_prefilter_selection(
                pools,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out_total=int(amount_out_total),
                max_legs=int(max_legs),
                max_candidate_pools=int(max_candidate_pools),
                max_full_domain_pools=int(max_full_domain_pools),
                max_enumerated_candidates=int(max_enumerated_candidates),
            )
            current_contraction = audit_exact_out_many_pool_prefilter_contraction(
                pools,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out_total=int(amount_out_total),
                max_legs=int(max_legs),
                max_candidate_pools=int(max_candidate_pools),
                max_full_domain_pools=int(max_full_domain_pools),
                max_enumerated_candidates=int(max_enumerated_candidates),
            )
            cover_contraction = audit_exact_out_many_pool_selected_subset_contraction(
                pools,
                tuple(pool_by_id[pool_id] for pool_id in cover_selection.selected_pool_ids),
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out_total=int(amount_out_total),
                max_legs=int(max_legs),
                max_full_domain_pools=int(max_full_domain_pools),
                max_enumerated_candidates=int(max_enumerated_candidates),
            )

            current_matches = bool(search_result.current_selected_matches_full_canonical)
            cover_matches = (
                search_result.full_domain_canonical_quote
                == (
                    search_result.best_cover_canonical_quote
                    if search_result.best_cover_subset_ids is not None
                    else search_result.current_selected_canonical_quote
                )
            )
            strict_improvement = (not current_matches) and cover_matches
            cover_never_worse = (not current_matches) or cover_matches

            current_matches_cases += int(current_matches)
            cover_matches_cases += int(cover_matches)
            current_contraction_cases += int(current_contraction.contraction_holds)
            cover_contraction_cases += int(cover_contraction.contraction_holds)
            strict_improvement_cases += int(strict_improvement)
            cover_never_worse_cases += int(cover_never_worse)
            bounded_cover_search_cases += int(cover_selection.strategy == "bounded_cover_search")
            max_searched_subset_count = max(
                max_searched_subset_count,
                int(search_result.searched_subset_count),
            )
            if not current_matches:
                current_mismatch_case_ids.append(case_id)
            if strict_improvement:
                strict_improvement_case_ids.append(case_id)
            if len(captured_cases) < int(capture_case_limit):
                captured_cases.append(
                    ExactOutManyPoolPrefilterCorpusCase(
                        case_id=case_id,
                        reserve_pairs=tuple((int(r0), int(r1)) for r0, r1 in reserve_pairs),
                        amount_out_total=int(amount_out_total),
                        current_selected_pool_ids=search_result.current_selected_pool_ids,
                        cover_selected_pool_ids=cover_selection.selected_pool_ids,
                        current_matches_full_canonical=current_matches,
                        cover_matches_full_canonical=cover_matches,
                        current_contraction_holds=bool(current_contraction.contraction_holds),
                        cover_contraction_holds=bool(cover_contraction.contraction_holds),
                        strict_improvement=strict_improvement,
                        cover_never_worse=cover_never_worse,
                        cover_strategy=cover_selection.strategy,
                        searched_subset_count=int(search_result.searched_subset_count),
                    )
                )

    evaluated_cases = total_cases - infeasible_cases
    return ExactOutManyPoolPrefilterCorpusBenchmarkResult(
        reserve_templates=tuple((int(r0), int(r1)) for r0, r1 in reserve_templates),
        num_pools=int(num_pools),
        amount_out_values=tuple(int(q) for q in amount_out_values),
        total_cases=total_cases,
        infeasible_cases=infeasible_cases,
        evaluated_cases=evaluated_cases,
        current_matches_full_canonical_cases=current_matches_cases,
        cover_matches_full_canonical_cases=cover_matches_cases,
        current_contraction_holds_cases=current_contraction_cases,
        cover_contraction_holds_cases=cover_contraction_cases,
        strict_improvement_cases=strict_improvement_cases,
        cover_never_worse_cases=cover_never_worse_cases,
        bounded_cover_search_cases=bounded_cover_search_cases,
        max_searched_subset_count=max_searched_subset_count,
        strict_improvement_case_ids=tuple(strict_improvement_case_ids),
        current_mismatch_case_ids=tuple(current_mismatch_case_ids),
        cases=tuple(captured_cases),
    )


def benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates(
    *,
    curve_templates: Sequence[CurveTemplate],
    num_pools: int,
    amount_out_values: Sequence[int],
    asset_in: str = "A",
    asset_out: str = "B",
    max_legs: int = 3,
    max_candidate_pools: int = 3,
    max_full_domain_pools: int = 8,
    max_enumerated_candidates: int = 20_000,
    require_non_cpmm_pool: bool = False,
    capture_case_limit: int = 128,
) -> ExactOutManyPoolPrefilterCurveTemplateBenchmarkResult:
    if not curve_templates:
        raise ValueError("curve_templates must be non-empty")
    if int(num_pools) <= 0:
        raise ValueError("num_pools must be positive")
    if not amount_out_values:
        raise ValueError("amount_out_values must be non-empty")
    if int(capture_case_limit) <= 0:
        raise ValueError("capture_case_limit must be positive")

    total_cases = 0
    infeasible_cases = 0
    current_matches_cases = 0
    cover_matches_cases = 0
    current_contraction_cases = 0
    cover_contraction_cases = 0
    strict_improvement_cases = 0
    cover_never_worse_cases = 0
    bounded_cover_search_cases = 0
    max_searched_subset_count = 0
    captured_cases: list[ExactOutManyPoolPrefilterCurveTemplateCorpusCase] = []
    strict_improvement_case_ids: list[str] = []
    current_mismatch_case_ids: list[str] = []
    cover_mismatch_case_ids: list[str] = []

    normalized_templates = tuple(
        (
            (int(reserve_pair[0]), int(reserve_pair[1])),
            normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)[0],
            curve_params,
        )
        for reserve_pair, curve_tag, curve_params in curve_templates
    )

    for selected_templates in product(normalized_templates, repeat=int(num_pools)):
        if bool(require_non_cpmm_pool) and all(
            normalize_curve_config(curve_tag=curve_tag, curve_params=curve_params)[0] == CURVE_TAG_CPMM
            for _reserve_pair, curve_tag, curve_params in selected_templates
        ):
            continue
        pools = tuple(
            _pool_from_curve_template(f"p{idx}", curve_template)
            for idx, curve_template in enumerate(selected_templates)
        )
        pool_by_id = {pool.pool_id: pool for pool in pools}
        for amount_out_total in amount_out_values:
            total_cases += 1
            case_id = _curve_case_id(selected_templates, int(amount_out_total))
            try:
                search_result = search_exact_out_many_pool_prefilter_subset(
                    pools,
                    asset_in=asset_in,
                    asset_out=asset_out,
                    amount_out_total=int(amount_out_total),
                    max_legs=int(max_legs),
                    max_candidate_pools=int(max_candidate_pools),
                    max_full_domain_pools=int(max_full_domain_pools),
                    max_enumerated_candidates=int(max_enumerated_candidates),
                )
            except ValueError:
                infeasible_cases += 1
                continue

            cover_selection = build_many_pool_repaired_prefilter_selection(
                pools,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out_total=int(amount_out_total),
                max_legs=int(max_legs),
                max_candidate_pools=int(max_candidate_pools),
                max_full_domain_pools=int(max_full_domain_pools),
                max_enumerated_candidates=int(max_enumerated_candidates),
            )
            current_contraction = audit_exact_out_many_pool_prefilter_contraction(
                pools,
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out_total=int(amount_out_total),
                max_legs=int(max_legs),
                max_candidate_pools=int(max_candidate_pools),
                max_full_domain_pools=int(max_full_domain_pools),
                max_enumerated_candidates=int(max_enumerated_candidates),
            )
            cover_contraction = audit_exact_out_many_pool_selected_subset_contraction(
                pools,
                tuple(pool_by_id[pool_id] for pool_id in cover_selection.selected_pool_ids),
                asset_in=asset_in,
                asset_out=asset_out,
                amount_out_total=int(amount_out_total),
                max_legs=int(max_legs),
                max_full_domain_pools=int(max_full_domain_pools),
                max_enumerated_candidates=int(max_enumerated_candidates),
            )

            current_matches = bool(search_result.current_selected_matches_full_canonical)
            cover_matches = (
                search_result.full_domain_canonical_quote
                == (
                    search_result.best_cover_canonical_quote
                    if search_result.best_cover_subset_ids is not None
                    else search_result.current_selected_canonical_quote
                )
            )
            strict_improvement = (not current_matches) and cover_matches
            cover_never_worse = (not current_matches) or cover_matches

            current_matches_cases += int(current_matches)
            cover_matches_cases += int(cover_matches)
            current_contraction_cases += int(current_contraction.contraction_holds)
            cover_contraction_cases += int(cover_contraction.contraction_holds)
            strict_improvement_cases += int(strict_improvement)
            cover_never_worse_cases += int(cover_never_worse)
            bounded_cover_search_cases += int(cover_selection.strategy == "bounded_cover_search")
            max_searched_subset_count = max(
                max_searched_subset_count,
                int(search_result.searched_subset_count),
            )
            if not current_matches:
                current_mismatch_case_ids.append(case_id)
            if not cover_matches:
                cover_mismatch_case_ids.append(case_id)
            if strict_improvement:
                strict_improvement_case_ids.append(case_id)
            if len(captured_cases) < int(capture_case_limit):
                captured_cases.append(
                    ExactOutManyPoolPrefilterCurveTemplateCorpusCase(
                        case_id=case_id,
                        pool_templates=tuple(_curve_template_text(curve_template) for curve_template in selected_templates),
                        amount_out_total=int(amount_out_total),
                        current_selected_pool_ids=search_result.current_selected_pool_ids,
                        cover_selected_pool_ids=cover_selection.selected_pool_ids,
                        current_matches_full_canonical=current_matches,
                        cover_matches_full_canonical=cover_matches,
                        current_contraction_holds=bool(current_contraction.contraction_holds),
                        cover_contraction_holds=bool(cover_contraction.contraction_holds),
                        strict_improvement=strict_improvement,
                        cover_never_worse=cover_never_worse,
                        cover_strategy=cover_selection.strategy,
                        searched_subset_count=int(search_result.searched_subset_count),
                    )
                )

    evaluated_cases = total_cases - infeasible_cases
    return ExactOutManyPoolPrefilterCurveTemplateBenchmarkResult(
        curve_templates=tuple(
            _curve_template_text(curve_template)
            for curve_template in normalized_templates
        ),
        num_pools=int(num_pools),
        amount_out_values=tuple(int(q) for q in amount_out_values),
        require_non_cpmm_pool=bool(require_non_cpmm_pool),
        total_cases=total_cases,
        infeasible_cases=infeasible_cases,
        evaluated_cases=evaluated_cases,
        current_matches_full_canonical_cases=current_matches_cases,
        cover_matches_full_canonical_cases=cover_matches_cases,
        current_contraction_holds_cases=current_contraction_cases,
        cover_contraction_holds_cases=cover_contraction_cases,
        strict_improvement_cases=strict_improvement_cases,
        cover_never_worse_cases=cover_never_worse_cases,
        bounded_cover_search_cases=bounded_cover_search_cases,
        max_searched_subset_count=max_searched_subset_count,
        strict_improvement_case_ids=tuple(strict_improvement_case_ids),
        current_mismatch_case_ids=tuple(current_mismatch_case_ids),
        cover_mismatch_case_ids=tuple(cover_mismatch_case_ids),
        cases=tuple(captured_cases),
    )
