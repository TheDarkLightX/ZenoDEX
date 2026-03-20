from __future__ import annotations

from src.kernels.python.exact_out_many_pool_prefilter_corpus_benchmark_v1 import (
    benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates,
)
from src.kernels.python.exact_out_many_pool_prefilter_corpus_benchmark_v1 import (
    benchmark_exact_out_many_pool_prefilter_cover_search,
)
from src.state.pools import CURVE_TAG_CPMM, CURVE_TAG_CUBIC_SUM_V1, CURVE_TAG_SUM_BOOST_V1


def test_prefilter_corpus_benchmark_shows_cover_search_is_never_worse_on_small_corpus() -> None:
    result = benchmark_exact_out_many_pool_prefilter_cover_search(
        reserve_templates=((20, 10), (30, 15)),
        num_pools=4,
        amount_out_values=(1, 2, 3, 4),
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert result.total_cases == 64
    assert result.infeasible_cases == 0
    assert result.evaluated_cases == 64
    assert result.cover_matches_full_canonical_cases >= result.current_matches_full_canonical_cases
    assert result.cover_never_worse_cases == result.evaluated_cases
    assert result.strict_improvement_cases > 0
    assert "q=4;pools=[(20,10),(20,10),(30,15),(30,15)]" in result.strict_improvement_case_ids


def test_prefilter_corpus_benchmark_still_finds_cover_search_repairs_at_larger_budget() -> None:
    result = benchmark_exact_out_many_pool_prefilter_cover_search(
        reserve_templates=((20, 10), (30, 15)),
        num_pools=4,
        amount_out_values=(1, 2, 3, 4),
        max_legs=3,
        max_candidate_pools=4,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert result.total_cases == 64
    assert result.evaluated_cases == 64
    assert result.cover_matches_full_canonical_cases == result.evaluated_cases
    assert result.cover_never_worse_cases == result.evaluated_cases
    assert result.strict_improvement_cases > 0
    assert "q=4;pools=[(20,10),(20,10),(30,15),(30,15)]" in result.strict_improvement_case_ids


def test_prefilter_corpus_benchmark_matches_broader_three_template_receipt() -> None:
    result = benchmark_exact_out_many_pool_prefilter_cover_search(
        reserve_templates=((20, 10), (30, 15), (40, 20)),
        num_pools=4,
        amount_out_values=(1, 2, 3, 4, 5),
        max_legs=3,
        max_candidate_pools=3,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )

    assert result.total_cases == 405
    assert result.infeasible_cases == 0
    assert result.evaluated_cases == 405
    assert result.current_matches_full_canonical_cases == 393
    assert result.cover_matches_full_canonical_cases == 405
    assert result.current_contraction_holds_cases == 393
    assert result.cover_contraction_holds_cases == 405
    assert result.strict_improvement_cases == 12
    assert result.cover_never_worse_cases == 405
    assert "q=5;pools=[(20,10),(40,20),(40,20),(40,20)]" in result.strict_improvement_case_ids


def test_prefilter_curve_template_benchmark_matches_mixed_curve_receipt() -> None:
    result = benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates(
        curve_templates=(
            ((20, 10), CURVE_TAG_CPMM, None),
            ((30, 15), CURVE_TAG_CPMM, None),
            ((20, 10), CURVE_TAG_SUM_BOOST_V1, {"mu_num": 1, "mu_den": 2}),
        ),
        num_pools=3,
        amount_out_values=(1, 2, 3, 4, 5, 6),
        max_legs=3,
        max_candidate_pools=2,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
        require_non_cpmm_pool=True,
    )

    assert result.require_non_cpmm_pool is True
    assert result.total_cases == 114
    assert result.infeasible_cases == 0
    assert result.evaluated_cases == 114
    assert result.current_matches_full_canonical_cases == 111
    assert result.cover_matches_full_canonical_cases == 114
    assert result.current_contraction_holds_cases == 111
    assert result.cover_contraction_holds_cases == 114
    assert result.strict_improvement_cases == 3
    assert result.cover_never_worse_cases == 114
    assert result.cover_mismatch_case_ids == ()
    assert (
        'q=6;pools=[(20,10)/CPMM,(30,15)/CPMM,(20,10)/SUM_BOOST_V1:{"mu_den":2,"mu_num":1}]'
        in result.strict_improvement_case_ids
    )


def test_prefilter_curve_template_benchmark_matches_cubic_supported_curve_receipt() -> None:
    result = benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates(
        curve_templates=(
            ((20, 10), CURVE_TAG_CPMM, None),
            ((30, 15), CURVE_TAG_CPMM, None),
            ((20, 10), CURVE_TAG_CUBIC_SUM_V1, {"p": 1, "q": 1}),
        ),
        num_pools=3,
        amount_out_values=(1, 2, 3, 4, 5, 6),
        max_legs=3,
        max_candidate_pools=2,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
        require_non_cpmm_pool=True,
    )

    assert result.require_non_cpmm_pool is True
    assert result.total_cases == 114
    assert result.infeasible_cases == 0
    assert result.evaluated_cases == 114
    assert result.current_matches_full_canonical_cases == 109
    assert result.cover_matches_full_canonical_cases == 114
    assert result.current_contraction_holds_cases == 109
    assert result.cover_contraction_holds_cases == 114
    assert result.strict_improvement_cases == 5
    assert result.cover_never_worse_cases == 114
    assert result.cover_mismatch_case_ids == ()
    assert (
        'q=5;pools=[(20,10)/CPMM,(30,15)/CPMM,(20,10)/CUBIC_SUM_V1:{"p":1,"q":1}]'
        in result.strict_improvement_case_ids
    )


def test_prefilter_curve_template_benchmark_matches_combined_supported_family_receipt() -> None:
    result = benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates(
        curve_templates=(
            ((20, 10), CURVE_TAG_CPMM, None),
            ((30, 15), CURVE_TAG_CPMM, None),
            ((20, 10), CURVE_TAG_SUM_BOOST_V1, {"mu_num": 1, "mu_den": 2}),
            ((20, 10), CURVE_TAG_CUBIC_SUM_V1, {"p": 1, "q": 1}),
        ),
        num_pools=3,
        amount_out_values=(1, 2, 3, 4, 5, 6),
        max_legs=3,
        max_candidate_pools=2,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
        require_non_cpmm_pool=True,
    )

    assert result.require_non_cpmm_pool is True
    assert result.total_cases == 336
    assert result.infeasible_cases == 0
    assert result.evaluated_cases == 336
    assert result.current_matches_full_canonical_cases == 327
    assert result.cover_matches_full_canonical_cases == 336
    assert result.current_contraction_holds_cases == 327
    assert result.cover_contraction_holds_cases == 336
    assert result.strict_improvement_cases == 9
    assert result.cover_never_worse_cases == 336
    assert result.cover_mismatch_case_ids == ()
    assert (
        'q=6;pools=[(20,10)/CPMM,(30,15)/CPMM,(20,10)/SUM_BOOST_V1:{"mu_den":2,"mu_num":1}]'
        in result.strict_improvement_case_ids
    )
    assert (
        'q=5;pools=[(20,10)/CPMM,(30,15)/CPMM,(20,10)/CUBIC_SUM_V1:{"p":1,"q":1}]'
        in result.strict_improvement_case_ids
    )


def test_prefilter_curve_template_benchmark_matches_four_pool_supported_family_receipts() -> None:
    for max_candidate_pools, expected_current_matches, expected_strict_improvement, expected_case_id in (
        (
            2,
            1395,
            45,
            'q=6;pools=[(20,10)/CPMM,(20,10)/CPMM,(30,15)/CPMM,(20,10)/SUM_BOOST_V1:{"mu_den":2,"mu_num":1}]',
        ),
        (
            3,
            1428,
            12,
            'q=6;pools=[(20,10)/CPMM,(30,15)/CPMM,(30,15)/CPMM,(20,10)/SUM_BOOST_V1:{"mu_den":2,"mu_num":1}]',
        ),
    ):
        result = benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates(
            curve_templates=(
                ((20, 10), CURVE_TAG_CPMM, None),
                ((30, 15), CURVE_TAG_CPMM, None),
                ((20, 10), CURVE_TAG_SUM_BOOST_V1, {"mu_num": 1, "mu_den": 2}),
                ((20, 10), CURVE_TAG_CUBIC_SUM_V1, {"p": 1, "q": 1}),
            ),
            num_pools=4,
            amount_out_values=(1, 2, 3, 4, 5, 6),
            max_legs=3,
            max_candidate_pools=max_candidate_pools,
            max_full_domain_pools=6,
            max_enumerated_candidates=50_000,
            require_non_cpmm_pool=True,
        )

        assert result.require_non_cpmm_pool is True
        assert result.total_cases == 1440
        assert result.infeasible_cases == 0
        assert result.evaluated_cases == 1440
        assert result.current_matches_full_canonical_cases == expected_current_matches
        assert result.cover_matches_full_canonical_cases == 1440
        assert result.current_contraction_holds_cases == expected_current_matches
        assert result.cover_contraction_holds_cases == 1440
        assert result.strict_improvement_cases == expected_strict_improvement
        assert result.cover_never_worse_cases == 1440
        assert result.cover_mismatch_case_ids == ()
        assert expected_case_id in result.strict_improvement_case_ids


def test_prefilter_curve_template_benchmark_matches_five_pool_supported_family_receipts() -> None:
    for max_candidate_pools, expected_max_searched_subset_count in (
        (2, 15),
        (3, 25),
    ):
        result = benchmark_exact_out_many_pool_prefilter_cover_search_on_curve_templates(
            curve_templates=(
                ((20, 10), CURVE_TAG_CPMM, None),
                ((30, 15), CURVE_TAG_CPMM, None),
                ((20, 10), CURVE_TAG_SUM_BOOST_V1, {"mu_num": 1, "mu_den": 2}),
                ((20, 10), CURVE_TAG_CUBIC_SUM_V1, {"p": 1, "q": 1}),
            ),
            num_pools=5,
            amount_out_values=(1, 2, 3, 4),
            max_legs=3,
            max_candidate_pools=max_candidate_pools,
            max_full_domain_pools=7,
            max_enumerated_candidates=50_000,
            require_non_cpmm_pool=True,
        )

        assert result.require_non_cpmm_pool is True
        assert result.total_cases == 3968
        assert result.infeasible_cases == 0
        assert result.evaluated_cases == 3968
        assert result.current_matches_full_canonical_cases == 3968
        assert result.cover_matches_full_canonical_cases == 3968
        assert result.current_contraction_holds_cases == 3968
        assert result.cover_contraction_holds_cases == 3968
        assert result.strict_improvement_cases == 0
        assert result.cover_never_worse_cases == 3968
        assert result.cover_mismatch_case_ids == ()
        assert result.max_searched_subset_count == expected_max_searched_subset_count
