from __future__ import annotations

from src.integration.exact_out_many_pool_repaired_replacement_shadow_benchmark_v1 import (
    benchmark_exact_out_many_pool_repaired_replacement_shadow_on_curve_templates,
)
from src.state.pools import CURVE_TAG_CPMM, CURVE_TAG_CUBIC_SUM_V1, CURVE_TAG_SUM_BOOST_V1


def test_repaired_replacement_shadow_benchmark_matches_sum_boost_receipt() -> None:
    result = benchmark_exact_out_many_pool_repaired_replacement_shadow_on_curve_templates(
        curve_templates=(
            ((20, 10), CURVE_TAG_CPMM, None),
            ((30, 15), CURVE_TAG_CPMM, None),
            ((20, 10), CURVE_TAG_SUM_BOOST_V1, {"mu_num": 1, "mu_den": 2}),
        ),
        num_pools=3,
        amount_out_values=(1, 2, 3, 4, 5, 6),
        max_legs=3,
        max_candidate_pools=2,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
        require_non_cpmm_pool=True,
    )

    assert result.require_non_cpmm_pool is True
    assert result.total_cases == 114
    assert result.infeasible_cases == 0
    assert result.evaluated_cases == 114
    assert result.shadow_packet_ok_cases == 114
    assert result.default_packet_ok_cases == 114
    assert result.replacement_available_cases == 114
    assert result.replacement_quote_matches_full_canonical_cases == 114
    assert result.replacement_quote_matches_selected_runtime_quote_cases == 114
    assert result.effective_quote_matches_replacement_quote_cases == 114
    assert result.default_effective_quote_matches_full_domain_canonical_cases == 114
    assert result.default_uses_repaired_advisory_cases == 0
    assert result.strict_replacement_cases == 0
    assert result.replacement_unavailable_case_ids == ()
    assert result.strict_replacement_case_ids == ()


def test_repaired_replacement_shadow_benchmark_matches_combined_supported_family_receipt() -> None:
    result = benchmark_exact_out_many_pool_repaired_replacement_shadow_on_curve_templates(
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
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
        require_non_cpmm_pool=True,
    )

    assert result.require_non_cpmm_pool is True
    assert result.total_cases == 336
    assert result.infeasible_cases == 0
    assert result.evaluated_cases == 336
    assert result.shadow_packet_ok_cases == 336
    assert result.default_packet_ok_cases == 336
    assert result.replacement_available_cases == 336
    assert result.replacement_quote_matches_full_canonical_cases == 336
    assert result.replacement_quote_matches_selected_runtime_quote_cases == 336
    assert result.effective_quote_matches_replacement_quote_cases == 336
    assert result.default_effective_quote_matches_full_domain_canonical_cases == 336
    assert result.default_uses_repaired_advisory_cases == 0
    assert result.strict_replacement_cases == 0
    assert result.replacement_unavailable_case_ids == ()
    assert result.strict_replacement_case_ids == ()
