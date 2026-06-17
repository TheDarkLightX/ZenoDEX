from __future__ import annotations

from itertools import product

from src.integration.exact_out_many_pool_adaptive_liveness_regions import (
    ExactOutManyPoolAdaptiveLivenessInputs,
    build_exact_out_many_pool_adaptive_liveness_regions,
    exact_out_many_pool_adaptive_liveness_ok,
    input_region,
    packet_input_region,
)
from src.integration.exact_out_route_certificate import (
    build_exact_out_many_pool_adaptive_liveness_packet,
)
from src.state.pools import CURVE_TAG_CPMM, PoolState, PoolStatus


def _pool(
    *,
    pool_id: str,
    reserve0: int,
    reserve1: int,
    fee_bps: int = 0,
    curve_tag: str = CURVE_TAG_CPMM,
    curve_params: object | None = None,
) -> PoolState:
    return PoolState(
        pool_id=pool_id,
        asset0="A",
        asset1="B",
        reserve0=reserve0,
        reserve1=reserve1,
        fee_bps=fee_bps,
        curve_tag=curve_tag,
        curve_params=curve_params,
        status=PoolStatus.ACTIVE,
        lp_supply=100,
        created_at=0,
    )


def _adaptive_pools() -> tuple[PoolState, ...]:
    return (
        _pool(pool_id="p0", reserve0=20, reserve1=10),
        _pool(pool_id="p1", reserve0=20, reserve1=10),
        _pool(pool_id="p2", reserve0=30, reserve1=15),
        _pool(pool_id="p3", reserve0=30, reserve1=15),
    )


def test_exact_out_many_pool_adaptive_liveness_regions_partition_ok_surface() -> None:
    regions = build_exact_out_many_pool_adaptive_liveness_regions()

    assert (regions.liveness_ok & regions.budget_blocked).is_empty()
    assert (regions.liveness_ok & regions.invalid).is_empty()
    assert (regions.budget_blocked & regions.invalid).is_empty()
    assert regions.partition_is_total()


def test_exact_out_many_pool_adaptive_liveness_regions_accept_success_packet() -> None:
    packet = build_exact_out_many_pool_adaptive_liveness_packet(
        _adaptive_pools(),
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=3,
        max_candidates=12,
        max_iters=4096,
        window=64,
        brute_force_max=512,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    regions = build_exact_out_many_pool_adaptive_liveness_regions()
    region = packet_input_region(packet)

    assert region <= regions.liveness_ok
    assert region <= regions.returned_success
    assert (region & regions.explicit_failure).is_empty()


def test_exact_out_many_pool_adaptive_liveness_regions_accept_replayable_failure_packet() -> None:
    packet = build_exact_out_many_pool_adaptive_liveness_packet(
        _adaptive_pools(),
        asset_in="A",
        asset_out="B",
        amount_out_total=4,
        max_legs=3,
        max_candidate_pools=1,
        max_candidates=2,
        max_iters=1,
        window=0,
        brute_force_max=0,
        max_full_domain_pools=6,
        max_enumerated_candidates=50_000,
    )
    regions = build_exact_out_many_pool_adaptive_liveness_regions()
    region = packet_input_region(packet)

    assert region <= regions.liveness_ok
    assert region <= regions.explicit_failure
    assert (region & regions.returned_success).is_empty()


def test_exact_out_many_pool_adaptive_liveness_regions_budget_blocked_surface() -> None:
    inputs = ExactOutManyPoolAdaptiveLivenessInputs(
        selected_domain_budget_respected=False,
        repaired_selection_budget_respected=False,
        full_domain_pool_budget_respected=False,
        full_domain_candidate_budget_respected=False,
        budget_parameters_bound=False,
        cheap_path_attempted=True,
        cheap_path_success=False,
        fallback_required=True,
        fallback_attempted=True,
        fallback_available=False,
        returned_success=False,
        explicit_failure=True,
        effective_quote_present=False,
        failure_reason_present=True,
    )
    regions = build_exact_out_many_pool_adaptive_liveness_regions()
    region = input_region(inputs)

    assert region <= regions.budget_blocked
    assert (region & regions.invalid).is_empty()
    assert (region & regions.liveness_ok).is_empty()


def test_exact_out_many_pool_adaptive_liveness_regions_invalid_surface() -> None:
    inputs = ExactOutManyPoolAdaptiveLivenessInputs(
        selected_domain_budget_respected=True,
        repaired_selection_budget_respected=True,
        full_domain_pool_budget_respected=True,
        full_domain_candidate_budget_respected=True,
        budget_parameters_bound=True,
        cheap_path_attempted=False,
        cheap_path_success=True,
        fallback_required=False,
        fallback_attempted=False,
        fallback_available=True,
        returned_success=True,
        explicit_failure=False,
        effective_quote_present=True,
        failure_reason_present=False,
    )
    regions = build_exact_out_many_pool_adaptive_liveness_regions()
    region = input_region(inputs)

    assert region <= regions.invalid
    assert (region & regions.liveness_ok).is_empty()
    assert (region & regions.budget_blocked).is_empty()


def test_exact_out_many_pool_adaptive_liveness_python_formula_matches_region_membership() -> None:
    regions = build_exact_out_many_pool_adaptive_liveness_regions()

    for word in product((0, 1), repeat=14):
        inputs = ExactOutManyPoolAdaptiveLivenessInputs.from_word(word)
        region = input_region(inputs)
        assert (region <= regions.liveness_ok) == exact_out_many_pool_adaptive_liveness_ok(inputs)
