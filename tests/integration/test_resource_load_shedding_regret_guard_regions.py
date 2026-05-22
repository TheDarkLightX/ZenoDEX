from __future__ import annotations

from itertools import product

from src.integration.resource_load_shedding_regret_guard_regions import (
    ResourceLoadSheddingRegretGuardInputs,
    build_resource_load_shedding_regret_guard_regions,
    final_admission_ok,
    input_region,
    proof_gated_final_admission_ok,
)


def test_resource_load_shedding_regret_guard_regions_partition_ok_surface() -> None:
    regions = build_resource_load_shedding_regret_guard_regions()

    assert (regions.proof_gated_final_admission_ok & regions.admitted_without_proof).is_empty()
    assert (regions.proof_gated_final_admission_ok & regions.denied).is_empty()
    assert (regions.admitted_without_proof & regions.denied).is_empty()
    assert regions.partition_is_total()


def test_resource_load_shedding_regret_guard_regions_proof_gated_refines_final_admission() -> None:
    regions = build_resource_load_shedding_regret_guard_regions()

    assert regions.proof_gated_final_admission_ok <= regions.final_admission_ok
    assert (regions.normal_path_ok & regions.shed_path_ok).is_empty()
    assert (regions.normal_only | regions.shed_only) == regions.final_admission_ok


def test_resource_load_shedding_regret_guard_regions_match_tau_trace_cases() -> None:
    regions = build_resource_load_shedding_regret_guard_regions()
    cases = (
        ((1, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1), True),
        ((1, 1, 0, 1, 1, 1, 1, 0, 0, 1, 1, 1), False),
        ((0, 1, 0, 0, 0, 1, 1, 1, 1, 0, 1, 1), True),
        ((0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1), False),
    )

    for word, expected_proof_gated in cases:
        inputs = ResourceLoadSheddingRegretGuardInputs.from_word(word)
        region = input_region(inputs)
        assert (region <= regions.proof_gated_final_admission_ok) == expected_proof_gated


def test_resource_load_shedding_regret_guard_regions_capture_admitted_without_proof_surface() -> None:
    regions = build_resource_load_shedding_regret_guard_regions()
    inputs = ResourceLoadSheddingRegretGuardInputs(
        resource_admission_ok=True,
        artifact_binding_ok=True,
        user_regret_ok=True,
        user_impact_ok=True,
        quote_fresh_ok=True,
        route_cert_ok=True,
        require_route_cert=True,
        load_shedding_mode=False,
        emergency_override_ok=False,
        strict_regret_mode=True,
        proof_ok=False,
        binding_ok=True,
    )
    region = input_region(inputs)

    assert region <= regions.final_admission_ok
    assert region <= regions.admitted_without_proof
    assert (region & regions.proof_gated_final_admission_ok).is_empty()


def test_resource_load_shedding_regret_guard_python_formulas_match_region_membership() -> None:
    regions = build_resource_load_shedding_regret_guard_regions()

    for word in product((0, 1), repeat=12):
        inputs = ResourceLoadSheddingRegretGuardInputs.from_word(word)
        region = input_region(inputs)
        assert (region <= regions.final_admission_ok) == final_admission_ok(inputs)
        assert (region <= regions.proof_gated_final_admission_ok) == proof_gated_final_admission_ok(inputs)
