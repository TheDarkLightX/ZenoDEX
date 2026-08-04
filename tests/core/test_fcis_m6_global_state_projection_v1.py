"""Closed-world bookkeeping tests for M6 application-content coverage."""

from __future__ import annotations

from dataclasses import replace

import pytest

from src.core.fcis_m6_global_state_projection_v1 import (
    M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1,
    M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1,
    M6ApplicationStateComponentV1,
    M6GlobalStateProjectionRejectCodeV1,
    M6GlobalStateProjectionRejectV1,
    M6ProjectionCoverageV1,
    M6StructuralCoverageWitnessV1,
    require_complete_structural_coverage_v1,
)


def _root(index: int) -> str:
    return "0x" + f"{index:064x}"


def _coverage(
    *,
    missing: tuple[M6ApplicationStateComponentV1, ...],
) -> M6ProjectionCoverageV1:
    covered = tuple(
        component
        for component in M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1
        if component not in missing
    )
    return M6ProjectionCoverageV1(
        component_roots=tuple(
            (component, _root(index + 1)) for index, component in enumerate(covered)
        ),
        covered_components=covered,
        missing_components=missing,
    )


def test_fake_complete_roots_receive_only_non_authoritative_structural_witness() -> None:
    coverage = _coverage(missing=())
    result = require_complete_structural_coverage_v1(coverage)
    assert type(result) is M6StructuralCoverageWitnessV1
    assert result.coverage.coverage_root == coverage.coverage_root


def test_zeno_ledger_spot_registry_is_an_exact_strict_subset() -> None:
    assert tuple(component.value for component in M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1) == (
        "account_balances",
        "amm_pools",
        "lp_ownership",
        "lp_mint_age",
        "lp_duration_risk",
        "nonces",
        "legacy_fee_accumulator",
    )
    assert set(M6_ZENO_LEDGER_SPOT_COMMITTED_COMPONENTS_V1) < set(
        M6_REQUIRED_APPLICATION_STATE_COMPONENTS_V1
    )


def test_missing_component_fails_closed_with_exact_gap_set() -> None:
    missing = (
        M6ApplicationStateComponentV1.PROOF_MINING_STATE,
        M6ApplicationStateComponentV1.ZUSD_MONETARY_STATE,
    )
    result = require_complete_structural_coverage_v1(_coverage(missing=missing))
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.INCOMPLETE_APPLICATION_CONTENT
    assert result.missing_components == missing


def test_coverage_requires_exact_partition_and_component_roots() -> None:
    complete = _coverage(missing=())
    with pytest.raises(ValueError, match="exactly cover"):
        replace(complete, component_roots=complete.component_roots[:-1])
    with pytest.raises(ValueError, match="disjoint"):
        replace(
            complete,
            missing_components=(M6ApplicationStateComponentV1.PERPS_STATE,),
        )


def test_component_order_duplicate_and_surplus_are_rejected() -> None:
    complete = _coverage(missing=())
    with pytest.raises(ValueError, match="canonical order"):
        replace(complete, covered_components=tuple(reversed(complete.covered_components)))
    with pytest.raises(ValueError, match="unique"):
        replace(
            complete,
            component_roots=complete.component_roots + (complete.component_roots[-1],),
        )


def test_coverage_root_is_source_neutral() -> None:
    coverage = _coverage(missing=())
    assert not hasattr(coverage, "source_schema")
    assert not hasattr(coverage, "source_state_root")
    assert coverage.coverage_root == replace(coverage).coverage_root


def test_wrong_coverage_type_is_typed_rejection() -> None:
    result = require_complete_structural_coverage_v1({"complete": True})
    assert type(result) is M6GlobalStateProjectionRejectV1
    assert result.code is M6GlobalStateProjectionRejectCodeV1.WRONG_EXACT_TYPE
