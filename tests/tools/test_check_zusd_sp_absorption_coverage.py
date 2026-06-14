"""Tests for the zUSD stability-pool absorption-coverage advisory gate."""

from __future__ import annotations

import json

from src.core.zusd import E8
from tools.check_zusd_sp_absorption_coverage import (
    REPORT_SCHEMA,
    CoverageScenario,
    _evaluate_scenario,
    _vault_state,
    main,
    validate_sp_absorption_coverage_corpus,
)


def test_shipped_corpus_is_accepted_and_faithful() -> None:
    report = validate_sp_absorption_coverage_corpus()
    assert report["schema"] == REPORT_SCHEMA
    assert report["ok"] is True
    assert report["status"] == "accepted"
    assert report["scenario_count"] == 6
    assert report["accepted_scenario_count"] == 6
    assert report["failed_scenarios"] == []
    for scenario in report["scenarios"]:
        assert scenario["ok"] is True
        assert scenario["errors"] == []
        assert scenario["coverage"]["schema"] == "zenodex.zusd.sp_absorption_coverage.v0"


def test_corpus_includes_the_blocked_precursor_bound_to_the_kernel_refusal() -> None:
    report = validate_sp_absorption_coverage_corpus()
    blocked = next(s for s in report["scenarios"] if s["name"] == "blocked_spiral_precursor")
    assert blocked["coverage"]["classification"] == "liquidation_blocked"
    assert blocked["coverage"]["liquidation_blocked_by_sp"] is True
    # The advisory monitor predicted the exact kernel refusal.
    assert blocked["kernel_liquidate_ok"] is False
    assert blocked["kernel_liquidate_error"] == "stability pool cannot absorb debt"


def test_mislabeled_scenario_is_rejected() -> None:
    """A wrong expected classification must fail -- the gate is not vacuous."""
    bad = CoverageScenario(
        name="mislabeled",
        description="under-MCR uninsured vault mislabeled as covered",
        state=_vault_state(
            collateral_e8=1_000 * E8,
            debt_e8=1_000 * E8,
            free_debt_e8=400 * E8,
            sp_debt_e8=600 * E8,
        ),
        expected_classification="covered",
    )
    result = _evaluate_scenario(bad)
    assert result["ok"] is False
    assert any("classification" in error for error in result["errors"])


def test_main_json_returns_zero_and_emits_valid_report(capsys) -> None:
    code = main(["--json"])
    assert code == 0
    payload = json.loads(capsys.readouterr().out)
    assert payload["ok"] is True
    assert payload["schema"] == REPORT_SCHEMA
