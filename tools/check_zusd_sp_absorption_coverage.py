#!/usr/bin/env python3
"""Advisory gate for the zUSD stability-pool absorption-coverage axis.

This checker validates the ADVISORY monitor in
``src/core/zusd_sp_coverage.py`` (recommendation R7c,
``docs/MECHANISM_DESIGN_IMPROVEMENT_ANALYSIS.md`` section 6.2). It does two
things over a bounded, deterministic scenario corpus:

1. asserts the monitor classifies each scenario as declared, and
2. proves the monitor is FAITHFUL to the kernel: the monitor's ``coverage_ok``
   prediction equals the real ``zusd`` Python-reference liquidation-refusal
   decision (``_step_python`` on a ``liquidate`` command) on every scenario.

The second check is the point: it pins the read-only pre-disaster axis to the
runtime's actual ``debt_e8 > sp_debt_e8`` refusal, so the advisory signal can
never silently drift from settlement behavior. No settlement code is modified.
"""

from __future__ import annotations

import argparse
import json
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.core.zusd import (  # noqa: E402
    E8,
    ZUSDCommand,
    ZUSDState,
    _step_python,
    check_invariants,
)
from src.core.zusd_sp_coverage import sp_absorption_coverage  # noqa: E402

REPORT_SCHEMA = "zenodex.zusd.sp_absorption_coverage_report.v0"
SP_ABSORPTION_REFUSAL_ERROR = "stability pool cannot absorb debt"


@dataclass(frozen=True)
class CoverageScenario:
    name: str
    description: str
    state: ZUSDState
    expected_classification: str


def _vault_state(
    *,
    collateral_e8: int,
    debt_e8: int,
    free_debt_e8: int,
    sp_debt_e8: int,
    oracle_seen: bool = True,
    price_e8: int = E8,
) -> ZUSDState:
    """Build a legal single-vault state; oracle pending == active when seen."""
    if oracle_seen:
        return ZUSDState(
            now_epoch=0,
            oracle_seen=True,
            oracle_last_update_epoch=0,
            price_e8=price_e8,
            price_pending_e8=price_e8,
            collateral_e8=collateral_e8,
            debt_e8=debt_e8,
            free_debt_e8=free_debt_e8,
            sp_debt_e8=sp_debt_e8,
        )
    return ZUSDState(
        now_epoch=0,
        oracle_seen=False,
        oracle_last_update_epoch=0,
        price_e8=0,
        price_pending_e8=0,
        collateral_e8=collateral_e8,
        debt_e8=debt_e8,
        free_debt_e8=free_debt_e8,
        sp_debt_e8=sp_debt_e8,
    )


def _scenarios() -> tuple[CoverageScenario, ...]:
    # Default MCR is 110%; at price 1.0 a vault is under MCR iff collateral < 1.1*debt.
    return (
        CoverageScenario(
            name="covered_liquidatable",
            description=(
                "Under MCR but the stability pool fully backs the vault "
                "(free_debt == 0): the kernel liquidates cleanly."
            ),
            state=_vault_state(
                collateral_e8=1_000 * E8,
                debt_e8=1_000 * E8,
                free_debt_e8=0,
                sp_debt_e8=1_000 * E8,
            ),
            expected_classification="covered",
        ),
        CoverageScenario(
            name="blocked_spiral_precursor",
            description=(
                "Under MCR with uninsured free debt (sp_debt < debt): the kernel "
                "refuses liquidation -- the section 6.2 acute disaster precursor."
            ),
            state=_vault_state(
                collateral_e8=1_000 * E8,
                debt_e8=1_000 * E8,
                free_debt_e8=400 * E8,
                sp_debt_e8=600 * E8,
            ),
            expected_classification="liquidation_blocked",
        ),
        CoverageScenario(
            name="uninsurable_region_healthy",
            description=(
                "Above MCR but only partially stability-pool backed: a price dip "
                "would strand the vault as unliquidatable."
            ),
            state=_vault_state(
                collateral_e8=2_000 * E8,
                debt_e8=1_000 * E8,
                free_debt_e8=400 * E8,
                sp_debt_e8=600 * E8,
            ),
            expected_classification="uninsurable_region",
        ),
        CoverageScenario(
            name="fully_covered_healthy",
            description="Above MCR and fully stability-pool backed.",
            state=_vault_state(
                collateral_e8=2_000 * E8,
                debt_e8=1_000 * E8,
                free_debt_e8=0,
                sp_debt_e8=1_000 * E8,
            ),
            expected_classification="covered",
        ),
        CoverageScenario(
            name="no_debt",
            description="No outstanding debt; nothing to absorb.",
            state=_vault_state(
                collateral_e8=0,
                debt_e8=0,
                free_debt_e8=0,
                sp_debt_e8=0,
            ),
            expected_classification="no_debt",
        ),
        CoverageScenario(
            name="indeterminate_oracle",
            description=(
                "Debt outstanding but oracle unseen: the MCR trigger is unpriced, "
                "so coverage is fail-closed to indeterminate."
            ),
            state=_vault_state(
                collateral_e8=1_000 * E8,
                debt_e8=1_000 * E8,
                free_debt_e8=1_000 * E8,
                sp_debt_e8=0,
                oracle_seen=False,
            ),
            expected_classification="indeterminate_oracle",
        ),
    )


def _evaluate_scenario(scenario: CoverageScenario) -> dict[str, Any]:
    state = scenario.state
    errors: list[str] = []

    invariant_failures = check_invariants(state)
    if invariant_failures:
        errors.append("scenario state violates invariants: " + ",".join(invariant_failures))

    cov = sp_absorption_coverage(state)
    if cov.classification != scenario.expected_classification:
        errors.append(
            f"classification {cov.classification!r} != expected "
            f"{scenario.expected_classification!r}"
        )

    # The shortfall is exactly the uninsured (free) debt by supply conservation.
    if cov.absorption_shortfall_e8 != state.free_debt_e8:
        errors.append(
            f"absorption_shortfall_e8 {cov.absorption_shortfall_e8} != "
            f"free_debt_e8 {state.free_debt_e8}"
        )

    # Faithfulness: the monitor must predict the real kernel liquidation decision.
    result = _step_python(state, ZUSDCommand(tag="liquidate", args={}))
    if cov.liquidation_blocked_by_sp:
        if result.ok:
            errors.append("monitor flagged liquidation_blocked_by_sp but kernel liquidated")
        elif result.error != SP_ABSORPTION_REFUSAL_ERROR:
            errors.append(
                "monitor flagged liquidation_blocked_by_sp but kernel refused for a "
                f"different reason: {result.error!r}"
            )
    elif cov.classification == "covered" and cov.vault_under_mcr:
        if not result.ok:
            errors.append(
                f"monitor predicted clean liquidation but kernel refused: {result.error!r}"
            )
    else:
        # The stability-pool gate is not the binding constraint here, so the
        # kernel must NOT refuse for the absorption reason.
        if result.ok:
            errors.append("kernel liquidated a scenario the monitor did not classify as covered")
        elif result.error == SP_ABSORPTION_REFUSAL_ERROR:
            errors.append(
                "kernel refused for stability-pool absorption but the monitor did not "
                "flag liquidation_blocked_by_sp"
            )

    return {
        "name": scenario.name,
        "description": scenario.description,
        "ok": not errors,
        "coverage": cov.to_dict(),
        "kernel_liquidate_ok": result.ok,
        "kernel_liquidate_error": result.error,
        "errors": errors,
    }


def validate_sp_absorption_coverage_corpus() -> dict[str, Any]:
    scenarios = [_evaluate_scenario(scenario) for scenario in _scenarios()]
    failed = [scenario["name"] for scenario in scenarios if not scenario["ok"]]
    return {
        "schema": REPORT_SCHEMA,
        "ok": not failed,
        "status": "accepted" if not failed else "rejected",
        "objective": (
            "zUSD stability-pool absorption-coverage monitor is faithful to the "
            "kernel liquidation-refusal decision (advisory, R7c)."
        ),
        "scenario_count": len(scenarios),
        "accepted_scenario_count": sum(1 for scenario in scenarios if scenario["ok"]),
        "failed_scenarios": failed,
        "scenarios": scenarios,
    }


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--json", action="store_true", help="Emit machine-readable JSON.")
    parser.add_argument("--pretty", action="store_true", help="Indent JSON output.")
    args = parser.parse_args(argv)

    report = validate_sp_absorption_coverage_corpus()
    if args.json or args.pretty:
        print(json.dumps(report, indent=2 if args.pretty else None, sort_keys=True))
    elif report["ok"]:
        print(
            "zusd sp-absorption-coverage monitor ok: "
            f"{report['accepted_scenario_count']}/{report['scenario_count']} scenarios faithful"
        )
    else:
        print("zusd sp-absorption-coverage monitor REJECTED", file=sys.stderr)
        for scenario in report["scenarios"]:
            for error in scenario["errors"]:
                print(f"{scenario['name']}: {error}", file=sys.stderr)
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
