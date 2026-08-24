#!/usr/bin/env python3
"""Replay the bounded Tau perps risk-envelope equations with exact inputs.

This checker is research evidence. It has no settlement, liquidation, Oracle,
or publication authority. Inputs mirror the ``bv[32]`` and ``sbf`` streams in
``perp_risk_envelope_proof_gate_v1.tau`` and reject values that Tau would
otherwise truncate or reinterpret.
"""

from __future__ import annotations

import argparse
from collections.abc import Mapping
from typing import Any

BV32_MAX = (1 << 32) - 1

_NUMERIC_FIELDS = (
    "mark_price_e8",
    "oracle_price_e8",
    "prev_mark_price_e8",
    "prev_oracle_price_e8",
    "open_interest",
    "max_open_interest",
    "funding_abs_bps",
    "funding_cap_bps",
    "liq_penalty_bps",
    "liq_penalty_cap_bps",
    "insurance_balance",
    "insurance_floor",
    "margin_ratio_bps",
    "maint_margin_bps",
    "max_mark_oracle_gap_abs",
    "max_mark_drift_abs",
    "max_oracle_drift_abs",
)

_BOOLEAN_FIELDS = (
    "stale_oracle_flag",
    "breaker_active_flag",
    "proof_ok",
    "binding_ok",
    "has_open_positions",
)


def _validate_tau_inputs(values: Mapping[str, object]) -> None:
    for field in _NUMERIC_FIELDS:
        value = values[field]
        if type(value) is not int or not 0 <= value <= BV32_MAX:
            raise ValueError(f"{field} must be an exact unsigned 32-bit integer")
    for field in _BOOLEAN_FIELDS:
        if type(values[field]) is not bool:
            raise ValueError(f"{field} must be an exact bool")


def _evaluate_risk_envelope(
    *,
    mark_price_e8: int,
    oracle_price_e8: int,
    prev_mark_price_e8: int,
    prev_oracle_price_e8: int,
    open_interest: int,
    max_open_interest: int,
    funding_abs_bps: int,
    funding_cap_bps: int,
    liq_penalty_bps: int,
    liq_penalty_cap_bps: int,
    insurance_balance: int,
    insurance_floor: int,
    stale_oracle_flag: bool,
    breaker_active_flag: bool,
    proof_ok: bool,
    binding_ok: bool,
    has_open_positions: bool,
    margin_ratio_bps: int,
    maint_margin_bps: int,
    max_mark_oracle_gap_abs: int,
    max_mark_drift_abs: int,
    max_oracle_drift_abs: int,
) -> dict[str, bool]:
    """Evaluate the exact host-side image of the bounded Tau equations."""
    inputs = locals()
    _validate_tau_inputs(inputs)

    mark_oracle_gap_ok = abs(mark_price_e8 - oracle_price_e8) <= max_mark_oracle_gap_abs
    mark_drift_ok = abs(mark_price_e8 - prev_mark_price_e8) <= max_mark_drift_abs
    oracle_drift_ok = abs(oracle_price_e8 - prev_oracle_price_e8) <= max_oracle_drift_abs
    oi_cap_ok = open_interest <= max_open_interest
    funding_cap_ok = funding_abs_bps <= funding_cap_bps
    liq_penalty_cap_ok = liq_penalty_bps <= liq_penalty_cap_bps
    insurance_floor_ok = insurance_balance >= insurance_floor
    stale_guard_ok = not stale_oracle_flag
    breaker_guard_ok = not breaker_active_flag
    margin_guard_ok = not has_open_positions or margin_ratio_bps >= maint_margin_bps
    risk_envelope_ok = bool(
        mark_oracle_gap_ok
        and mark_drift_ok
        and oracle_drift_ok
        and oi_cap_ok
        and funding_cap_ok
        and liq_penalty_cap_ok
        and insurance_floor_ok
        and stale_guard_ok
        and breaker_guard_ok
        and margin_guard_ok
        and proof_ok
        and binding_ok
    )
    return {
        "mark_oracle_gap_ok": mark_oracle_gap_ok,
        "mark_drift_ok": mark_drift_ok,
        "oracle_drift_ok": oracle_drift_ok,
        "oi_cap_ok": oi_cap_ok,
        "funding_cap_ok": funding_cap_ok,
        "liq_penalty_cap_ok": liq_penalty_cap_ok,
        "insurance_floor_ok": insurance_floor_ok,
        "stale_guard_ok": stale_guard_ok,
        "breaker_guard_ok": breaker_guard_ok,
        "margin_guard_ok": margin_guard_ok,
        "risk_envelope_ok": risk_envelope_ok,
    }


def _boundary_witness() -> dict[str, Any]:
    return {
        "mark_price_e8": 1_000_000,
        "oracle_price_e8": 1_000_000,
        "prev_mark_price_e8": 1_000_000,
        "prev_oracle_price_e8": 1_000_000,
        "open_interest": 100,
        "max_open_interest": 100,
        "funding_abs_bps": 10,
        "funding_cap_bps": 10,
        "liq_penalty_bps": 50,
        "liq_penalty_cap_bps": 50,
        "insurance_balance": 1_000,
        "insurance_floor": 1_000,
        "stale_oracle_flag": False,
        "breaker_active_flag": False,
        "proof_ok": True,
        "binding_ok": True,
        "has_open_positions": True,
        "margin_ratio_bps": 500,
        "maint_margin_bps": 500,
        "max_mark_oracle_gap_abs": 100,
        "max_mark_drift_abs": 100,
        "max_oracle_drift_abs": 100,
    }


def check_perp_risk_envelope_containment_v1() -> dict[str, Any]:
    """Run positive-boundary and one-atom rejection witnesses."""
    baseline = _boundary_witness()
    scenarios: list[dict[str, Any]] = []

    accepted = _evaluate_risk_envelope(**baseline)
    scenarios.append(
        {
            "scenario_id": "all_exact_boundaries_accept",
            "expected": True,
            "observed": accepted["risk_envelope_ok"],
        }
    )

    mutations = {
        "mark_oracle_gap_plus_one_rejects": {
            "mark_price_e8": 1_000_101,
            "prev_mark_price_e8": 1_000_101,
        },
        "mark_drift_plus_one_rejects": {"prev_mark_price_e8": 999_899},
        "oracle_drift_plus_one_rejects": {"prev_oracle_price_e8": 999_899},
        "open_interest_plus_one_rejects": {"open_interest": 101},
        "funding_plus_one_rejects": {"funding_abs_bps": 11},
        "liquidation_penalty_plus_one_rejects": {"liq_penalty_bps": 51},
        "insurance_one_below_floor_rejects": {"insurance_balance": 999},
        "margin_one_below_maintenance_rejects": {"margin_ratio_bps": 499},
        "missing_proof_rejects": {"proof_ok": False},
        "missing_binding_rejects": {"binding_ok": False},
        "stale_oracle_with_proof_rejects": {"stale_oracle_flag": True},
        "active_breaker_with_proof_rejects": {"breaker_active_flag": True},
    }
    for scenario_id, replacement in mutations.items():
        witness = {**baseline, **replacement}
        observed = _evaluate_risk_envelope(**witness)["risk_envelope_ok"]
        scenarios.append({"scenario_id": scenario_id, "expected": False, "observed": observed})

    ok = all(row["observed"] is row["expected"] for row in scenarios)
    return {
        "schema": "zenodex.perp_risk_envelope_containment.v1",
        "ok": ok,
        "scenario_count": len(scenarios),
        "scenarios": scenarios,
        "production_authority": "NONE",
        "nonclaims": [
            "This bounded checker does not establish runtime or whole-market containment.",
            "Tau proof and binding flags remain externally supplied inputs.",
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(description="Replay the bounded perps risk-envelope equations.")
    parser.parse_args()
    report = check_perp_risk_envelope_containment_v1()
    print(
        "OK PERP_RISK_ENVELOPE_CONTAINMENT_V1 "
        f"scenarios={report['scenario_count']}/{report['scenario_count']}"
    )
    return 0 if report["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
