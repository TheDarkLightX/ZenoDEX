#!/usr/bin/env python3
from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
REPORT = ROOT / "generated" / "report.json"


def load_report() -> dict:
    subprocess.run([sys.executable, str(ROOT / "run_cycle.py")], check=True)
    return json.loads(REPORT.read_text(encoding="utf-8"))


def row_by_surface(report: dict) -> dict[str, dict]:
    return {row["surface"]: row for row in report["meet_rows"]}


def test_evidence_meet_counts_and_audit() -> None:
    report = load_report()

    assert report["surface_count"] == 16
    assert report["meet_cap_surface_count"] == 6
    assert report["execution_backed_meet_count"] == 2
    assert report["synthetic_meet_count"] == 4
    assert report["single_source_cap_count"] == 0
    assert report["no_user_value_cap_count"] == 10
    assert report["model_audit"]["total_meet_invariant_failures"] == 0


def test_meet_caps_are_minimum_of_sources() -> None:
    report = load_report()
    for row in report["meet_rows"]:
        caps = row["source_caps"]
        if not caps:
            assert row["meet_cap_bps"] is None
            continue
        assert row["meet_cap_bps"] == min(caps.values())
        assert all(row["meet_cap_bps"] <= cap for cap in caps.values())
        assert row["launch_parameter_claim"] is False


def test_execution_backed_meet_caps_are_conservative() -> None:
    rows = row_by_surface(load_report())

    assert rows["route_surplus_capture"]["classification"] == "execution_backed_meet_cap"
    assert rows["route_surplus_capture"]["meet_cap_bps"] == 1800
    assert rows["route_surplus_capture"]["source_caps"]["v192_execution"] == 2500
    assert rows["route_surplus_capture"]["execution_stress_tension_bps"] == 700

    assert rows["exact_out_savings_capture"]["classification"] == "execution_backed_meet_cap"
    assert rows["exact_out_savings_capture"]["meet_cap_bps"] == 2000
    assert rows["exact_out_savings_capture"]["source_caps"]["v192_execution"] == 2497
    assert rows["exact_out_savings_capture"]["execution_stress_tension_bps"] == 497


def test_bad_and_non_user_surfaces_do_not_get_meet_caps() -> None:
    rows = row_by_surface(load_report())
    for surface in (
        "execution_route_overcharge_bad",
        "execution_exact_out_wash_bad",
        "extractive_notional_bad",
        "wash_rebate_bad",
        "staking_early_exit_penalty",
        "treasury_market_maker_bot",
    ):
        assert rows[surface]["classification"] == "no_user_value_cap"
        assert rows[surface]["meet_cap_bps"] is None
        assert rows[surface]["source_caps"] == {}
