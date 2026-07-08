from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin
from tools.zenodex_tau_semantic_coverage_selector_20260628 import (
    REPORT_JSON,
    SURFACES,
    build_focus_candidates,
    build_inventory,
    build_report,
    proposed_specifications,
    selector_facts,
)

ROOT = Path(__file__).resolve().parents[2]


def test_tau_semantic_coverage_selector_report() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()

    assert report["ok"] is True
    assert report["schema"] == "zenodex.tau_semantic_coverage_selector_report.v1"
    assert report["tau_replay"]["surface_count"] == 3
    assert report["tau_replay"]["required_fact_mutations"] == 38
    assert report["tau_replay"]["case_count"] == 44
    assert report["tau_replay"]["invalid_accepts"] == 0
    assert report["tau_replay"]["false_rejects"] == 0
    assert all(surface["ok"] for surface in report["tau_replay"]["surfaces"])
    assert {row["work_item"] for row in report["proposed_specifications"]} >= {"1_ab_ordering", "2_cow_matching"}


def test_tau_semantic_coverage_selector_cli_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_semantic_coverage_selector_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=90,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    assert report["ok"] is True
    assert report["tau_replay"]["invalid_accepts"] == 0


def test_selector_facts_require_ab_and_cow_work_items() -> None:
    inventory = build_inventory()
    focus = build_focus_candidates(inventory)
    facts = selector_facts(inventory, focus)

    assert facts["work_item_1_ab_selected"] is True
    assert facts["work_item_2_cow_selected"] is True
    assert facts["critical_bucket_coverage_ok"] is True
    assert facts["no_runtime_authority_effect"] is True

    specs = proposed_specifications()
    assert any(row["spec_id"] == "ab_ordering_held_karp_dp_certificate_v1" for row in specs)
    assert any(row["spec_id"] == "cow_hungarian_matching_certificate_v1" for row in specs)


def test_all_surface_mutations_are_exercised() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    report = build_report()
    surface_by_id = {surface.surface_id: surface for surface in SURFACES}

    for surface in report["tau_replay"]["surfaces"]:
        expected_count = surface_by_id[surface["surface_id"]].input_count + 2
        assert surface["case_count"] == expected_count
        positive = [row for row in surface["cases"] if row["expected_primary"] == 1]
        rejecting = [row for row in surface["cases"] if row["expected_primary"] == 0]
        assert len(positive) == 1
        assert len(rejecting) == expected_count - 1
        assert all(row["ok"] for row in surface["cases"])
