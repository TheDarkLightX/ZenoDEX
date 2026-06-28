from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

import pytest

from src.integration.tau_runner import find_tau_bin


ROOT = Path(__file__).resolve().parents[2]
REPORT_JSON = ROOT / "generated" / "zenodex_tau_semantic_coverage_selector_20260628" / "report.json"
REPORT_MD = ROOT / "docs" / "research" / "ZENODEX_TAU_SEMANTIC_COVERAGE_SELECTOR_20260628.md"


def _surface(report: dict, surface_id: str) -> dict:
    for surface in report["tau_replay"]["surfaces"]:
        if surface["surface_id"] == surface_id:
            return surface
    raise AssertionError(f"missing surface {surface_id}")


def _case(surface: dict, case_id: str) -> dict:
    for row in surface["cases"]:
        if row["case_id"] == case_id:
            return row
    raise AssertionError(f"missing case {surface['surface_id']}.{case_id}")


def test_tau_semantic_coverage_selector_replay() -> None:
    if not find_tau_bin(ROOT, profile="latest"):
        pytest.skip("latest Tau binary not found")

    proc = subprocess.run(
        [sys.executable, "tools/zenodex_tau_semantic_coverage_selector_20260628.py"],
        cwd=ROOT,
        capture_output=True,
        text=True,
        timeout=180,
    )

    assert proc.returncode == 0, proc.stdout + proc.stderr
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))

    assert report["ok"] is True
    assert report["breakthrough"]["name"] == "Tau semantic coverage selector"
    assert report["tau_replay"]["ok"] is True
    assert report["tau_replay"]["totals"]["surface_count"] == 3
    assert report["tau_replay"]["totals"]["mutation_count"] >= 38
    assert report["tau_replay"]["totals"]["invalid_accepts"] == 0
    assert report["tau_replay"]["totals"]["false_rejects"] == 0
    assert REPORT_MD.exists()


def test_tau_semantic_coverage_selector_selects_work_items_1_and_2() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    proposed_ids = {spec["spec_id"] for spec in report["proposed_specifications"]}
    facts = report["selector_facts"]

    assert "ab_ordering_held_karp_dp_certificate_v1" in proposed_ids
    assert "cow_hungarian_matching_certificate_v1" in proposed_ids
    assert "tau_semantic_coverage_selector_certificate_v1" in proposed_ids
    assert facts["work_item_1_ab_selected"] is True
    assert facts["work_item_2_cow_selected"] is True
    assert report["work_items"]["1_ab_ordering"]["status"] == "specified_for_certificate_replay"
    assert report["work_items"]["2_cow_matching"]["status"] == "specified_for_certificate_replay"


def test_tau_semantic_coverage_selector_bucket_coverage_and_ordering() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    candidates = report["focus_candidates"]
    buckets = {candidate["risk_bucket"] for candidate in candidates}
    scores = [(int(candidate["priority_score"]), candidate["spec_id"]) for candidate in candidates]

    assert {"consensus_core", "spot_math_core"} <= buckets
    assert report["selector_facts"]["deterministic_priority_order_ok"] is True
    assert scores == sorted(scores, key=lambda item: (-item[0], item[1]))
    assert all(candidate["next_actions"] for candidate in candidates)


def test_tau_semantic_coverage_selector_mutations_reject_and_scope_non_claims() -> None:
    report = json.loads(REPORT_JSON.read_text(encoding="utf-8"))
    selector = _surface(report, "tau_semantic_coverage_selector_certificate")
    ab = _surface(report, "ab_ordering_held_karp_dp_certificate")
    cow = _surface(report, "cow_hungarian_matching_certificate")
    non_claims = "\n".join(report["non_claims"])

    assert _case(selector, "positive_accept")["got_primary"] == 1
    assert _case(selector, "flip_i12_reject")["got_primary"] == 0
    assert _case(selector, "inactive_safe")["got_inactive"] == 1
    assert _case(ab, "flip_i10_reject")["got_primary"] == 0
    assert _case(cow, "flip_i11_reject")["got_primary"] == 0
    assert "does not authorize settlement" in non_claims
    assert "does not prove the proposed host algorithms correct" in non_claims
