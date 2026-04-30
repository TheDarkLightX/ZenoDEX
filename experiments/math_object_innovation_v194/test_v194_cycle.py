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


def row_by_id(report: dict) -> dict[str, dict]:
    return {row["config_id"]: row for row in report["config_rows"]}


def test_launch_config_guard_counts_and_audit() -> None:
    report = load_report()

    assert report["config_count"] == 10
    assert report["surface_check_count"] == 18
    assert report["accepted_without_override_count"] == 2
    assert report["accepted_with_override_count"] == 3
    assert report["rejected_count"] == 5
    assert report["evidence_compliant_config_count"] == 2
    assert report["governance_assumption_change_count"] == 3
    assert report["model_audit"]["total_config_invariant_failures"] == 0


def test_without_override_acceptance_implies_all_fees_under_meet_caps() -> None:
    report = load_report()

    for row in report["config_rows"]:
        if row["acceptance_class"] != "accepted_without_override":
            continue
        assert row["evidence_compliant"] is True
        assert row["has_assumption_override"] is False
        for check in row["checks"]:
            assert check["status"] == "ok_under_meet_cap"
            assert check["meet_cap_bps"] is not None
            assert check["fee_bps"] <= check["meet_cap_bps"]


def test_overcap_or_unknown_acceptance_requires_recorded_override() -> None:
    report = load_report()

    for row in report["config_rows"]:
        if not row["accepted"]:
            continue
        for check in row["checks"]:
            cap = check["meet_cap_bps"]
            if cap is None or check["fee_bps"] > cap:
                assert check["status"] == "ok_assumption_change_override"
                assert check["override_present"] is True
                assert check["override_valid"] is True


def test_bad_configs_reject_for_expected_reasons() -> None:
    rows = row_by_id(load_report())

    assert rows["overcap_no_override_bad"]["accepted"] is False
    assert "missing_override" in rows["overcap_no_override_bad"]["config_failures"]

    assert rows["overcap_claim_bad"]["accepted"] is False
    assert "missing_override" in rows["overcap_claim_bad"]["config_failures"]
    assert "unsafe_evidence_compliance_claim" in rows["overcap_claim_bad"]["config_failures"]

    assert rows["invalid_override_missing_ack_bad"]["accepted"] is False
    assert "missing_no_user_net_ack" in rows["invalid_override_missing_ack_bad"]["config_failures"]

    assert rows["unknown_surface_no_override_bad"]["accepted"] is False
    assert "missing_override" in rows["unknown_surface_no_override_bad"]["config_failures"]

    assert rows["redundant_override_bad"]["accepted"] is False
    assert "redundant_override" in rows["redundant_override_bad"]["config_failures"]


def test_valid_overrides_do_not_claim_evidence_compliance() -> None:
    rows = row_by_id(load_report())

    for config_id in (
        "valid_route_override_review",
        "unknown_surface_valid_override",
        "mixed_safe_and_override_review",
    ):
        row = rows[config_id]
        assert row["accepted"] is True
        assert row["acceptance_class"] == "accepted_with_override"
        assert row["claimed_evidence_compliant"] is False
        assert row["evidence_compliant"] is False
