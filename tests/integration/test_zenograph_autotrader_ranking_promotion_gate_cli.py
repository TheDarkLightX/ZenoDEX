from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BASELINE_CLI = REPO_ROOT / "tools" / "zenograph_autotrader_shadow_compare_baseline.py"
GATE_CLI = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_promotion_gate.py"


def test_zenograph_ranking_promotion_gate_blocks_current_signed_baseline(
    tmp_path: Path,
) -> None:
    baseline_report = tmp_path / "baseline_report.json"
    subprocess.run(
        [
            sys.executable,
            str(BASELINE_CLI),
            "--report-out",
            str(baseline_report),
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(GATE_CLI),
            "--report-file",
            str(baseline_report),
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    payload = json.loads(completed.stdout)
    assert payload["source_metrics"]["signed_input_only"] is True
    assert payload["source_metrics"]["minimum_case_count_met"] is True
    assert payload["source_metrics"]["required_family_coverage_met"] is True
    assert payload["gate"]["ranking_influence_allowed"] is False
    assert payload["gate"]["block_reason"] == "submit_vs_block_disagreement"


def test_zenograph_ranking_promotion_gate_passes_clean_signed_report(
    tmp_path: Path,
) -> None:
    report_path = tmp_path / "clean_report.json"
    report_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/zenograph-autotrader-shadow-compare-baseline/v1",
                "input_kind": "accepted_store_exports",
                "case_count": 20,
                "family_summary": {
                    "aligned_neutral": {"case_count": 4, "disagreement_rate": 0.0},
                    "aligned_irrelevant": {"case_count": 4, "disagreement_rate": 0.0},
                    "governance_block": {"case_count": 4, "disagreement_rate": 0.0},
                    "oracle_stale_block": {"case_count": 4, "disagreement_rate": 0.0},
                    "slippage_limit_block": {"case_count": 4, "disagreement_rate": 0.0},
                },
                "disagreement_rate": 0.0,
                "controller_submit_vs_zenograph_block_rate": 0.0,
                "controller_block_vs_zenograph_allow_rate": 0.0,
                "selected_template_mismatch_rate": 0.25,
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(GATE_CLI),
            "--report-file",
            str(report_path),
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    payload = json.loads(completed.stdout)
    assert payload["risk_disclosure"]["advanced_feature"] is True
    assert payload["promotion_contract"]["required_case_count"] == 20
    assert payload["gate"]["ranking_influence_allowed"] is True
    assert payload["gate"]["block_reason"] is None


def test_zenograph_ranking_promotion_gate_blocks_missing_family_coverage(
    tmp_path: Path,
) -> None:
    report_path = tmp_path / "partial_report.json"
    report_path.write_text(
        json.dumps(
            {
                "schema": "zenodex/zenograph-autotrader-shadow-compare-baseline/v1",
                "input_kind": "accepted_store_exports",
                "case_count": 20,
                "family_summary": {
                    "aligned_neutral": {"case_count": 4, "disagreement_rate": 0.0},
                },
                "disagreement_rate": 0.0,
                "controller_submit_vs_zenograph_block_rate": 0.0,
                "controller_block_vs_zenograph_allow_rate": 0.0,
                "selected_template_mismatch_rate": 0.0,
            },
            indent=2,
            sort_keys=True,
        ),
        encoding="utf-8",
    )

    completed = subprocess.run(
        [
            sys.executable,
            str(GATE_CLI),
            "--report-file",
            str(report_path),
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    payload = json.loads(completed.stdout)
    assert payload["gate"]["ranking_influence_allowed"] is False
    assert payload["gate"]["block_reason"] == "required_family_coverage_missing"
