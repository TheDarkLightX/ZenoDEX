from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "zenograph_autotrader_shadow_compare_baseline.py"


def test_zenograph_autotrader_shadow_compare_baseline_cli_roundtrip(tmp_path: Path) -> None:
    report_path = tmp_path / "baseline_report.json"
    log_path = tmp_path / "baseline_log.jsonl"

    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--report-out",
            str(report_path),
            "--log-out",
            str(log_path),
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    stdout_payload = json.loads(completed.stdout)
    report_payload = json.loads(report_path.read_text(encoding="utf-8"))
    log_rows = [json.loads(line) for line in log_path.read_text(encoding="utf-8").splitlines() if line.strip()]

    assert stdout_payload["schema"] == "zenodex/zenograph-autotrader-shadow-compare-baseline/v1"
    assert report_payload["case_count"] == 20
    assert len(log_rows) == 20
    assert report_payload["input_kind"] == "accepted_store_exports"
    assert report_payload["disagreement_rate"] == 12.0 / 20.0
    assert report_payload["controller_submit_vs_zenograph_block_rate"] == 4.0 / 20.0
    assert report_payload["controller_block_vs_zenograph_allow_rate"] == 8.0 / 20.0
    assert report_payload["selected_template_mismatch_rate"] == 0.0
    assert report_payload["family_summary"]["aligned_neutral"]["disagreement_rate"] == 0.0
    assert report_payload["family_summary"]["aligned_irrelevant"]["disagreement_rate"] == 0.0
    assert report_payload["family_summary"]["governance_block"]["disagreement_rate"] == 1.0
    assert report_payload["family_summary"]["oracle_stale_block"]["disagreement_rate"] == 1.0
    assert report_payload["family_summary"]["oracle_stale_block"]["controller_block_vs_zenograph_allow_rate"] == 1.0
    assert report_payload["family_summary"]["slippage_limit_block"]["disagreement_rate"] == 1.0
    assert (
        report_payload["family_summary"]["slippage_limit_block"][
            "controller_block_vs_zenograph_allow_rate"
        ]
        == 1.0
    )
    assert report_payload["first_disagreement"]["family"] == "governance_block"
