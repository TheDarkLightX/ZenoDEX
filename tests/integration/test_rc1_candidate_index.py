from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path


def _write_candidate(root: Path, dirname: str, *, overall_ok: bool, unmet: list[str], dirty_count: int) -> None:
    bundle_dir = root / dirname
    bundle_dir.mkdir(parents=True, exist_ok=True)
    payload = {
        "schema": "zenodex/rc1-candidate-report/v1",
        "overall_ok": overall_ok,
        "blocked_before_run": not overall_ok,
        "unmet_criteria": unmet,
        "readiness": {
            "dirty_count": dirty_count,
            "assurance": {"branch": "test-branch"},
        },
    }
    (bundle_dir / "candidate_report.json").write_text(json.dumps(payload), encoding="utf-8")


def test_rc1_candidate_index_cli_filters_and_counts(tmp_path: Path) -> None:
    root = Path(__file__).resolve().parents[2]
    campaign_root = tmp_path / "rc1_candidates"
    _write_candidate(campaign_root, "20260327T120000Z_rc1-a", overall_ok=False, unmet=["clean_tree"], dirty_count=10)
    _write_candidate(campaign_root, "20260328T120000Z_rc1-b", overall_ok=True, unmet=[], dirty_count=0)

    proc = subprocess.run(
        [
            sys.executable,
            "tools/rc1_candidate_index.py",
            "--campaign-root",
            str(campaign_root),
            "--format",
            "json",
        ],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    payload = json.loads(proc.stdout)
    assert payload["schema"] == "zenodex/rc1-candidate-index/v1"
    assert payload["historical_release_label"] == "RC1"
    assert payload["active_candidate_label"] == "RC2"
    assert payload["candidate_count"] == 2
    assert payload["ready_count"] == 1
    assert payload["blocked_count"] == 1
    assert payload["unmet_criteria_counts"]["clean_tree"] == 1

    filtered = subprocess.run(
        [
            sys.executable,
            "tools/rc1_candidate_index.py",
            "--campaign-root",
            str(campaign_root),
            "--format",
            "json",
            "--ready-state",
            "blocked",
            "--run-id-prefix",
            "rc1-a",
        ],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    filtered_payload = json.loads(filtered.stdout)
    assert filtered_payload["candidate_count"] == 1
    assert filtered_payload["candidates"][0]["run_id"] == "rc1-a"


def test_rc1_candidate_index_markdown_and_csv_export(tmp_path: Path) -> None:
    root = Path(__file__).resolve().parents[2]
    campaign_root = tmp_path / "rc1_candidates"
    csv_out = tmp_path / "rc1_candidates.csv"
    _write_candidate(campaign_root, "20260327T120000Z_rc1-a", overall_ok=False, unmet=["clean_tree"], dirty_count=10)
    _write_candidate(campaign_root, "20260328T120000Z_rc1-b", overall_ok=True, unmet=[], dirty_count=0)

    proc = subprocess.run(
        [
            sys.executable,
            "tools/rc1_candidate_index.py",
            "--campaign-root",
            str(campaign_root),
            "--format",
            "markdown",
            "--csv-out",
            str(csv_out),
        ],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "# ZenoDex RC2 Candidate Index" in proc.stdout
    assert "| Timestamp | Run ID | Status | Dirty Count | Unmet Criteria |" in proc.stdout
    csv_text = csv_out.read_text(encoding="utf-8")
    assert "campaign_timestamp_utc,run_id,status,dirty_count,branch,unmet_criteria,bundle_dir,report_path" in csv_text
    assert "20260328T120000Z,rc1-b,READY,0" in csv_text
