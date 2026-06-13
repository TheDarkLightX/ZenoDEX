from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BUNDLE_CLI = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_review_bundle.py"
INDEX_CLI = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_review_campaign_index.py"


def test_zenograph_autotrader_ranking_review_campaign_index_cli_lists_bundles(
    tmp_path: Path,
) -> None:
    campaign_root = tmp_path / "campaigns"
    subprocess.run(
        [
            sys.executable,
            str(BUNDLE_CLI),
            "--campaign-root",
            str(campaign_root),
            "--timestamp-utc",
            "20260326T204500Z",
            "--run-id",
            "older",
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    subprocess.run(
        [
            sys.executable,
            str(BUNDLE_CLI),
            "--campaign-root",
            str(campaign_root),
            "--timestamp-utc",
            "20260326T214500Z",
            "--run-id",
            "newer",
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    subprocess.run(
        [
            sys.executable,
            str(BUNDLE_CLI),
            "--campaign-root",
            str(campaign_root),
            "--timestamp-utc",
            "20260327T000100Z",
            "--run-id",
            "latest",
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    older_manifest = campaign_root / "20260326T204500Z_older" / "manifest.json"
    older_payload = json.loads(older_manifest.read_text(encoding="utf-8"))
    older_payload["metadata"]["git_dirty"] = True
    older_manifest.write_text(
        json.dumps(older_payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    newer_manifest = campaign_root / "20260326T214500Z_newer" / "manifest.json"
    newer_payload = json.loads(newer_manifest.read_text(encoding="utf-8"))
    newer_payload["metadata"]["git_commit_short"] = "abc1234"
    newer_payload["metadata"]["git_dirty"] = False
    newer_manifest.write_text(
        json.dumps(newer_payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )
    latest_manifest = campaign_root / "20260327T000100Z_latest" / "manifest.json"
    latest_payload = json.loads(latest_manifest.read_text(encoding="utf-8"))
    latest_payload["metadata"]["git_commit_short"] = "def5678"
    latest_payload["metadata"]["git_dirty"] = True
    latest_payload["ranking_influence_allowed"] = True
    latest_payload["block_reason"] = None
    latest_manifest.write_text(
        json.dumps(latest_payload, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    markdown_out = tmp_path / "index.md"
    csv_out = tmp_path / "index.csv"
    csv_daily_out = tmp_path / "index_daily.csv"
    csv_daily_block_reasons_out = tmp_path / "index_daily_block_reasons.csv"
    completed = subprocess.run(
        [
            sys.executable,
            str(INDEX_CLI),
            "--campaign-root",
            str(campaign_root),
            "--markdown-out",
            str(markdown_out),
            "--csv-out",
            str(csv_out),
            "--csv-daily-out",
            str(csv_daily_out),
            "--csv-daily-block-reasons-out",
            str(csv_daily_block_reasons_out),
            "--pretty",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    payload = json.loads(completed.stdout)
    assert payload["schema"] == "zenodex/zenograph-autotrader-ranking-review-campaign-index/v1"
    assert payload["bundle_count"] == 3
    assert payload["filters"] == {
        "gate_status": None,
        "run_id_prefix": None,
        "git_prefix": None,
        "dirty_state": None,
        "generated_since_utc": None,
        "generated_until_utc": None,
    }
    assert payload["gate_status_counts"] == {"allowed": 1, "blocked": 2}
    assert payload["block_reason_counts"] == {"none": 1, "submit_vs_block_disagreement": 2}
    assert payload["campaign_day_counts"] == {"20260326": 2, "20260327": 1}
    assert payload["campaign_day_gate_status_counts"] == {
        "20260326": {"blocked": 2},
        "20260327": {"allowed": 1},
    }
    assert payload["block_reason_spans"] == {
        "none": {
            "count": 1,
            "first_campaign_day": "20260327",
            "last_campaign_day": "20260327",
        },
        "submit_vs_block_disagreement": {
            "count": 2,
            "first_campaign_day": "20260326",
            "last_campaign_day": "20260326",
        },
    }
    assert payload["latest_gate_status"] == "allowed"
    assert payload["latest_gate_status_streak_length"] == 1
    assert payload["latest_block_reason"] == "none"
    assert payload["latest_block_reason_streak_length"] == 1
    assert payload["entries"][0]["run_id"] == "20260327T000100Z_latest"
    assert payload["entries"][1]["run_id"] == "20260326T214500Z_newer"
    assert payload["entries"][2]["run_id"] == "20260326T204500Z_older"
    markdown = markdown_out.read_text(encoding="utf-8")
    assert "# ZenoGraph Ranking Review Campaign Index" in markdown
    assert "Block reason counts" in markdown
    assert "Campaign Day Trends" in markdown
    assert "Block Reason Spans" in markdown
    assert "Latest gate status streak" in markdown
    assert "20260326" in markdown
    assert "20260327" in markdown
    assert "20260326T214500Z_newer" in markdown
    csv_text = csv_out.read_text(encoding="utf-8")
    assert "run_id,campaign_timestamp_utc,generated_at_utc,ranking_influence_allowed" in csv_text
    assert "20260327T000100Z_latest,20260327T000100Z," in csv_text
    assert ",true,allowed,," in csv_text
    assert "20260326T214500Z_newer,20260326T214500Z," in csv_text
    assert ",false,blocked,submit_vs_block_disagreement,abc1234,clean," in csv_text
    csv_daily_text = csv_daily_out.read_text(encoding="utf-8")
    assert "campaign_day,bundle_count,allowed_count,blocked_count,unknown_count,gate_status_counts" in csv_daily_text
    assert "20260326,2,0,2,0,blocked=2" in csv_daily_text
    assert "20260327,1,1,0,0,allowed=1" in csv_daily_text
    csv_daily_block_reasons_text = csv_daily_block_reasons_out.read_text(encoding="utf-8")
    assert "campaign_day,block_reason,count" in csv_daily_block_reasons_text
    assert "20260326,submit_vs_block_disagreement,2" in csv_daily_block_reasons_text
    assert "20260327,none,1" in csv_daily_block_reasons_text

    blocked = subprocess.run(
        [
            sys.executable,
            str(INDEX_CLI),
            "--campaign-root",
            str(campaign_root),
            "--gate-status",
            "blocked",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    blocked_payload = json.loads(blocked.stdout)
    assert blocked_payload["bundle_count"] == 2
    assert blocked_payload["gate_status_counts"] == {"blocked": 2}
    assert blocked_payload["campaign_day_counts"] == {"20260326": 2}

    allowed = subprocess.run(
        [
            sys.executable,
            str(INDEX_CLI),
            "--campaign-root",
            str(campaign_root),
            "--gate-status",
            "allowed",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    allowed_payload = json.loads(allowed.stdout)
    assert allowed_payload["bundle_count"] == 1
    assert allowed_payload["entries"][0]["run_id"] == "20260327T000100Z_latest"
    assert allowed_payload["gate_status_counts"] == {"allowed": 1}

    filtered = subprocess.run(
        [
            sys.executable,
            str(INDEX_CLI),
            "--campaign-root",
            str(campaign_root),
            "--run-id-prefix",
            "20260326T214500Z",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    filtered_payload = json.loads(filtered.stdout)
    assert filtered_payload["bundle_count"] == 1
    assert filtered_payload["entries"][0]["run_id"] == "20260326T214500Z_newer"
    assert filtered_payload["block_reason_counts"] == {"submit_vs_block_disagreement": 1}
    assert filtered_payload["campaign_day_counts"] == {"20260326": 1}

    git_filtered = subprocess.run(
        [
            sys.executable,
            str(INDEX_CLI),
            "--campaign-root",
            str(campaign_root),
            "--git-prefix",
            "abc",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    git_filtered_payload = json.loads(git_filtered.stdout)
    assert git_filtered_payload["bundle_count"] == 1
    assert git_filtered_payload["entries"][0]["run_id"] == "20260326T214500Z_newer"

    clean_filtered = subprocess.run(
        [
            sys.executable,
            str(INDEX_CLI),
            "--campaign-root",
            str(campaign_root),
            "--dirty-state",
            "clean",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    clean_filtered_payload = json.loads(clean_filtered.stdout)
    assert clean_filtered_payload["bundle_count"] == 1
    assert clean_filtered_payload["entries"][0]["run_id"] == "20260326T214500Z_newer"

    since_filtered = subprocess.run(
        [
            sys.executable,
            str(INDEX_CLI),
            "--campaign-root",
            str(campaign_root),
            "--generated-since-utc",
            "20260326T210000Z",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    since_filtered_payload = json.loads(since_filtered.stdout)
    assert since_filtered_payload["bundle_count"] == 2
    assert since_filtered_payload["entries"][0]["run_id"] == "20260327T000100Z_latest"
    assert since_filtered_payload["entries"][1]["run_id"] == "20260326T214500Z_newer"

    until_filtered = subprocess.run(
        [
            sys.executable,
            str(INDEX_CLI),
            "--campaign-root",
            str(campaign_root),
            "--generated-until-utc",
            "20260326T210000Z",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )
    until_filtered_payload = json.loads(until_filtered.stdout)
    assert until_filtered_payload["bundle_count"] == 1
    assert until_filtered_payload["entries"][0]["run_id"] == "20260326T204500Z_older"
