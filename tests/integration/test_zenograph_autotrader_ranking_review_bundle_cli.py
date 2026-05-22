from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
CLI_PATH = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_review_bundle.py"


def test_zenograph_autotrader_ranking_review_bundle_cli_builds_outputs(
    tmp_path: Path,
) -> None:
    baseline_report = tmp_path / "baseline_report.json"
    baseline_log = tmp_path / "baseline_log.jsonl"
    gate_report = tmp_path / "gate_report.json"
    summary = tmp_path / "ranking_review.md"
    instructions = tmp_path / "README.md"

    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--baseline-report-out",
            str(baseline_report),
            "--baseline-log-out",
            str(baseline_log),
            "--gate-report-out",
            str(gate_report),
            "--summary-out",
            str(summary),
            "--instructions-out",
            str(instructions),
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    payload = json.loads(completed.stdout)
    assert payload["schema"] == "zenodex/zenograph-autotrader-ranking-review-bundle/v1"
    assert payload["ranking_influence_allowed"] is False
    assert payload["block_reason"] == "submit_vs_block_disagreement"
    assert payload["run_id"] == baseline_report.parent.name
    assert payload["metadata"]["python_version"]
    assert payload["metadata"]["tool_versions"]["bundle_cli"] == "zenograph_autotrader_ranking_review_bundle/v1"
    assert payload["artifacts"]["baseline_report"]["path"] == str(baseline_report)
    assert payload["artifacts"]["gate_report"]["path"] == str(gate_report)
    assert payload["artifacts"]["summary"]["path"] == str(summary)
    assert payload["artifacts"]["instructions"]["path"] == str(instructions)
    assert baseline_report.exists()
    assert baseline_log.exists()
    assert gate_report.exists()
    assert summary.exists()
    assert instructions.exists()

    summary_text = summary.read_text(encoding="utf-8")
    assert "# ZenoGraph Ranking Review Bundle" in summary_text
    assert "submit_vs_block_disagreement" in summary_text
    assert "slippage_limit_block" in summary_text
    instructions_text = instructions.read_text(encoding="utf-8")
    assert "Build Command" in instructions_text
    assert "Verify Command" in instructions_text


def test_zenograph_autotrader_ranking_review_bundle_cli_supports_out_dir(
    tmp_path: Path,
) -> None:
    out_dir = tmp_path / "bundle"

    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--out-dir",
            str(out_dir),
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    payload = json.loads(completed.stdout)
    manifest_path = Path(payload["manifest_path"])
    assert manifest_path.exists()
    assert (out_dir / "baseline_report.json").exists()
    assert (out_dir / "baseline_log.jsonl").exists()
    assert (out_dir / "gate_report.json").exists()
    assert (out_dir / "ranking_review.md").exists()
    manifest_payload = json.loads(manifest_path.read_text(encoding="utf-8"))
    assert manifest_payload["schema"] == "zenodex/zenograph-autotrader-ranking-review-bundle/v1"
    assert manifest_payload["block_reason"] == "submit_vs_block_disagreement"
    assert manifest_payload["metadata"]["tool_versions"]["gate_cli"] == "zenograph_autotrader_ranking_promotion_gate/v1"
    assert manifest_payload["artifacts"]["baseline_log"]["path"] == str(
        out_dir / "baseline_log.jsonl"
    )
    assert manifest_payload["artifacts"]["baseline_report"]["sha256"] == hashlib.sha256(
        (out_dir / "baseline_report.json").read_bytes()
    ).hexdigest()
    assert manifest_payload["artifacts"]["gate_report"]["sha256"] == hashlib.sha256(
        (out_dir / "gate_report.json").read_bytes()
    ).hexdigest()
    assert manifest_payload["artifacts"]["summary"]["sha256"] == hashlib.sha256(
        (out_dir / "ranking_review.md").read_bytes()
    ).hexdigest()
    assert manifest_payload["artifacts"]["instructions"]["sha256"] == hashlib.sha256(
        (out_dir / "README.md").read_bytes()
    ).hexdigest()


def test_zenograph_autotrader_ranking_review_bundle_cli_auto_campaign_dir(
    tmp_path: Path,
) -> None:
    campaign_root = tmp_path / "campaigns"

    completed = subprocess.run(
        [
            sys.executable,
            str(CLI_PATH),
            "--campaign-root",
            str(campaign_root),
            "--timestamp-utc",
            "20260326T204500Z",
            "--run-id",
            "signed_replay_v1",
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    payload = json.loads(completed.stdout)
    bundle_dir = Path(payload["bundle_dir"])
    assert bundle_dir == campaign_root / "20260326T204500Z_signed_replay_v1"
    assert payload["run_id"] == "20260326T204500Z_signed_replay_v1"
    assert payload["metadata"]["generated_at_utc"]
    assert payload["artifacts"]["baseline_report"]["bytes"] > 0
    assert (bundle_dir / "baseline_report.json").exists()
    assert (bundle_dir / "baseline_log.jsonl").exists()
    assert (bundle_dir / "gate_report.json").exists()
    assert (bundle_dir / "ranking_review.md").exists()
    assert (bundle_dir / "README.md").exists()
    assert (bundle_dir / "manifest.json").exists()
