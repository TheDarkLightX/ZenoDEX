from __future__ import annotations

import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[2]
BUNDLE_CLI = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_review_bundle.py"
REPORT_CLI = REPO_ROOT / "tools" / "zenograph_autotrader_ranking_review_campaign_report.py"


def test_zenograph_autotrader_ranking_review_campaign_report_cli_renders_html(
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
            "20260327T010203Z",
            "--run-id",
            "report",
            "--operator-release-enable",
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    html_out = tmp_path / "campaign_report.html"
    subprocess.run(
        [
            sys.executable,
            str(REPORT_CLI),
            "--campaign-root",
            str(campaign_root),
            "--html-out",
            str(html_out),
        ],
        check=True,
        capture_output=True,
        text=True,
        cwd=str(REPO_ROOT),
    )

    html = html_out.read_text(encoding="utf-8")
    assert "<!doctype html>" in html
    assert "ZenoGraph Campaign Governance Report" in html
    assert "Use at your own risk." in html
    assert "Latest Bundle" in html
    assert "Campaign Day Trends" in html
    assert "Bundle Index" in html
    assert "20260327T010203Z_report" in html
    assert ">manifest<" in html
    assert ">review<" in html
    assert ">gate<" in html
    assert ">baseline<" in html
    assert ">readme<" in html
    assert "Latest bundle remains blocked. Lead blocker:" in html
