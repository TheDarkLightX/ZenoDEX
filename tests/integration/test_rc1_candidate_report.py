from __future__ import annotations

import subprocess
import sys
from pathlib import Path


from src.integration.rc1_candidate_index import build_candidate_index_payload
from src.integration.rc1_candidate_report import render_candidate_report_html
from tests.integration.test_rc1_candidate_index import _write_candidate


def test_render_candidate_report_html_contains_latest_and_table(tmp_path: Path) -> None:
    campaign_root = tmp_path / "rc1_candidates"
    _write_candidate(campaign_root, "20260327T120000Z_rc1-a", overall_ok=False, unmet=["clean_tree"], dirty_count=3)
    _write_candidate(campaign_root, "20260328T120000Z_rc1-b", overall_ok=True, unmet=[], dirty_count=0)
    payload = build_candidate_index_payload(campaign_root)

    html = render_candidate_report_html(payload)
    assert "ZenoDex RC2 Candidate Report" in html
    assert "Historical baseline: RC1 already shipped." in html
    assert "Latest Candidate" in html
    assert "rc1-b" in html
    assert "Candidate Table" in html
    assert "clean_tree" in html
    assert 'href="file://' in html
    assert "candidate_report.json" in html


def test_rc1_candidate_report_cli_writes_html(tmp_path: Path) -> None:
    root = Path(__file__).resolve().parents[2]
    campaign_root = tmp_path / "rc1_candidates"
    html_out = tmp_path / "rc1_candidate_report.html"
    _write_candidate(campaign_root, "20260327T120000Z_rc1-a", overall_ok=False, unmet=["clean_tree"], dirty_count=3)

    proc = subprocess.run(
        [
            sys.executable,
            "tools/rc1_candidate_report.py",
            "--campaign-root",
            str(campaign_root),
            "--html-out",
            str(html_out),
        ],
        cwd=root,
        check=True,
        capture_output=True,
        text=True,
    )
    assert "wrote" in proc.stdout
    html = html_out.read_text(encoding="utf-8")
    assert "<!DOCTYPE html>" in html
    assert "ZenoDex RC2 Candidate Report" in html
    assert "rc1-a" in html
